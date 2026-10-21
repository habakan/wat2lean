use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::Path;
use std::process;

use wast::Wat;
use wast::core::{BlockType, FuncKind, Instruction, ModuleField, ModuleKind, ValType};
use wast::parser::{self, ParseBuffer};
use wast::token::{Index, Span};

const USAGE: &str =
    "usage: wat2lean <module.wat> <body-index> <lean-name> [block-line:lean-name ...]";

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    if args.len() == 1 && (args[0] == "-h" || args[0] == "--help") {
        println!("{USAGE}");
        return Ok(());
    }
    if args.len() < 3 {
        return Err(USAGE.to_owned());
    }

    let path = Path::new(&args[0]);
    let body_index = args[1]
        .parse::<usize>()
        .map_err(|_| format!("invalid body index: {}", args[1]))?;
    let top_name = &args[2];
    validate_name(top_name)?;
    let names = parse_names(&args[3..])?;
    if names.values().any(|name| name == top_name) {
        return Err(format!("duplicate Lean name: {top_name}"));
    }

    let source =
        fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let mut buffer =
        ParseBuffer::new(&source).map_err(|error| format_wast_error(error, path, &source))?;
    buffer.track_instr_spans(true);
    let mut wat =
        parser::parse::<Wat>(&buffer).map_err(|error| format_wast_error(error, path, &source))?;

    let module = match &mut wat {
        Wat::Module(module) => module,
        Wat::Component(_) => return Err("component text is not supported".to_owned()),
    };
    module
        .resolve()
        .map_err(|error| format_wast_error(error, path, &source))?;
    let fields = match &module.kind {
        ModuleKind::Text(fields) => fields,
        ModuleKind::Binary(_) => return Err("binary module text is not supported".to_owned()),
    };

    let mut current_body = 0;
    let mut selected = None;
    for field in fields {
        let ModuleField::Func(function) = field else {
            continue;
        };
        if let FuncKind::Inline { locals, expression } = &function.kind {
            if current_body == body_index {
                selected = Some((function, locals.as_ref(), expression));
                break;
            }
            current_body += 1;
        }
    }
    let (function, locals, expression) =
        selected.ok_or_else(|| format!("no function body at index {body_index}"))?;
    if locals
        .iter()
        .any(|local| !matches!(local.ty, ValType::I32 | ValType::I64))
    {
        return Err("only i32 and i64 locals are supported".to_owned());
    }

    let function_line = function.span.linecol_in(&source).0;
    let mut cursor = 0;
    let mut definitions = Vec::new();
    let mut used_names = BTreeSet::new();
    let (body, terminator) = sequence(
        &expression.instrs,
        expression.instr_spans.as_deref(),
        &mut cursor,
        function_line,
        &source,
        path,
        &names,
        &mut used_names,
        &mut definitions,
        false,
    )?;
    if terminator.is_some() || cursor != expression.instrs.len() {
        return Err("unexpected end or else in the function body".to_owned());
    }
    if used_names.len() != names.len() {
        let unused = names
            .keys()
            .filter(|line| !used_names.contains(line))
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "no named block starts on function-relative line(s): {unused}"
        ));
    }

    for definition in definitions {
        println!("{definition}");
    }
    println!(
        "def {top_name} : Func :=\n  ⟨{}, {}⟩",
        locals.len(),
        format_list(&body)
    );
    Ok(())
}

fn format_wast_error(mut error: wast::Error, path: &Path, source: &str) -> String {
    error.set_text(source);
    error.set_path(path);
    error.to_string()
}

fn validate_name(name: &str) -> Result<(), String> {
    let mut chars = name.chars();
    let valid_start = chars
        .next()
        .is_some_and(|ch| ch == '_' || ch.is_ascii_alphabetic());
    if !valid_start || !chars.all(|ch| ch == '_' || ch == '\'' || ch.is_ascii_alphanumeric()) {
        return Err(format!("invalid Lean identifier: {name}"));
    }
    const KEYWORDS: &[&str] = &[
        "abbrev",
        "axiom",
        "by",
        "class",
        "def",
        "do",
        "else",
        "end",
        "example",
        "export",
        "if",
        "import",
        "inductive",
        "instance",
        "let",
        "match",
        "mutual",
        "namespace",
        "open",
        "opaque",
        "partial",
        "private",
        "protected",
        "section",
        "structure",
        "then",
        "theorem",
        "unsafe",
        "where",
        "with",
    ];
    if KEYWORDS.contains(&name) {
        return Err(format!(
            "Lean keyword cannot be used as an identifier: {name}"
        ));
    }
    Ok(())
}

fn parse_names(args: &[String]) -> Result<BTreeMap<usize, String>, String> {
    let mut names = BTreeMap::new();
    let mut unique = BTreeSet::new();
    for arg in args {
        let (line, name) = arg
            .split_once(':')
            .ok_or_else(|| format!("invalid block name mapping: {arg}"))?;
        let line = line
            .parse::<usize>()
            .map_err(|_| format!("invalid block line: {line}"))?;
        if line == 0 {
            return Err("block lines start at 1 on the first line after the function header".to_owned());
        }
        validate_name(name)?;
        if names.insert(line, name.to_owned()).is_some() {
            return Err(format!("duplicate block line: {line}"));
        }
        if !unique.insert(name.to_owned()) {
            return Err(format!("duplicate Lean name: {name}"));
        }
    }
    Ok(names)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Terminator {
    Else,
    End,
}

#[allow(clippy::too_many_arguments)]
fn sequence(
    instructions: &[Instruction<'_>],
    spans: Option<&[Span]>,
    cursor: &mut usize,
    function_line: usize,
    source: &str,
    path: &Path,
    names: &BTreeMap<usize, String>,
    used_names: &mut BTreeSet<usize>,
    definitions: &mut Vec<String>,
    allow_else: bool,
) -> Result<(Vec<String>, Option<Terminator>), String> {
    let mut output = Vec::new();
    while *cursor < instructions.len() {
        let position = *cursor;
        let instruction = &instructions[position];
        let span = spans.and_then(|spans| spans.get(position)).copied();
        *cursor += 1;

        match instruction {
            Instruction::else_(_) if allow_else => {
                return Ok((output, Some(Terminator::Else)));
            }
            Instruction::else_(_) => {
                return Err(located(path, source, span, "else without a matching if"));
            }
            Instruction::end(_) => return Ok((output, Some(Terminator::End))),
            Instruction::block(block) => {
                let (body, stop) = sequence(
                    instructions,
                    spans,
                    cursor,
                    function_line,
                    source,
                    path,
                    names,
                    used_names,
                    definitions,
                    false,
                )?;
                if stop != Some(Terminator::End) {
                    return Err(located(path, source, span, "block has no matching end"));
                }
                let results =
                    result_count(block).map_err(|error| located(path, source, span, &error))?;
                let body = named_body(
                    body,
                    span,
                    function_line,
                    source,
                    names,
                    used_names,
                    definitions,
                );
                output.push(format!(".block {results} {body}"));
            }
            Instruction::loop_(block) => {
                let (body, stop) = sequence(
                    instructions,
                    spans,
                    cursor,
                    function_line,
                    source,
                    path,
                    names,
                    used_names,
                    definitions,
                    false,
                )?;
                if stop != Some(Terminator::End) {
                    return Err(located(path, source, span, "loop has no matching end"));
                }
                let results =
                    result_count(block).map_err(|error| located(path, source, span, &error))?;
                let body = named_body(
                    body,
                    span,
                    function_line,
                    source,
                    names,
                    used_names,
                    definitions,
                );
                output.push(format!(".loop {results} {body}"));
            }
            Instruction::if_(block) => {
                let (then_body, stop) = sequence(
                    instructions,
                    spans,
                    cursor,
                    function_line,
                    source,
                    path,
                    names,
                    used_names,
                    definitions,
                    true,
                )?;
                let else_body = match stop {
                    Some(Terminator::End) => Vec::new(),
                    Some(Terminator::Else) => {
                        let (body, stop) = sequence(
                            instructions,
                            spans,
                            cursor,
                            function_line,
                            source,
                            path,
                            names,
                            used_names,
                            definitions,
                            false,
                        )?;
                        if stop != Some(Terminator::End) {
                            return Err(located(path, source, span, "if has no matching end"));
                        }
                        body
                    }
                    None => return Err(located(path, source, span, "if has no matching end")),
                };
                let results =
                    result_count(block).map_err(|error| located(path, source, span, &error))?;
                let then_body = named_body(
                    then_body,
                    span,
                    function_line,
                    source,
                    names,
                    used_names,
                    definitions,
                );
                output.push(format!(
                    ".if_ {results} {then_body} {}",
                    format_list(&else_body)
                ));
            }
            _ => {
                let term = instruction_term(instruction)
                    .map_err(|error| located(path, source, span, &error))?;
                output.push(term);
            }
        }
    }
    Ok((output, None))
}

fn named_body(
    body: Vec<String>,
    span: Option<Span>,
    function_line: usize,
    source: &str,
    names: &BTreeMap<usize, String>,
    used_names: &mut BTreeSet<usize>,
    definitions: &mut Vec<String>,
) -> String {
    let line = span.map(|span| span.linecol_in(source).0.saturating_sub(function_line));
    if let Some((line, name)) = line.and_then(|line| names.get(&line).map(|name| (line, name))) {
        used_names.insert(line);
        definitions.push(format!(
            "def {name} : List Instr :=\n  {}\n",
            format_list(&body)
        ));
        name.clone()
    } else {
        format_list(&body)
    }
}

fn format_list(items: &[String]) -> String {
    if items.is_empty() {
        "[]".to_owned()
    } else {
        format!("[{}]", items.join(",\n    "))
    }
}

fn result_count(block: &BlockType<'_>) -> Result<usize, String> {
    if block.ty.index.is_some() {
        return Err("type-indexed block signatures are not supported".to_owned());
    }
    let Some(signature) = &block.ty.inline else {
        return Ok(0);
    };
    if !signature.params.is_empty() {
        return Err("block parameters are not supported".to_owned());
    }
    match signature.results.as_ref() {
        [] => Ok(0),
        [ValType::I32] => Ok(1),
        _ => Err("only blocks with no result or one i32 result are supported".to_owned()),
    }
}

fn index_value(index: &Index<'_>) -> Result<u32, String> {
    match index {
        Index::Num(value, _) => Ok(*value),
        Index::Id(id) => Err(format!("unresolved WAT identifier: {}", id.name())),
    }
}

fn require_zero_index(index: &Index<'_>, kind: &str) -> Result<(), String> {
    if index_value(index)? == 0 {
        Ok(())
    } else {
        Err(format!("only {kind} index 0 is supported"))
    }
}

fn memory_offset(memory: &wast::core::MemArg<'_>) -> Result<u64, String> {
    require_zero_index(&memory.memory, "memory")?;
    Ok(memory.offset)
}

fn instruction_term(instruction: &Instruction<'_>) -> Result<String, String> {
    use Instruction as I;
    let term = match instruction {
        I::unreachable => ".unreachable".to_owned(),
        I::br(index) => format!(".br {}", index_value(index)?),
        I::br_if(index) => format!(".brIf {}", index_value(index)?),
        I::br_table(table) => {
            let labels = table
                .labels
                .iter()
                .map(index_value)
                .collect::<Result<Vec<_>, _>>()?;
            format!(
                ".brTable [{}] {}",
                labels
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                index_value(&table.default)?
            )
        }
        I::return_ => ".ret".to_owned(),
        I::call(index) => format!(".call {}", index_value(index)?),
        I::call_indirect(call) => {
            require_zero_index(&call.table, "table")?;
            let index =
                call.ty.index.as_ref().ok_or_else(|| {
                    "inline call_indirect signatures are not supported".to_owned()
                })?;
            format!(".callIndirect {}", index_value(index)?)
        }
        I::drop => ".drop".to_owned(),
        I::select(types) => {
            if types.tys.is_some() {
                return Err("typed select is not supported".to_owned());
            }
            ".select".to_owned()
        }
        I::local_get(index) => format!(".localGet {}", index_value(index)?),
        I::local_set(index) => format!(".localSet {}", index_value(index)?),
        I::local_tee(index) => format!(".localTee {}", index_value(index)?),
        I::global_get(index) => format!(".globalGet {}", index_value(index)?),
        I::global_set(index) => format!(".globalSet {}", index_value(index)?),
        I::i32_load(memory) => format!(".load32 {}", memory_offset(memory)?),
        I::i32_load8_u(memory) => format!(".load8u {}", memory_offset(memory)?),
        I::i32_load8_s(memory) => format!(".load8s {}", memory_offset(memory)?),
        I::i32_load16_u(memory) => format!(".load16u {}", memory_offset(memory)?),
        I::i64_load(memory) => format!(".load64 {}", memory_offset(memory)?),
        I::i32_store(memory) => format!(".store32 {}", memory_offset(memory)?),
        I::i64_store32(memory) => format!(".store32 {}", memory_offset(memory)?),
        I::i64_store(memory) => format!(".store64 {}", memory_offset(memory)?),
        I::i32_store8(memory) => format!(".store8 {}", memory_offset(memory)?),
        I::i32_store16(memory) => format!(".store16 {}", memory_offset(memory)?),
        I::memory_fill(memory) => {
            require_zero_index(&memory.mem, "memory")?;
            ".fill".to_owned()
        }
        I::memory_copy(memory) => {
            require_zero_index(&memory.src, "source memory")?;
            require_zero_index(&memory.dst, "destination memory")?;
            ".copy".to_owned()
        }
        I::i32_const(value) => format!(".const {}", *value as u32),
        I::i64_const(value) => format!(".const64 {}", *value as u64),
        I::i32_eqz | I::i64_eqz => ".eqz".to_owned(),
        I::i32_add => ".bin .add".to_owned(),
        I::i32_sub => ".bin .sub".to_owned(),
        I::i32_shl => ".bin .shl".to_owned(),
        I::i32_eq => ".bin .eq".to_owned(),
        I::i32_ne => ".bin .ne".to_owned(),
        I::i32_lt_u => ".bin .ltU".to_owned(),
        I::i32_gt_u => ".bin .gtU".to_owned(),
        I::i32_le_u => ".bin .leU".to_owned(),
        I::i32_ge_u => ".bin .geU".to_owned(),
        I::i32_and => ".bin .and".to_owned(),
        I::i32_or => ".bin .or".to_owned(),
        I::i32_mul => ".bin .mul".to_owned(),
        I::i32_lt_s => ".bin .ltS".to_owned(),
        I::i32_ge_s => ".bin .geS".to_owned(),
        I::i64_add => ".bin .add64".to_owned(),
        I::i64_sub => ".bin .sub64".to_owned(),
        I::i64_lt_u => ".bin .ltU".to_owned(),
        I::i64_gt_u => ".bin .gtU".to_owned(),
        I::i32_shr_u => ".bin .shrU".to_owned(),
        I::i32_xor => ".bin .xor".to_owned(),
        I::i32_div_u => ".divU".to_owned(),
        I::i32_wrap_i64 => ".wrap".to_owned(),
        other => return Err(format!("unsupported instruction: {other:?}")),
    };
    Ok(term)
}

fn located(path: &Path, source: &str, span: Option<Span>, message: &str) -> String {
    match span {
        Some(span) => {
            let (line, column) = span.linecol_in(source);
            format!("{}:{}:{}: {message}", path.display(), line + 1, column + 1)
        }
        None => format!("{}: {message}", path.display()),
    }
}
