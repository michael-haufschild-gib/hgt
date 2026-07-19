#!/usr/bin/env python3
"""Local automation for the hgt Lean formal project.

This script is intentionally CI-agnostic.  It gives agents local tools for:

* generating a declaration API index;
* generating a gap/status report;
* linting proof debt and project wiring;
* searching reusable formal infrastructure before reproving it.
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
SRC = FORMAL / "GaloisForLFunctions"
API_MD = FORMAL / "LEAN_API.md"
GAPS_MD = FORMAL / "LEAN_GAPS.md"
OVERVIEW_MD = FORMAL / "LEAN_OVERVIEW.md"

DECL_RE = re.compile(r"^\s*(theorem|lemma|def|structure|class|abbrev|inductive)\s+([\w'.]+)")
DEBT_RE = re.compile(r"^\s*(sorry|admit)\b|^\s*(axiom|opaque)\s+[A-Za-z_]|^\s*unsafe\s+(def|theorem|axiom)\b")
MARKER_RE = re.compile(r"\b(TODO|FIXME|OPEN|NEXT|Remaining|remaining|blocked|missing)\b")
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
MODULE_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")

THEOREM_AREAS = {
    "rh_tower": {
        "module": "GaloisForLFunctions.RHTower",
        "path": SRC / "RHTower",
        "capstones": ["RHTower.rh_iff_tower", "RHTower.rh_iff_forall_ladder"],
    },
    "ht_geometry": {
        "module": "GaloisForLFunctions.HTGeometry",
        "path": SRC / "HTGeometry",
        "capstones": [
            "hypertranscendental_gamma",
            "HTGeometry.exists_wedgeFacetSewnUpperEndSystem",
        ],
    },
    "hurwitz": {
        "module": "GaloisForLFunctions.Hurwitz",
        "path": SRC / "Hurwitz",
        "capstones": ["hurwitz_n2_unconditional"],
    },
    "u0_pui": {
        "module": "GaloisForLFunctions.U0",
        "path": SRC / "U0",
        "capstones": [
            "U0PhiIndep.u0_phi_independence",
            "U0CardTheorems.u0_phi_independence_all_parameters",
        ],
    },
    "q62_boettcher": {
        "module": "GaloisForLFunctions.Bottcher",
        "path": SRC / "Bottcher",
        "capstones": ["Bottcher.q62_independence", "Bottcher.q62_mixed"],
    },
    "hilbert_metric": {
        "module": "GaloisForLFunctions.HilbertMetric",
        "path": SRC / "HilbertMetric",
        "capstones": [
            "gaussianCorrectedDeterminant_mul_sq_le",
            "gaussianDistanceMatrix_det_mul_sq_le",
        ],
    },
}

ALLOWED_ROOT_LEAN = {
    "Bottcher.lean",
    "Core.lean",
    "FullyProvenNewTargets.lean",
    "HTGeometry.lean",
    "HilbertMetric.lean",
    "Hurwitz.lean",
    "KummerRootApplications.lean",
    "MainTheorems.lean",
    "RHTower.lean",
    "U0.lean",
}


@dataclasses.dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    module: str
    relpath: str
    line: int
    doc: str


@dataclasses.dataclass(frozen=True)
class Finding:
    kind: str
    relpath: str
    line: int
    text: str
    context: str


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def lean_files() -> list[Path]:
    return sorted(SRC.rglob("*.lean"))


def module_name(path: Path, *, formal: Path = FORMAL) -> str:
    return ".".join(path.relative_to(formal).with_suffix("").parts)


def read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Strip Lean line and block comments while preserving line numbers."""
    out: list[str] = []
    depth = 0
    for line in lines:
        i = 0
        kept: list[str] = []
        while i < len(line):
            if depth == 0 and line.startswith("--", i):
                break
            if line.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if depth > 0:
                if line.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            kept.append(line[i])
            i += 1
        out.append("".join(kept))
    return out


def imported_modules(path: Path) -> set[str]:
    imports: set[str] = set()
    for line in strip_lean_comments(read_lines(path)):
        match = IMPORT_RE.match(line)
        if not match:
            continue
        imports.update(
            token for token in match.group(1).split() if MODULE_NAME_RE.fullmatch(token)
        )
    return imports


def unreachable_owned_modules(
    theorem_areas: dict[str, dict[str, object]] = THEOREM_AREAS,
    *,
    formal: Path = FORMAL,
    src: Path = SRC,
) -> dict[str, list[str]]:
    paths = sorted(src.rglob("*.lean"))
    root_module = formal / f"{src.name}.lean"
    if root_module.exists():
        paths.append(root_module)

    module_paths = {module_name(path, formal=formal): path for path in paths}
    import_graph = {name: imported_modules(path) for name, path in module_paths.items()}
    unreachable: dict[str, list[str]] = {}

    for area_name, info in theorem_areas.items():
        umbrella = str(info["module"])
        if umbrella not in module_paths:
            continue

        reachable: set[str] = set()
        pending = [umbrella]
        while pending:
            current = pending.pop()
            if current in reachable:
                continue
            reachable.add(current)
            pending.extend(
                imported
                for imported in import_graph.get(current, set())
                if imported in module_paths and imported not in reachable
            )

        area_path = Path(info["path"])
        owned = {
            module_name(path, formal=formal) for path in area_path.rglob("*.lean")
        }
        missing = sorted(owned - reachable)
        if missing:
            unreachable[area_name] = missing

    return unreachable


def doc_before(lines: list[str], index: int) -> str:
    """Return the first useful line of the docstring immediately above index."""
    j = index - 1
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    if j < 0 or "-/" not in lines[j]:
        return ""
    block: list[str] = []
    while j >= 0:
        block.append(lines[j])
        if "/--" in lines[j]:
            break
        j -= 1
    block.reverse()
    text = " ".join(
        line.strip()
        .removeprefix("/--")
        .removesuffix("-/")
        .strip()
        .lstrip("*")
        .strip()
        for line in block
    )
    text = re.sub(r"\s+", " ", text).strip()
    return text[:180]


def declarations() -> list[Declaration]:
    out: list[Declaration] = []
    for path in lean_files():
        lines = read_lines(path)
        code_lines = strip_lean_comments(lines)
        mod = module_name(path)
        for i, line in enumerate(code_lines):
            match = DECL_RE.match(line)
            if not match:
                continue
            out.append(
                Declaration(
                    kind=match.group(1),
                    name=match.group(2),
                    module=mod,
                    relpath=rel(path),
                    line=i + 1,
                    doc=doc_before(lines, i),
                )
            )
    return out


def declaration_context(lines: list[str], index: int) -> str:
    code_lines = strip_lean_comments(lines[: index + 1])
    for j in range(index, -1, -1):
        match = DECL_RE.match(code_lines[j])
        if match:
            return f"{match.group(1)} {match.group(2)}"
    return ""


def proof_debt() -> list[Finding]:
    out: list[Finding] = []
    for path in lean_files():
        lines = read_lines(path)
        code_lines = strip_lean_comments(lines)
        for i, line in enumerate(code_lines):
            if DEBT_RE.search(line):
                out.append(Finding("proof-debt", rel(path), i + 1, lines[i].strip(), declaration_context(lines, i)))
    return out


def marker_findings(limit: int = 250, *, include_status_logs: bool = False) -> list[Finding]:
    paths = sorted(list(SRC.rglob("*.lean")) + list(SRC.rglob("*.md")) + [FORMAL / "README.md"])
    out: list[Finding] = []
    for path in paths:
        if not path.exists():
            continue
        if path.name == "STATUS.md" and not include_status_logs:
            continue
        for i, line in enumerate(read_lines(path)):
            if MARKER_RE.search(line):
                out.append(Finding("marker", rel(path), i + 1, line.strip(), ""))
                if len(out) >= limit:
                    return out
    return out


def file_sizes(*, include_status_logs: bool = False) -> list[tuple[int, str]]:
    sizes: list[tuple[int, str]] = []
    for path in sorted(list(SRC.rglob("*.lean")) + list(SRC.rglob("*.md"))):
        if path.name == "STATUS.md" and not include_status_logs:
            continue
        sizes.append((len(read_lines(path)), rel(path)))
    return sorted(sizes, reverse=True)


def area_lean_files(path: Path) -> list[Path]:
    if path.is_dir():
        return sorted(path.rglob("*.lean"))
    if path.with_suffix(".lean").exists():
        return [path.with_suffix(".lean")]
    return []


def split_declarations_by_area(
    decls: list[Declaration] | None = None,
) -> tuple[dict[str, list[Declaration]], list[Declaration]]:
    by_area: dict[str, list[Declaration]] = {key: [] for key in THEOREM_AREAS}
    other: list[Declaration] = []
    for d in decls or declarations():
        placed = False
        for key, info in THEOREM_AREAS.items():
            area_path = rel(info["path"])
            if d.relpath.startswith(area_path + "/") or d.relpath == area_path + ".lean":
                by_area[key].append(d)
                placed = True
                break
        if not placed:
            other.append(d)
    return by_area, other


def api_markdown() -> str:
    decls = declarations()
    by_area, other = split_declarations_by_area(decls)

    lines = [
        "# Lean API Index",
        "",
        "Generated by `scripts/formal_tools.py index` from the current Lean tree.",
        "Use this before proving a lemma; search by declaration name, module, or docstring.",
        "",
        "## Theorem Areas",
        "",
        "| Area | Umbrella | Declarations | Capstones |",
        "|---|---|---:|---|",
    ]
    for key, info in THEOREM_AREAS.items():
        lines.append(
            f"| `{key}` | `{info['module']}` | {len(by_area[key])} | "
            f"{', '.join(f'`{x}`' for x in info['capstones'])} |"
        )
    lines.extend(["", "## Declarations", ""])

    def emit_group(title: str, group: list[Declaration]) -> None:
        lines.extend([f"### {title}", "", "| Kind | Name | Module | Location | Doc |", "|---|---|---|---|---|"])
        for d in sorted(group, key=lambda item: (item.module, item.line, item.name)):
            lines.append(f"| {d.kind} | `{d.name}` | `{d.module}` | `{d.relpath}:{d.line}` | {d.doc} |")
        lines.append("")

    for key in THEOREM_AREAS:
        emit_group(key, by_area[key])
    emit_group("shared and bridge infrastructure", other)
    return "\n".join(lines).rstrip() + "\n"


def overview_markdown() -> str:
    decls = declarations()
    by_area, other = split_declarations_by_area(decls)
    debt = proof_debt()
    root_imports = (FORMAL / "GaloisForLFunctions.lean").read_text(encoding="utf-8")
    root_wired = "yes" if "import GaloisForLFunctions.MainTheorems" in root_imports else "no"
    lines = [
        "# Lean Formal Overview",
        "",
        "Generated by `scripts/formal_tools.py index` from the current Lean tree.",
        "Use this as the quick map before opening large proof files.",
        "",
        "## Theorem Areas",
        "",
        "| Area | Umbrella | Lean modules | Declarations | Capstones |",
        "|---|---|---:|---:|---|",
    ]
    for key, info in THEOREM_AREAS.items():
        module_count = len(area_lean_files(info["path"]))
        lines.append(
            f"| `{key}` | `{info['module']}` | {module_count} | {len(by_area[key])} | "
            f"{', '.join(f'`{x}`' for x in info['capstones'])} |"
        )
    lines.extend(
        [
            "",
            "## Wiring",
            "",
            f"- Root imports `GaloisForLFunctions.MainTheorems`: **{root_wired}**.",
            f"- Package-level declarations outside the five theorem areas: **{len(other)}**.",
            f"- Active proof-debt findings: **{len(debt)}**.",
            "",
            "## Local Commands",
            "",
            "| Command | Purpose |",
            "|---|---|",
            "| `../scripts/formal_tools.py status` | Print theorem-area counts, proof debt, and largest files. |",
            "| `../scripts/formal_tools.py research \"<query>\"` | Search generated declarations and gap markers before proving a lemma. |",
            "| `../scripts/formal_tools.py index` | Regenerate this overview plus API and gap reports. |",
            "| `../scripts/formal_tools.py lint --check-generated` | Check proof debt, project wiring, file sizes, and generated-file freshness. |",
            "| `../scripts/formal_tools.py lint --check-generated --build --build-target GaloisForLFunctions.MainTheorems` | Run the local full formal gate. |",
            "",
            "## Largest Lean Files",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    emitted = 0
    for count, path in file_sizes():
        if path.endswith(".lean") and count >= 500:
            lines.append(f"| {count} | `{path}` |")
            emitted += 1
        if emitted >= 12:
            break
    return "\n".join(lines).rstrip() + "\n"


def gaps_markdown() -> str:
    debt = proof_debt()
    sizes = file_sizes()
    markers = marker_findings()
    lines = [
        "# Lean Gap and Order Report",
        "",
        "Generated by `scripts/formal_tools.py index` from local files.",
        "This is an agent worklist aid, not a mathematical ledger.",
        "",
        "## Proof Debt",
        "",
    ]
    if debt:
        lines.extend(["| Kind | Location | Context | Text |", "|---|---|---|---|"])
        for f in debt:
            lines.append(f"| {f.kind} | `{f.relpath}:{f.line}` | `{f.context}` | `{f.text}` |")
    else:
        lines.append("No active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations found.")

    lines.extend(
        [
            "",
            "## Large Files",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    for count, path in sizes[:25]:
        if count >= 500:
            lines.append(f"| {count} | `{path}` |")

    lines.extend(
        [
            "",
            "## Gap Markers",
            "",
            "| Location | Text |",
            "|---|---|",
        ]
    )
    for f in markers:
        lines.append(f"| `{f.relpath}:{f.line}` | {f.text} |")
    lines.extend(
        [
            "",
            "## Historical Status Logs",
            "",
            "`STATUS.md` progress logs are intentionally excluded from the default gap-marker table.",
            "Use `scripts/formal_tools.py research \"<query>\"` when you need to search those logs.",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    for path in sorted(SRC.rglob("STATUS.md")):
        lines.append(f"| {len(read_lines(path))} | `{rel(path)}` |")
    return "\n".join(lines).rstrip() + "\n"


def write_indexes(_: argparse.Namespace | None = None) -> int:
    API_MD.write_text(api_markdown(), encoding="utf-8")
    GAPS_MD.write_text(gaps_markdown(), encoding="utf-8")
    OVERVIEW_MD.write_text(overview_markdown(), encoding="utf-8")
    print(f"wrote {rel(API_MD)}")
    print(f"wrote {rel(GAPS_MD)}")
    print(f"wrote {rel(OVERVIEW_MD)}")
    return 0


def check_generated() -> list[str]:
    errors: list[str] = []
    expected = {API_MD: api_markdown(), GAPS_MD: gaps_markdown(), OVERVIEW_MD: overview_markdown()}
    for path, content in expected.items():
        if not path.exists():
            errors.append(f"missing generated file: {rel(path)}")
        elif path.read_text(encoding="utf-8") != content:
            errors.append(f"stale generated file: {rel(path)}")
    return errors


def run_lake_build(target: str | None) -> tuple[int, str]:
    cmd = ["lake", "build"]
    if target:
        cmd.append(target if target.startswith("+") else f"+{target}")
    result = subprocess.run(cmd, cwd=FORMAL, text=True, capture_output=True)
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    return result.returncode, result.stdout + result.stderr


def lint(args: argparse.Namespace) -> int:
    errors: list[str] = []
    warnings: list[str] = []

    for name, info in THEOREM_AREAS.items():
        module_path = FORMAL / Path(*info["module"].split(".")).with_suffix(".lean")
        if not module_path.exists():
            errors.append(f"missing theorem-area umbrella for {name}: {rel(module_path)}")

    for name, modules in unreachable_owned_modules().items():
        umbrella = THEOREM_AREAS[name]["module"]
        for module in modules:
            errors.append(
                f"owned module unreachable from theorem-area umbrella {umbrella}: {module}"
            )

    root_imports = (FORMAL / "GaloisForLFunctions.lean").read_text(encoding="utf-8")
    if "import GaloisForLFunctions.MainTheorems" not in root_imports:
        errors.append("root module does not import GaloisForLFunctions.MainTheorems")

    unexpected_root_modules = sorted(
        path.name for path in SRC.glob("*.lean") if path.name not in ALLOWED_ROOT_LEAN
    )
    for name in unexpected_root_modules:
        errors.append(
            f"research leaf module at package root: {name}; move it into an owned theorem area"
        )

    formal_claude = FORMAL / "CLAUDE.md"
    formal_agents = FORMAL / "AGENTS.md"
    if not formal_claude.exists():
        errors.append(f"missing formal agent instructions: {rel(formal_claude)}")
    if not formal_agents.exists():
        errors.append(f"missing formal agent instructions: {rel(formal_agents)}")
    if formal_claude.exists() and formal_agents.exists():
        if formal_claude.read_text(encoding="utf-8") != formal_agents.read_text(encoding="utf-8"):
            errors.append("formal/CLAUDE.md and formal/AGENTS.md have drifted")

    for f in proof_debt():
        errors.append(f"proof debt: {f.relpath}:{f.line}: {f.text} ({f.context})")

    for count, path in file_sizes():
        if path.endswith(".lean") and count > args.max_lines:
            warnings.append(f"large Lean file: {path} has {count} lines")

    if args.check_generated:
        errors.extend(check_generated())

    if args.build:
        build_code, build_output = run_lake_build(args.build_target)
        if build_code != 0:
            errors.append(f"lake build failed with exit code {build_code}")
        build_warnings = [line for line in build_output.splitlines() if line.startswith("warning:")]
        if build_warnings and not args.allow_build_warnings:
            errors.append(
                f"lake build emitted {len(build_warnings)} warnings "
                "(fix them or pass --allow-build-warnings)"
            )

    for msg in warnings:
        print(f"warning: {msg}", file=sys.stderr)
    for msg in errors:
        print(f"error: {msg}", file=sys.stderr)

    if errors:
        return 1
    print("formal lint passed")
    return 0


def status(_: argparse.Namespace) -> int:
    print("Theorem areas:")
    for key, info in THEOREM_AREAS.items():
        module_count = len(area_lean_files(info["path"]))
        print(f"- {key}: {info['module']} ({module_count} Lean modules)")
        print(f"  capstones: {', '.join(info['capstones'])}")
    print()
    debt = proof_debt()
    print(f"Proof debt findings: {len(debt)}")
    for f in debt:
        print(f"- {f.relpath}:{f.line}: {f.text}")
    print()
    print("Largest files:")
    for count, path in file_sizes()[:10]:
        print(f"- {count:5d} {path}")
    status_logs = sorted(SRC.rglob("STATUS.md"))
    if status_logs:
        print()
        print("Historical status logs:")
        for path in status_logs:
            print(f"- {len(read_lines(path)):5d} {rel(path)}")
    return 0


def research(args: argparse.Namespace) -> int:
    query = " ".join(args.query).strip().lower()
    if not query:
        print("provide a search query", file=sys.stderr)
        return 2

    scored: list[tuple[int, Declaration]] = []
    for d in declarations():
        hay = f"{d.name} {d.kind} {d.module} {d.relpath} {d.doc}".lower()
        score = sum(3 if token in d.name.lower() else 1 for token in query.split() if token in hay)
        if score:
            scored.append((score, d))
    scored.sort(key=lambda item: (-item[0], item[1].module, item[1].line))

    print("Declarations:")
    for _, d in scored[: args.limit]:
        print(f"- {d.name} ({d.kind}) {d.module} {d.relpath}:{d.line}")
        if d.doc:
            print(f"  {d.doc}")

    gap_hits = [
        f
        for f in marker_findings(limit=500, include_status_logs=True)
        if query in f.text.lower() or any(t in f.text.lower() for t in query.split())
    ]
    if gap_hits:
        print("\nGap markers:")
        for f in gap_hits[: args.limit]:
            print(f"- {f.relpath}:{f.line}: {f.text}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser(
        "index",
        help="generate formal/LEAN_OVERVIEW.md, formal/LEAN_API.md, and formal/LEAN_GAPS.md",
    ).set_defaults(func=write_indexes)

    lint_parser = sub.add_parser("lint", help="run local formal-project lint checks")
    lint_parser.add_argument("--max-lines", type=int, default=1500)
    lint_parser.add_argument("--check-generated", action="store_true")
    lint_parser.add_argument("--build", action="store_true", help="also run lake build")
    lint_parser.add_argument("--build-target", default="GaloisForLFunctions.MainTheorems")
    lint_parser.add_argument("--allow-build-warnings", action="store_true")
    lint_parser.set_defaults(func=lint)

    sub.add_parser("status", help="print theorem-area and proof-debt summary").set_defaults(func=status)

    research_parser = sub.add_parser("research", help="search declarations and gap markers")
    research_parser.add_argument("query", nargs="+")
    research_parser.add_argument("--limit", type=int, default=20)
    research_parser.set_defaults(func=research)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
