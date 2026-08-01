#!/usr/bin/env python3
"""Generate a zero-omission RHTower/HTGeometry paper census.

The generated TSV contains one row for every Lean module in the two research
areas.  It is a coverage ledger, not a novelty verdict: scientific disposition
is deliberately left to the accompanying hostile audit.
"""

from __future__ import annotations

import argparse
import csv
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from formal_tools import Declaration, declarations


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal" / "GaloisForLFunctions"
PAPER = (
    ROOT
    / "docs/drafts/pipeline/4-publication-ready"
    / "riemann-source-modular-superselection"
)
TARGETS = {
    "RHTower": FORMAL / "RHTower",
    "HTGeometry": FORMAL / "HTGeometry",
}

CAMEL_TOKEN_RE = re.compile(
    r"[A-Z]+(?=[A-Z][a-z]|[0-9]|$)|[A-Z]?[a-z]+|[0-9]+"
)
MODULE_DOC_RE = re.compile(r"/-!\s*(.*?)\s*-/", re.DOTALL)
HEADING_RE = re.compile(r"^#+\s*", re.MULTILINE)

SIGNALS = {
    "rh": re.compile(r"\bRiemannHypothesis\b|\briemannHypothesis\b|\bRH\b"),
    "equivalence": re.compile(r"\biff\b|equivalent|equivalence|criterion", re.IGNORECASE),
    "no_go": re.compile(
        r"no.?go|obstruct|blind|imposs|cannot|fails?|collapse|barrier|exclusion|"
        r"unbounded|nonexist|not_exists|nowhere|counterexample|rigidity",
        re.IGNORECASE,
    ),
    "positive": re.compile(
        r"positive|nonneg|strict|faithful|inject|surject|reconstruct|recover|"
        r"tomograph|complete|classif|unique|exact|conservation|realization",
        re.IGNORECASE,
    ),
    "singular": re.compile(
        r"singular|boundary|corona|calkin|residue|pole|principal|extension|"
        r"completion|localization|graded|rees|anomal|curvature|cocycle",
        re.IGNORECASE,
    ),
    "orientation": re.compile(
        r"orientation|sign|phase|character|parity|unitar|reflection|odd|"
        r"chirotope|signature",
        re.IGNORECASE,
    ),
    "observer": re.compile(
        r"observer|reporter|finite.?horizon|recurrence|clock|jet|moment|"
        r"mellin|sampling|capacity|torelli|holograph|trace",
        re.IGNORECASE,
    ),
    "ht": re.compile(
        r"hypertrans|differential.?algebra|transcenden|kolchin|schwarzian|"
        r"projective.?horizon|differential.?field",
        re.IGNORECASE,
    ),
}


@dataclass(frozen=True)
class ModuleRow:
    area: str
    module: str
    family: str
    relpath: str
    lines: int
    declarations: int
    theorem_like: int
    flags: tuple[str, ...]
    title: str
    capstones: str


def camel_tokens(name: str) -> list[str]:
    return CAMEL_TOKEN_RE.findall(name)


def module_family(name: str, prefix_counts: dict[tuple[str, ...], int]) -> str:
    """Use deepest populated prefix, avoiding singleton pseudo-families."""
    tokens = camel_tokens(name)
    for depth in (4, 3, 2):
        prefix = tuple(tokens[:depth])
        if len(prefix) == depth and prefix_counts.get(prefix, 0) >= 3:
            return "".join(prefix)
    return tokens[0] if tokens else name


def module_title(source: str) -> str:
    match = MODULE_DOC_RE.search(source)
    if not match:
        return ""
    text = HEADING_RE.sub("", match.group(1))
    text = re.sub(r"`([^`]*)`", r"\1", text)
    text = re.sub(r"\s+", " ", text).strip()
    sentence = re.split(r"(?<=[.!?])\s+", text, maxsplit=1)[0]
    return sentence[:360]


def declaration_score(decl: Declaration) -> tuple[int, int, int]:
    text = f"{decl.name} {decl.doc}"
    score = sum(bool(pattern.search(text)) for pattern in SIGNALS.values())
    if decl.kind in {"theorem", "lemma"}:
        score += 2
    if decl.doc:
        score += 1
    return score, bool(decl.doc), decl.line


def summarize_capstones(module_decls: list[Declaration]) -> str:
    theorem_like = [d for d in module_decls if d.kind in {"theorem", "lemma"}]
    selected = sorted(theorem_like, key=declaration_score, reverse=True)[:4]
    return " | ".join(
        f"{d.name}: {d.doc}" if d.doc else d.name for d in selected
    )[:1800]


def build_rows() -> list[ModuleRow]:
    target_paths = sorted(
        path for directory in TARGETS.values() for path in directory.rglob("*.lean")
    )
    prefixes: Counter[tuple[str, ...]] = Counter()
    for path in target_paths:
        tokens = camel_tokens(path.stem)
        for depth in (1, 2, 3, 4):
            if len(tokens) >= depth:
                prefixes[tuple(tokens[:depth])] += 1

    by_relpath: dict[str, list[Declaration]] = defaultdict(list)
    for decl in declarations():
        if "/RHTower/" in decl.relpath or "/HTGeometry/" in decl.relpath:
            by_relpath[decl.relpath].append(decl)

    rows: list[ModuleRow] = []
    for path in target_paths:
        area, area_root = next(
            (name, directory)
            for name, directory in TARGETS.items()
            if path.is_relative_to(directory)
        )
        module = ".".join(path.relative_to(area_root).with_suffix("").parts)
        relpath = path.relative_to(ROOT).as_posix()
        source = path.read_text(encoding="utf-8")
        module_decls = by_relpath.get(relpath, [])
        signal_text = " ".join(
            [module, module_title(source)]
            + [f"{decl.name} {decl.doc}" for decl in module_decls]
        )
        flags = tuple(
            [name for name, pattern in SIGNALS.items() if pattern.search(signal_text)]
            + (["parser_zero"] if not module_decls else [])
        )
        rows.append(
            ModuleRow(
                area=area,
                module=module,
                family=module_family(path.stem, prefixes),
                relpath=relpath,
                lines=source.count("\n") + (not source.endswith("\n")),
                declarations=len(module_decls),
                theorem_like=sum(
                    decl.kind in {"theorem", "lemma"} for decl in module_decls
                ),
                flags=flags,
                title=module_title(source),
                capstones=summarize_capstones(module_decls),
            )
        )
    return rows


def write_tsv(rows: list[ModuleRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "area",
                "module",
                "family",
                "relpath",
                "lines",
                "declarations",
                "theorem_like",
                "flags",
                "title",
                "capstones",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.area,
                    row.module,
                    row.family,
                    row.relpath,
                    row.lines,
                    row.declarations,
                    row.theorem_like,
                    ",".join(row.flags),
                    row.title,
                    row.capstones,
                ]
            )


def write_summary(rows: list[ModuleRow], path: Path) -> None:
    by_area = Counter(row.area for row in rows)
    by_family: dict[str, list[ModuleRow]] = defaultdict(list)
    for row in rows:
        by_family[f"{row.area}/{row.family}"].append(row)

    high_signal = sorted(
        rows,
        key=lambda row: (
            len(row.flags),
            "rh" not in row.flags,
            row.theorem_like,
            row.module,
        ),
        reverse=True,
    )
    lines = [
        "# Whole-corpus mechanical census",
        "",
        "Generated by `scripts/rh_corpus_census.py`. This is coverage evidence, not a",
        "novelty or significance verdict. Every target module has exactly one TSV row;",
        "`formal/LEAN_API.md` remains the declaration-complete companion index.",
        "",
        f"- Modules: **{len(rows):,}**",
        f"- RHTower: **{by_area['RHTower']:,}**",
        f"- HTGeometry: **{by_area['HTGeometry']:,}**",
        f"- Declarations: **{sum(row.declarations for row in rows):,}**",
        f"- Theorems/lemmas: **{sum(row.theorem_like for row in rows):,}**",
        f"- Deterministic module families: **{len(by_family):,}**",
        f"- Modules with no declaration recognized by the shared parser: "
        f"**{sum(row.declarations == 0 for row in rows):,}**",
        "",
        "## Coverage invariants",
        "",
        "- one and only one row per `*.lean` file directly under each target area;",
        "- module, path, line count, declaration count, theorem count, title, and selected",
        "  high-signal declaration summaries recorded;",
        "- flags are lexical routing aids only; no flag is treated as proof of relevance;",
        "- final hostile audit must disposition every family and every high-signal row.",
        "",
        "## Largest deterministic families",
        "",
        "| Family | Modules | Declarations | Flags present |",
        "|---|---:|---:|---|",
    ]
    for family, members in sorted(
        by_family.items(), key=lambda item: (-len(item[1]), item[0])
    )[:250]:
        flags = sorted({flag for row in members for flag in row.flags})
        lines.append(
            f"| `{family}` | {len(members)} | "
            f"{sum(row.declarations for row in members)} | {', '.join(flags)} |"
        )
    lines += [
        "",
        "## Highest-signal routing queue",
        "",
        "This queue is exhaustive only together with TSV. It prioritizes manual review; it",
        "does not substitute for family dispositions.",
        "",
        "| Area/module | Family | Flags | Capstone synopsis |",
        "|---|---|---|---|",
    ]
    for row in high_signal[:1000]:
        synopsis = (row.capstones or row.title).replace("|", "\\|")[:420]
        lines.append(
            f"| `{row.area}/{row.module}` | `{row.family}` | "
            f"{', '.join(row.flags)} | {synopsis} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def validate(rows: list[ModuleRow], *, require_stable: bool) -> None:
    if require_stable:
        expected = sum(
            len(list(directory.rglob("*.lean"))) for directory in TARGETS.values()
        )
        if len(rows) != expected:
            raise SystemExit(
                f"coverage mismatch: {len(rows)} rows for {expected} modules"
            )
    keys = [row.relpath for row in rows]
    if len(keys) != len(set(keys)):
        raise SystemExit("duplicate area/module row")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tsv", type=Path, default=PAPER / "WHOLE_CORPUS_CENSUS.tsv"
    )
    parser.add_argument(
        "--summary", type=Path, default=PAPER / "WHOLE_CORPUS_CENSUS.md"
    )
    parser.add_argument(
        "--require-stable",
        action="store_true",
        help="fail if target module count changes while census is generated",
    )
    args = parser.parse_args()

    rows = build_rows()
    validate(rows, require_stable=args.require_stable)
    write_tsv(rows, args.tsv)
    write_summary(rows, args.summary)
    print(
        f"wrote {len(rows)} modules, "
        f"{sum(row.declarations for row in rows)} declarations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
