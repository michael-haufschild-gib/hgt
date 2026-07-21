"""Lean-native research-frontier extraction.

Lean theorem types are the only authority.  This module consumes an exact
export produced from the compiled Lean environment and computes unresolved
proposition cuts leading to a configured research target.
"""

from __future__ import annotations

import dataclasses
import itertools
import json
import subprocess
from pathlib import Path
from typing import Iterable, Mapping, Sequence


SCHEMA_VERSION = 1
EXPORT_SENTINEL = "HGT_FRONTIER_JSON:"
AREA_ALIASES = {
    "rh": "rh",
    "rh_tower": "rh",
    "riemann hypothesis": "rh",
}
AREA_TARGETS = {"rh": "RiemannHypothesis"}
VALID_RELATIONS = frozenset({"implication", "iff", "refutation"})
VALID_STATUSES = frozenset({"live", "retired"})


@dataclasses.dataclass(frozen=True)
class PropositionRef:
    key: str
    expression: str
    declaration: str | None = None


@dataclasses.dataclass(frozen=True)
class Reduction:
    name: str
    module: str
    type_text: str
    premises: tuple[PropositionRef, ...]
    conclusions: tuple[PropositionRef, ...]
    relation: str
    status: str = "live"
    type_dependencies: tuple[str, ...] = ()
    proof_dependencies: tuple[str, ...] = ()
    axioms: tuple[str, ...] = ()
    doc: str = ""
    relpath: str = ""
    line: int = 0


@dataclasses.dataclass(frozen=True)
class LeanFrontierExport:
    schema_version: int
    area: str
    target: PropositionRef
    reductions: tuple[Reduction, ...]
    commit: str = ""


@dataclasses.dataclass(frozen=True)
class FrontierNode:
    key: str
    expression: str
    declaration: str | None
    via_reductions: tuple[str, ...]
    distance_to_target: int
    relpath: str = ""
    line: int = 0


@dataclasses.dataclass(frozen=True)
class FrontierCut:
    nodes: tuple[FrontierNode, ...]
    via_reductions: tuple[str, ...]
    discharged: tuple[str, ...]
    distance_to_target: int
    unlock_count: int


@dataclasses.dataclass(frozen=True)
class ResearchBrief:
    area: str
    target: PropositionRef
    target_proven: bool
    cuts: tuple[FrontierCut, ...]
    frontier: tuple[FrontierNode, ...]
    equivalent_criteria: tuple[str, ...] = ()
    refuted_interfaces: tuple[str, ...] = ()
    retired_reductions: tuple[str, ...] = ()
    diagnostics: tuple[str, ...] = ()
    commit: str = ""


@dataclasses.dataclass(frozen=True)
class _Edge:
    name: str
    premises: tuple[str, ...]
    conclusions: tuple[str, ...]
    reduction: Reduction


@dataclasses.dataclass(frozen=True)
class _Solution:
    leaves: frozenset[str]
    path: tuple[str, ...]
    discharged: frozenset[str]


def canonical_area(area: str) -> str:
    key = " ".join(area.strip().lower().replace("-", "_").split())
    try:
        return AREA_ALIASES[key]
    except KeyError as error:
        accepted = ", ".join(sorted(AREA_ALIASES))
        raise ValueError(f"unknown area {area!r}; expected one of: {accepted}") from error


def _require_mapping(value: object, field: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{field} must be an object")
    return value


def _require_string(value: object, field: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value):
        raise ValueError(f"{field} must be a non-empty string")
    return value


def _string_tuple(value: object, field: str) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise ValueError(f"{field} must be an array of strings")
    return tuple(value)


def _parse_prop(value: object, field: str) -> PropositionRef:
    data = _require_mapping(value, field)
    declaration_value = data.get("declaration")
    if declaration_value is not None and not isinstance(declaration_value, str):
        raise ValueError(f"{field}.declaration must be a string or null")
    return PropositionRef(
        key=_require_string(data.get("key"), f"{field}.key"),
        expression=_require_string(data.get("expression"), f"{field}.expression"),
        declaration=declaration_value or None,
    )


def _parse_props(value: object, field: str) -> tuple[PropositionRef, ...]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be an array")
    return tuple(_parse_prop(item, f"{field}[{index}]") for index, item in enumerate(value))


def parse_lean_frontier_export(payload: str | Mapping[str, object]) -> LeanFrontierExport:
    try:
        raw = json.loads(payload) if isinstance(payload, str) else payload
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid Lean frontier JSON: {error}") from error
    data = _require_mapping(raw, "export")
    version = data.get("schema_version")
    if version != SCHEMA_VERSION:
        raise ValueError(
            f"unsupported schema_version {version!r}; expected {SCHEMA_VERSION}"
        )
    area = canonical_area(_require_string(data.get("area"), "area"))
    target = _parse_prop(data.get("target"), "target")
    raw_reductions = data.get("reductions")
    if not isinstance(raw_reductions, list):
        raise ValueError("reductions must be an array")

    reductions: list[Reduction] = []
    seen: set[str] = set()
    for index, raw_reduction in enumerate(raw_reductions):
        field = f"reductions[{index}]"
        item = _require_mapping(raw_reduction, field)
        name = _require_string(item.get("name"), f"{field}.name")
        if name in seen:
            raise ValueError(f"duplicate reduction declaration {name}")
        seen.add(name)
        relation = _require_string(item.get("relation"), f"{field}.relation")
        if relation not in VALID_RELATIONS:
            raise ValueError(f"{field}.relation has unsupported value {relation!r}")
        status = _require_string(item.get("status", "live"), f"{field}.status")
        if status not in VALID_STATUSES:
            raise ValueError(f"{field}.status has unsupported value {status!r}")
        source = item.get("source", {})
        source_data = _require_mapping(source, f"{field}.source")
        line_value = source_data.get("line", 0)
        if not isinstance(line_value, int) or line_value < 0:
            raise ValueError(f"{field}.source.line must be a nonnegative integer")
        reductions.append(
            Reduction(
                name=name,
                module=_require_string(item.get("module"), f"{field}.module"),
                type_text=_require_string(item.get("type_text"), f"{field}.type_text"),
                premises=_parse_props(item.get("premises", []), f"{field}.premises"),
                conclusions=_parse_props(
                    item.get("conclusions", []), f"{field}.conclusions"
                ),
                relation=relation,
                status=status,
                type_dependencies=_string_tuple(
                    item.get("type_dependencies", []), f"{field}.type_dependencies"
                ),
                proof_dependencies=_string_tuple(
                    item.get("proof_dependencies", []), f"{field}.proof_dependencies"
                ),
                axioms=_string_tuple(item.get("axioms", []), f"{field}.axioms"),
                doc=_require_string(item.get("doc", ""), f"{field}.doc", allow_empty=True),
                relpath=_require_string(
                    source_data.get("path", ""), f"{field}.source.path", allow_empty=True
                ),
                line=line_value,
            )
        )
    return LeanFrontierExport(
        schema_version=SCHEMA_VERSION,
        area=area,
        target=target,
        reductions=tuple(reductions),
        commit=_require_string(data.get("commit", ""), "commit", allow_empty=True),
    )


def load_lean_frontier_export(path: Path) -> LeanFrontierExport:
    try:
        return parse_lean_frontier_export(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise ValueError(f"cannot read Lean frontier graph {path}: {error}") from error


def _edges(export: LeanFrontierExport) -> tuple[tuple[_Edge, ...], tuple[str, ...], tuple[str, ...]]:
    edges: list[_Edge] = []
    refuted: set[str] = set()
    retired: list[str] = []
    for reduction in sorted(export.reductions, key=lambda item: item.name):
        if reduction.status == "retired":
            retired.append(reduction.name)
            continue
        if reduction.relation == "refutation":
            refuted.update(item.key for item in reduction.conclusions)
            continue
        premises = tuple(dict.fromkeys(item.key for item in reduction.premises))
        conclusions = tuple(dict.fromkeys(item.key for item in reduction.conclusions))
        if not conclusions:
            continue
        edges.append(_Edge(reduction.name, premises, conclusions, reduction))
        if reduction.relation == "iff" and len(premises) == 1 and len(conclusions) == 1:
            edges.append(
                _Edge(
                    reduction.name,
                    conclusions,
                    premises,
                    reduction,
                )
            )
    return tuple(edges), tuple(sorted(refuted)), tuple(retired)


def _closed_propositions(edges: Sequence[_Edge], refuted: frozenset[str]) -> frozenset[str]:
    closed: set[str] = set()
    changed = True
    while changed:
        changed = False
        for edge in edges:
            if any(premise in refuted for premise in edge.premises):
                continue
            if all(premise in closed for premise in edge.premises):
                for conclusion in edge.conclusions:
                    if conclusion not in closed:
                        closed.add(conclusion)
                        changed = True
    return frozenset(closed)


def _target_scc(target: str, edges: Sequence[_Edge]) -> frozenset[str]:
    adjacency: dict[str, set[str]] = {}
    reverse: dict[str, set[str]] = {}
    for edge in edges:
        if len(edge.premises) != 1:
            continue
        source = edge.premises[0]
        for conclusion in edge.conclusions:
            adjacency.setdefault(source, set()).add(conclusion)
            reverse.setdefault(conclusion, set()).add(source)

    def reachable(graph: Mapping[str, set[str]]) -> set[str]:
        seen = {target}
        stack = [target]
        while stack:
            node = stack.pop()
            for adjacent in graph.get(node, set()):
                if adjacent not in seen:
                    seen.add(adjacent)
                    stack.append(adjacent)
        return seen

    return frozenset(reachable(adjacency) & reachable(reverse))


def _prune_solutions(solutions: Iterable[_Solution], *, limit: int = 256) -> tuple[_Solution, ...]:
    unique: dict[tuple[frozenset[str], tuple[str, ...]], _Solution] = {}
    for solution in solutions:
        key = (solution.leaves, solution.path)
        current = unique.get(key)
        if current is None or len(solution.discharged) > len(current.discharged):
            unique[key] = solution
    ordered = sorted(
        unique.values(),
        key=lambda item: (
            len(item.leaves),
            -len(item.discharged),
            len(item.path),
            tuple(sorted(item.leaves)),
            item.path,
        ),
    )
    kept: list[_Solution] = []
    for solution in ordered:
        if any(
            existing.leaves < solution.leaves and len(existing.path) <= len(solution.path)
            for existing in kept
        ):
            continue
        kept.append(solution)
        if len(kept) == limit:
            break
    return tuple(kept)


def compute_frontier(export: LeanFrontierExport, *, limit: int = 12) -> ResearchBrief:
    edges, refuted_tuple, retired = _edges(export)
    refuted = frozenset(refuted_tuple)
    closed = _closed_propositions(edges, refuted)
    target = export.target.key
    target_scc = _target_scc(target, edges)
    equivalent = tuple(sorted(target_scc - {target}))
    incoming: dict[str, list[_Edge]] = {}
    refs: dict[str, PropositionRef] = {export.target.key: export.target}
    reduction_by_name = {item.name: item for item in export.reductions}
    for reduction in export.reductions:
        for ref in reduction.premises + reduction.conclusions:
            refs.setdefault(ref.key, ref)
    for edge in edges:
        for conclusion in edge.conclusions:
            incoming.setdefault(conclusion, []).append(edge)
    for edge_list in incoming.values():
        edge_list.sort(key=lambda item: item.name)

    memo: dict[str, tuple[_Solution, ...]] = {}

    def derive(goal: str, stack: frozenset[str]) -> tuple[_Solution, ...]:
        if goal in closed:
            return (_Solution(frozenset(), (), frozenset({goal})),)
        if goal in refuted or goal in stack:
            return ()
        if goal != target and goal in target_scc:
            return ()
        if goal in memo:
            return memo[goal]

        candidates = [
            edge
            for edge in incoming.get(goal, [])
            if not (
                len(edge.premises) == 1
                and edge.premises[0] in target_scc
                and goal in target_scc
            )
        ]
        if not candidates:
            if goal == target or goal in refuted:
                return ()
            result = (_Solution(frozenset({goal}), (), frozenset()),)
            memo[goal] = result
            return result

        results: list[_Solution] = []
        next_stack = stack | {goal}
        for edge in candidates:
            per_premise = [derive(premise, next_stack) for premise in edge.premises]
            if any(not choices for choices in per_premise):
                continue
            combinations = itertools.product(*per_premise) if per_premise else [()]
            for combination in combinations:
                leaves = frozenset().union(*(item.leaves for item in combination))
                path: list[str] = []
                discharged: set[str] = set()
                for item in combination:
                    for name in item.path:
                        if name not in path:
                            path.append(name)
                    discharged.update(item.discharged)
                if edge.name not in path:
                    path.append(edge.name)
                discharged.update(premise for premise in edge.premises if premise in closed)
                results.append(_Solution(leaves, tuple(path), frozenset(discharged)))
        result = _prune_solutions(results)
        memo[goal] = result
        return result

    if target in closed:
        solutions = ()
    else:
        solutions = derive(target, frozenset())

    cuts: list[FrontierCut] = []
    for solution in solutions:
        if not solution.leaves:
            continue
        nodes: list[FrontierNode] = []
        for key in sorted(solution.leaves):
            ref = refs.get(key, PropositionRef(key, key, key))
            source_reduction = next(
                (
                    reduction_by_name[name]
                    for name in solution.path
                    if any(item.key == key for item in reduction_by_name[name].premises)
                ),
                None,
            )
            nodes.append(
                FrontierNode(
                    key=key,
                    expression=ref.expression,
                    declaration=ref.declaration,
                    via_reductions=solution.path,
                    distance_to_target=len(solution.path),
                    relpath=source_reduction.relpath if source_reduction else "",
                    line=source_reduction.line if source_reduction else 0,
                )
            )
        cuts.append(
            FrontierCut(
                nodes=tuple(nodes),
                via_reductions=solution.path,
                discharged=tuple(sorted(solution.discharged)),
                distance_to_target=len(solution.path),
                unlock_count=len(set(solution.path)),
            )
        )
    cuts.sort(
        key=lambda cut: (
            len(cut.nodes),
            -cut.unlock_count,
            cut.distance_to_target,
            tuple(node.key for node in cut.nodes),
        )
    )
    cuts = cuts[: max(0, limit)]
    frontier: list[FrontierNode] = []
    seen_frontier: set[str] = set()
    for cut in cuts:
        for node in cut.nodes:
            if node.key not in seen_frontier:
                frontier.append(node)
                seen_frontier.add(node.key)
    return ResearchBrief(
        area=export.area,
        target=export.target,
        target_proven=target in closed,
        cuts=tuple(cuts),
        frontier=tuple(frontier),
        equivalent_criteria=equivalent,
        refuted_interfaces=refuted_tuple,
        retired_reductions=retired,
        commit=export.commit,
    )


def run_lean_frontier_export(root: Path, *, area: str) -> LeanFrontierExport:
    canonical = canonical_area(area)
    if canonical != "rh":
        raise ValueError(f"no Lean exporter configured for area {canonical}")
    exporter = root / "scripts" / "lean" / "export_research_frontier.lean"
    if not exporter.exists():
        raise ValueError(f"Lean frontier exporter not found: {exporter}")
    process = subprocess.run(
        ["lake", "env", "lean", str(exporter)],
        cwd=root / "formal",
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if process.returncode:
        detail = (process.stderr or process.stdout).strip()
        raise ValueError(f"Lean frontier export failed: {detail}")
    payload = next(
        (
            line[len(EXPORT_SENTINEL) :]
            for line in process.stdout.splitlines()
            if line.startswith(EXPORT_SENTINEL)
        ),
        None,
    )
    if payload is None:
        raise ValueError("Lean frontier exporter produced no graph payload")
    return parse_lean_frontier_export(payload)


def build_research_brief(
    *,
    root: Path,
    area: str,
    graph_path: Path | None = None,
    limit: int = 12,
    declarations: Sequence[object] | None = None,
) -> ResearchBrief:
    del declarations  # Legacy regex declarations are intentionally not frontier evidence.
    export = (
        load_lean_frontier_export(graph_path)
        if graph_path is not None
        else run_lean_frontier_export(root, area=area)
    )
    expected = canonical_area(area)
    if export.area != expected:
        raise ValueError(f"graph area {export.area!r} does not match requested area {expected!r}")
    return compute_frontier(export, limit=limit)


def render_research_brief(brief: ResearchBrief) -> str:
    lines = [
        f"# Lean research frontier: {brief.area}",
        "",
        f"Target: `{brief.target.expression}`",
        f"Target closed by corpus: `{'yes' if brief.target_proven else 'no'}`",
        "",
    ]
    if not brief.cuts:
        lines.append("No unresolved Lean-verified cut found.")
    else:
        lines.extend(["## Minimal open cuts", ""])
        for index, cut in enumerate(brief.cuts, start=1):
            declarations = " + ".join(f"`{node.key}`" for node in cut.nodes)
            lines.append(f"{index}. {declarations}")
            lines.append(f"   - Closed route: {' → '.join(f'`{name}`' for name in cut.via_reductions)}")
            if cut.discharged:
                lines.append(
                    "   - Already discharged: "
                    + ", ".join(f"`{name}`" for name in cut.discharged)
                )
    if brief.equivalent_criteria:
        lines.extend(["", "## RH-equivalent criteria (not frontier tasks)", ""])
        lines.append(", ".join(f"`{name}`" for name in brief.equivalent_criteria))
    if brief.refuted_interfaces:
        lines.extend(["", "## Refuted interfaces", ""])
        lines.append(", ".join(f"`{name}`" for name in brief.refuted_interfaces))
    if brief.retired_reductions:
        lines.extend(["", "## Retired Lean reductions", ""])
        lines.append(", ".join(f"`{name}`" for name in brief.retired_reductions))
    return "\n".join(lines).rstrip() + "\n"


def _prop_dict(prop: PropositionRef) -> dict[str, object]:
    return {
        "key": prop.key,
        "expression": prop.expression,
        "declaration": prop.declaration,
    }


def render_research_brief_json(brief: ResearchBrief) -> str:
    payload = {
        "schema_version": SCHEMA_VERSION,
        "area": brief.area,
        "commit": brief.commit,
        "target": _prop_dict(brief.target),
        "target_proven": brief.target_proven,
        "cuts": [
            {
                "nodes": [dataclasses.asdict(node) for node in cut.nodes],
                "via_reductions": list(cut.via_reductions),
                "discharged": list(cut.discharged),
                "distance_to_target": cut.distance_to_target,
                "unlock_count": cut.unlock_count,
            }
            for cut in brief.cuts
        ],
        "equivalent_criteria": list(brief.equivalent_criteria),
        "refuted_interfaces": list(brief.refuted_interfaces),
        "retired_reductions": list(brief.retired_reductions),
        "diagnostics": list(brief.diagnostics),
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"
