"""Lean-native research-frontier extraction.

Lean theorem types are the only authority.  This module consumes an exact
export produced from the compiled Lean environment and computes unresolved
proposition cuts leading to a configured research target.
"""

from __future__ import annotations

import dataclasses
import itertools
import json
import os
import re
import subprocess
import tempfile
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
IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
PROP_RESULT_RE = re.compile(r":\s*Prop\b")


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
    provenance: str = "declared"
    witness: str | None = None
    solver_depth: int = 0
    solver_attempts: int = 0


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
class ReductionEvidence:
    name: str
    module: str
    relpath: str = ""
    line: int = 0
    provenance: str = "declared"
    witness: str | None = None


@dataclasses.dataclass(frozen=True)
class FrontierCut:
    nodes: tuple[FrontierNode, ...]
    via_reductions: tuple[str, ...]
    discharged: tuple[str, ...]
    distance_to_target: int
    unlock_count: int
    reductions: tuple[ReductionEvidence, ...] = ()
    proof_steps: int = 0


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
    max_gaps: int = 0
    total_cuts: int = 0


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
    depth: int = 0
    steps: int = 0
    proof_nodes: frozenset[str] = frozenset()


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
        provenance = _require_string(
            item.get("provenance", "declared"), f"{field}.provenance"
        )
        if provenance not in {"declared", "interface_solver"}:
            raise ValueError(f"{field}.provenance has unsupported value {provenance!r}")
        witness_value = item.get("witness")
        if witness_value is not None and not isinstance(witness_value, str):
            raise ValueError(f"{field}.witness must be a string or null")
        solver_depth = item.get("solver_depth", 0)
        solver_attempts = item.get("solver_attempts", 0)
        if not isinstance(solver_depth, int) or solver_depth < 0:
            raise ValueError(f"{field}.solver_depth must be a nonnegative integer")
        if not isinstance(solver_attempts, int) or solver_attempts < 0:
            raise ValueError(f"{field}.solver_attempts must be a nonnegative integer")
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
                provenance=provenance,
                witness=witness_value or None,
                solver_depth=solver_depth,
                solver_attempts=solver_attempts,
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


def render_lean_frontier_export_json(export: LeanFrontierExport) -> str:
    payload = {
        "schema_version": export.schema_version,
        "area": export.area,
        "commit": export.commit,
        "target": _prop_dict(export.target),
        "reductions": [
            {
                "name": reduction.name,
                "module": reduction.module,
                "type_text": reduction.type_text,
                "premises": [_prop_dict(item) for item in reduction.premises],
                "conclusions": [_prop_dict(item) for item in reduction.conclusions],
                "relation": reduction.relation,
                "status": reduction.status,
                "type_dependencies": list(reduction.type_dependencies),
                "proof_dependencies": list(reduction.proof_dependencies),
                "axioms": list(reduction.axioms),
                "doc": reduction.doc,
                "source": {"path": reduction.relpath, "line": reduction.line},
                "provenance": reduction.provenance,
                "witness": reduction.witness,
                "solver_depth": reduction.solver_depth,
                "solver_attempts": reduction.solver_attempts,
            }
            for reduction in export.reductions
        ],
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True) + "\n"


def frontier_export_candidates(
    root: Path, declarations: Sequence[object]
) -> tuple[str, ...]:
    """Cheap source prefilter; compiled Lean types remain authoritative.

    Only theorem signatures mentioning a corpus-declared `Prop` interface can
    form the graph used here.  False positives are harmless because exporter
    validates and structurally classifies every candidate in Lean.
    """

    grouped: dict[str, list[object]] = {}
    for declaration in declarations:
        relpath = str(getattr(declaration, "relpath", ""))
        line = getattr(declaration, "line", 0)
        if relpath and isinstance(line, int) and line > 0:
            grouped.setdefault(relpath, []).append(declaration)

    headers: list[tuple[object, str]] = []
    for relpath, file_declarations in sorted(grouped.items()):
        path = root / relpath
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        ordered = sorted(file_declarations, key=lambda item: int(getattr(item, "line")))
        for index, declaration in enumerate(ordered):
            start = int(getattr(declaration, "line")) - 1
            end = (
                int(getattr(ordered[index + 1], "line")) - 1
                if index + 1 < len(ordered)
                else len(lines)
            )
            block = "\n".join(lines[start:end])
            headers.append((declaration, block.split(":=", 1)[0]))

    prop_names = {"RiemannHypothesis"}
    for declaration, header in headers:
        if getattr(declaration, "kind", "") in {
            "def",
            "abbrev",
            "inductive",
            "class",
            "structure",
        } and PROP_RESULT_RE.search(header):
            prop_names.add(str(getattr(declaration, "name")).split(".")[-1])

    theorem_refs: list[tuple[object, frozenset[str]]] = []
    consumers: dict[str, list[int]] = {}
    for declaration, header in headers:
        if getattr(declaration, "kind", "") not in {"theorem", "lemma"}:
            continue
        refs = frozenset(prop_names.intersection(IDENTIFIER_RE.findall(header)))
        if not refs:
            continue
        index = len(theorem_refs)
        theorem_refs.append((declaration, refs))
        for ref in refs:
            consumers.setdefault(ref, []).append(index)

    # Lexical pass only bounds work. Lean rechecks exact heads, binders, and
    # implication direction. Traverse complete named-Prop component of target.
    pending = ["RiemannHypothesis"]
    seen_props: set[str] = set()
    seen_theorems: set[int] = set()
    while pending:
        proposition = pending.pop()
        if proposition in seen_props:
            continue
        seen_props.add(proposition)
        for index in consumers.get(proposition, ()):
            if index in seen_theorems:
                continue
            seen_theorems.add(index)
            pending.extend(theorem_refs[index][1] - seen_props)

    qualified: set[str] = set()
    for index in seen_theorems:
        declaration = theorem_refs[index][0]
        raw_name = str(getattr(declaration, "name"))
        qualified.add(raw_name)
        module_parts = str(getattr(declaration, "module", "")).split(".")
        if len(module_parts) >= 2 and module_parts[0] == "GaloisForLFunctions":
            area_namespace = module_parts[1]
            if not raw_name.startswith(area_namespace + "."):
                qualified.add(f"{area_namespace}.{raw_name}")
    return tuple(sorted(qualified))


def corpus_theorem_candidates(declarations: Sequence[object]) -> tuple[str, ...]:
    """Return source-indexed theorem names for Lean to validate against compiled corpus.

    Source index is only a cheap name supplier. Missing, stale, and active-WIP names
    are ignored by the Lean environment; no source file is compiled here.
    """

    qualified: set[str] = set()
    for declaration in declarations:
        if getattr(declaration, "kind", "") not in {"theorem", "lemma"}:
            continue
        raw_name = str(getattr(declaration, "name", ""))
        if not raw_name:
            continue
        qualified.add(raw_name)
        module_parts = str(getattr(declaration, "module", "")).split(".")
        if len(module_parts) >= 2 and module_parts[0] == "GaloisForLFunctions":
            area_namespace = module_parts[1]
            if not raw_name.startswith(area_namespace + "."):
                qualified.add(f"{area_namespace}.{raw_name}")
            if not raw_name.startswith("GaloisForLFunctions."):
                qualified.add(f"GaloisForLFunctions.{raw_name}")
    return tuple(sorted(qualified))


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
    unique: dict[frozenset[str], _Solution] = {}
    for solution in solutions:
        current = unique.get(solution.leaves)
        if current is None or (
            len(solution.path), len(solution.discharged), solution.path
        ) > (
            len(current.path), len(current.discharged), current.path
        ):
            unique[solution.leaves] = solution
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


def _reduction_evidence(
    path: Sequence[str], reductions: Mapping[str, Reduction]
) -> tuple[ReductionEvidence, ...]:
    return tuple(
        ReductionEvidence(
            name=name,
            module=reductions[name].module,
            relpath=reductions[name].relpath,
            line=reductions[name].line,
            provenance=reductions[name].provenance,
            witness=reductions[name].witness,
        )
        for name in path
        if name in reductions
    )


def compute_frontier(export: LeanFrontierExport, *, limit: int = 12) -> ResearchBrief:
    edges, refuted_tuple, retired = _edges(export)
    refuted = frozenset(refuted_tuple)
    closed = _closed_propositions(edges, refuted)
    target = export.target.key
    target_scc = _target_scc(target, edges)
    incoming: dict[str, list[_Edge]] = {}
    refs: dict[str, PropositionRef] = {export.target.key: export.target}
    reduction_by_name = {item.name: item for item in export.reductions}
    for reduction in export.reductions:
        for ref in reduction.premises + reduction.conclusions:
            refs.setdefault(ref.key, ref)
    equivalent = tuple(
        sorted(
            {
                (refs.get(key).declaration if refs.get(key) else None) or key
                for key in target_scc - {target}
            }
        )
    )
    refuted_display = tuple(
        sorted(
            {
                (refs.get(key).declaration if refs.get(key) else None) or key
                for key in refuted_tuple
            }
        )
    )
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
                reductions=_reduction_evidence(solution.path, reduction_by_name),
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
        refuted_interfaces=refuted_display,
        retired_reductions=retired,
        commit=export.commit,
        total_cuts=len(cuts),
    )


def _solution_preference(solution: _Solution) -> tuple[object, ...]:
    """Canonical witness ordering for one exact cost state."""

    return (solution.depth, solution.steps, solution.path)


def _solution_state_key(
    solution: _Solution,
) -> tuple[frozenset[str], int, int]:
    return (solution.leaves, solution.depth, solution.steps)


def _dominates(left: _Solution, right: _Solution) -> bool:
    """Safe compositional dominance for bounded hypergraph propagation."""

    return (
        left.leaves <= right.leaves
        and left.depth <= right.depth
        and left.steps <= right.steps
    )


def _insert_nondominated_solution(
    table: dict[tuple[frozenset[str], int, int], _Solution],
    candidate: _Solution,
    *,
    max_gaps: int,
) -> bool:
    """Insert one state without losing a cheaper useful superset witness."""

    if len(candidate.leaves) > max_gaps:
        return False
    key = _solution_state_key(candidate)
    current = table.get(key)
    if current is not None:
        if candidate.path < current.path:
            table[key] = candidate
            return True
        return False
    if any(_dominates(existing, candidate) for existing in table.values()):
        return False
    dominated = [
        state_key
        for state_key, existing in table.items()
        if _dominates(candidate, existing)
    ]
    for state_key in dominated:
        del table[state_key]
    table[key] = candidate
    return True


def enumerate_frontier_chains(
    export: LeanFrontierExport,
    *,
    max_gaps: int = 4,
    limit: int | None = None,
) -> ResearchBrief:
    """Enumerate all subset-minimal target chains with at most ``max_gaps``.

    This is an exact bounded fixed point over the theorem AND/OR hypergraph.
    Each retained solution is identified by its unresolved proposition set;
    cycles cannot manufacture solutions because they have no initial proof seed.
    """

    if max_gaps < 1:
        raise ValueError("max_gaps must be at least 1")
    if limit is not None and limit < 0:
        raise ValueError("limit must be nonnegative or None")

    edges, refuted_tuple, retired = _edges(export)
    refuted = frozenset(refuted_tuple)
    closed = _closed_propositions(edges, refuted)
    target = export.target.key
    target_scc = _target_scc(target, edges)
    reduction_by_name = {item.name: item for item in export.reductions}
    refs: dict[str, PropositionRef] = {target: export.target}
    nodes = {target}
    for reduction in export.reductions:
        for ref in reduction.premises + reduction.conclusions:
            refs.setdefault(ref.key, ref)
            nodes.add(ref.key)

    solutions: dict[
        str, dict[tuple[frozenset[str], int, int], _Solution]
    ] = {
        node: {} for node in nodes
    }
    for node in sorted(nodes):
        if node in refuted:
            continue
        if node not in closed and node != target and node not in target_scc:
            leaves = frozenset({node})
            seed = _Solution(
                leaves,
                (),
                frozenset(),
                depth=0,
                steps=0,
                proof_nodes=frozenset({node}),
            )
            solutions[node][_solution_state_key(seed)] = seed

    changed = True
    iterations = 0
    ordered_edges = tuple(sorted(edges, key=lambda item: item.name))
    while changed:
        changed = False
        iterations += 1
        for edge in ordered_edges:
            if any(premise in refuted for premise in edge.premises):
                continue
            per_premise = [tuple(solutions.get(premise, {}).values()) for premise in edge.premises]
            if any(not choices for choices in per_premise):
                continue
            combinations = itertools.product(*per_premise) if per_premise else [()]
            for combination in combinations:
                leaves = frozenset().union(
                    *(item.leaves for item in combination)
                )
                if len(leaves) > max_gaps:
                    continue
                path: list[str] = []
                discharged: set[str] = set()
                proof_nodes: set[str] = set()
                for premise, item in zip(edge.premises, combination):
                    if item.leaves:
                        for name in item.path:
                            if name not in path:
                                path.append(name)
                    discharged.update(item.discharged)
                    proof_nodes.update(item.proof_nodes)
                    if not item.leaves:
                        discharged.add(premise)
                if edge.name not in path:
                    path.append(edge.name)
                for conclusion in edge.conclusions:
                    if conclusion in refuted or conclusion in proof_nodes:
                        continue
                    candidate = _Solution(
                        leaves,
                        tuple(path),
                        frozenset(discharged),
                        depth=1 + max((item.depth for item in combination), default=0),
                        steps=1 + sum(item.steps for item in combination),
                        proof_nodes=frozenset(proof_nodes | {conclusion}),
                    )
                    if _insert_nondominated_solution(
                        solutions.setdefault(conclusion, {}),
                        candidate,
                        max_gaps=max_gaps,
                    ):
                        changed = True

    target_states = tuple(solutions.get(target, {}).values())
    target_solutions: tuple[_Solution, ...]
    if target in closed or any(not solution.leaves for solution in target_states):
        target_solutions = ()
    else:
        minimal_gap_sets = {
            solution.leaves
            for solution in target_states
            if solution.leaves
            and not any(
                other.leaves < solution.leaves
                for other in target_states
                if other.leaves
            )
        }
        target_solutions = tuple(
            min(
                (
                    solution
                    for solution in target_states
                    if solution.leaves == leaves
                ),
                key=_solution_preference,
            )
            for leaves in minimal_gap_sets
        )
    cuts: list[FrontierCut] = []
    for solution in target_solutions:
        frontier_nodes: list[FrontierNode] = []
        for key in sorted(solution.leaves):
            ref = refs.get(key, PropositionRef(key, key, key))
            source_reduction = next(
                (
                    reduction_by_name[name]
                    for name in solution.path
                    if name in reduction_by_name
                    and any(
                        premise.key == key
                        for premise in reduction_by_name[name].premises
                    )
                ),
                None,
            )
            frontier_nodes.append(
                FrontierNode(
                    key=key,
                    expression=ref.expression,
                    declaration=ref.declaration,
                    via_reductions=solution.path,
                    distance_to_target=solution.depth,
                    relpath=source_reduction.relpath if source_reduction else "",
                    line=source_reduction.line if source_reduction else 0,
                )
            )
        cuts.append(
            FrontierCut(
                nodes=tuple(frontier_nodes),
                via_reductions=solution.path,
                discharged=tuple(sorted(solution.discharged)),
                distance_to_target=solution.depth,
                unlock_count=len(set(solution.path)),
                reductions=_reduction_evidence(solution.path, reduction_by_name),
                proof_steps=solution.steps,
            )
        )

    cuts.sort(
        key=lambda cut: (
            len(cut.nodes),
            cut.distance_to_target,
            cut.proof_steps,
            tuple(node.key for node in cut.nodes),
            cut.via_reductions,
        )
    )
    total_cuts = len(cuts)
    selected = cuts if limit is None else cuts[:limit]
    frontier: list[FrontierNode] = []
    seen_frontier: set[str] = set()
    for cut in selected:
        for node in cut.nodes:
            if node.key not in seen_frontier:
                frontier.append(node)
                seen_frontier.add(node.key)

    equivalent = tuple(
        sorted(
            {
                (refs.get(key).declaration if refs.get(key) else None) or key
                for key in target_scc - {target}
            }
        )
    )
    refuted_display = tuple(
        sorted(
            {
                (refs.get(key).declaration if refs.get(key) else None) or key
                for key in refuted_tuple
            }
        )
    )
    counts = {
        gap_count: sum(len(cut.nodes) == gap_count for cut in cuts)
        for gap_count in range(1, max_gaps + 1)
    }
    diagnostics = (
        f"exact bounded fixed point converged in {iterations} iterations",
        "minimal cuts by gap count: "
        + ", ".join(f"{gap_count}={counts[gap_count]}" for gap_count in counts),
    )
    return ResearchBrief(
        area=export.area,
        target=export.target,
        target_proven=target in closed,
        cuts=tuple(selected),
        frontier=tuple(frontier),
        equivalent_criteria=equivalent,
        refuted_interfaces=refuted_display,
        retired_reductions=retired,
        diagnostics=diagnostics,
        commit=export.commit,
        max_gaps=max_gaps,
        total_cuts=total_cuts,
    )


def run_lean_frontier_export(
    root: Path,
    *,
    area: str,
    declarations: Sequence[object],
    refresh: bool = False,
) -> LeanFrontierExport:
    canonical = canonical_area(area)
    if canonical != "rh":
        raise ValueError(f"no Lean exporter configured for area {canonical}")
    exporter = root / "scripts" / "lean" / "export_research_frontier.lean"
    if not exporter.exists():
        raise ValueError(f"Lean frontier exporter not found: {exporter}")
    cache = root / "formal" / ".lake" / "hgt-research" / f"{canonical}-frontier.json"
    compiled_umbrella = (
        root / "formal" / ".lake" / "build" / "lib" / "lean" / "GaloisForLFunctions.olean"
    )
    if not compiled_umbrella.exists():
        raise ValueError(
            "compiled GaloisForLFunctions umbrella is missing; build a stable corpus snapshot first"
        )
    newest_input = max(
        (
            path.stat().st_mtime
            for path in {compiled_umbrella, exporter, Path(__file__).resolve()}
            if path.exists()
        ),
        default=0.0,
    )
    if not refresh and cache.exists() and cache.stat().st_mtime >= newest_input:
        return load_lean_frontier_export(cache)
    theorem_names = frontier_export_candidates(root, declarations)
    if not theorem_names:
        raise ValueError("Lean frontier export received no corpus theorem declarations")
    command = (
        "\n#export_research_frontier_with_producers [\n"
        + ",\n".join(f"  {json.dumps(name)}" for name in theorem_names)
        + "\n] using []\n"
    )
    template = exporter.read_text(encoding="utf-8")
    project_import = "import GaloisForLFunctions\n"
    if project_import not in template:
        raise ValueError("Lean frontier exporter is missing project import marker")
    generated_source = template + command
    with tempfile.TemporaryDirectory(prefix="hgt-frontier-") as temporary:
        generated = Path(temporary) / "ExportResearchFrontier.lean"
        generated.write_text(generated_source, encoding="utf-8")
        timeout_seconds = int(os.environ.get("HGT_FRONTIER_TIMEOUT_SECONDS", "300"))
        try:
            process = subprocess.run(
                ["lake", "env", "lean", str(generated)],
                cwd=root / "formal",
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=timeout_seconds,
            )
        except subprocess.TimeoutExpired as error:
            output = error.stdout or error.stderr or ""
            if isinstance(output, bytes):
                output = output.decode("utf-8", errors="replace")
            detail = output.strip()
            raise ValueError(
                f"Lean frontier export exceeded {timeout_seconds} seconds on compiled corpus snapshot"
                + (f":\n{detail}" if detail else "")
            ) from error
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
    export = parse_lean_frontier_export(payload)
    source_index = {
        (str(getattr(declaration, "module", "")), str(getattr(declaration, "name", ""))): declaration
        for declaration in declarations
    }
    enriched: list[Reduction] = []
    for reduction in export.reductions:
        # Solver-generated edges have synthetic names; their kernel-checked
        # witness is the declaration whose source location matters.
        source_name = reduction.witness or reduction.name
        parts = source_name.split(".")
        source = next(
            (
                source_index[(reduction.module, ".".join(parts[index:]))]
                for index in range(len(parts))
                if (reduction.module, ".".join(parts[index:])) in source_index
            ),
            None,
        )
        enriched.append(
            dataclasses.replace(
                reduction,
                relpath=(str(getattr(source, "relpath")) if source else reduction.relpath),
                line=(int(getattr(source, "line")) if source else reduction.line),
            )
        )
    export = dataclasses.replace(export, reductions=tuple(enriched))
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(render_lean_frontier_export_json(export), encoding="utf-8")
    return export


def build_research_brief(
    *,
    root: Path,
    area: str,
    graph_path: Path | None = None,
    limit: int = 12,
    declarations: Sequence[object] | None = None,
    refresh: bool = False,
) -> ResearchBrief:
    # Source declaration names bound export cost; Lean still validates every
    # name and supplies all logical data used by frontier computation.
    export = (
        load_lean_frontier_export(graph_path)
        if graph_path is not None
        else run_lean_frontier_export(
            root,
            area=area,
            declarations=declarations or (),
            refresh=refresh,
        )
    )
    expected = canonical_area(area)
    if export.area != expected:
        raise ValueError(f"graph area {export.area!r} does not match requested area {expected!r}")
    return compute_frontier(export, limit=limit)


def build_frontier_chains(
    *,
    root: Path,
    area: str,
    graph_path: Path | None = None,
    max_gaps: int = 4,
    limit: int | None = None,
    declarations: Sequence[object] | None = None,
    refresh: bool = False,
) -> ResearchBrief:
    export = (
        load_lean_frontier_export(graph_path)
        if graph_path is not None
        else run_lean_frontier_export(
            root,
            area=area,
            declarations=declarations or (),
            refresh=refresh,
        )
    )
    expected = canonical_area(area)
    if export.area != expected:
        raise ValueError(
            f"graph area {export.area!r} does not match requested area {expected!r}"
        )
    return enumerate_frontier_chains(
        export,
        max_gaps=max_gaps,
        limit=limit,
    )


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
            sources = sorted(
                {
                    f"{node.relpath}:{node.line}"
                    for node in cut.nodes
                    if node.relpath and node.line
                }
            )
            if sources:
                lines.append("   - Lean evidence: " + ", ".join(f"`{source}`" for source in sources))
            lines.append(f"   - Closed route: {' → '.join(f'`{name}`' for name in cut.via_reductions)}")
            if cut.discharged:
                lines.append(
                    "   - Already discharged: "
                    + ", ".join(f"`{name}`" for name in cut.discharged)
                )
    if brief.equivalent_criteria:
        lines.extend(["", "## RH-equivalent criteria (not frontier tasks)", ""])
        shown = brief.equivalent_criteria[:12]
        lines.append(", ".join(f"`{name}`" for name in shown))
        if len(brief.equivalent_criteria) > len(shown):
            lines.append(
                f"\n{len(brief.equivalent_criteria) - len(shown)} more in JSON output."
            )
    if brief.refuted_interfaces:
        lines.extend(["", "## Refuted interfaces", ""])
        shown = brief.refuted_interfaces[:12]
        lines.append(", ".join(f"`{name}`" for name in shown))
        if len(brief.refuted_interfaces) > len(shown):
            lines.append(f"\n{len(brief.refuted_interfaces) - len(shown)} more in JSON output.")
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
                "gap_count": len(cut.nodes),
                "reductions": [dataclasses.asdict(item) for item in cut.reductions],
            }
            for cut in brief.cuts
        ],
        "equivalent_criteria": list(brief.equivalent_criteria),
        "refuted_interfaces": list(brief.refuted_interfaces),
        "retired_reductions": list(brief.retired_reductions),
        "diagnostics": list(brief.diagnostics),
        "max_gaps": brief.max_gaps,
        "total_cuts": brief.total_cuts,
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _report_slug(cut: FrontierCut) -> str:
    labels = [node.declaration or node.key for node in cut.nodes]
    raw = "-and-".join(labels)
    slug = re.sub(r"[^a-z0-9]+", "-", raw.lower()).strip("-")
    return (slug[:72].rstrip("-") or "unnamed-gap")


def write_chain_reports(
    brief: ResearchBrief,
    output_dir: Path,
    *,
    limit: int = 20,
) -> tuple[Path, ...]:
    """Write deterministic Markdown reports for least-gap chains."""

    if limit < 0:
        raise ValueError("limit must be nonnegative")
    output_dir.mkdir(parents=True, exist_ok=True)
    selected = brief.cuts[:limit]
    report_paths: list[Path] = []
    index_rows: list[str] = []

    for index, cut in enumerate(selected, start=1):
        filename = f"chain-{index:02d}-{_report_slug(cut)}.md"
        path = output_dir / filename
        gap_count = len(cut.nodes)
        lines = [
            f"# RH frontier chain {index:02d}",
            "",
            "Generated automatically from kernel-checked theorem types in the compiled Lean corpus snapshot.",
            "Active uncompiled work-in-progress files, cards, prose, and model judgment are not inputs.",
            "",
            f"- Gap count: **{gap_count}**",
            f"- Checked reductions: **{len(cut.reductions)}**",
            f"- Search bound: `max_gaps={brief.max_gaps or 4}`",
            f"- Corpus commit: `{brief.commit or 'not recorded'}`",
            "",
            "## Open gaps",
            "",
        ]
        for gap_index, node in enumerate(cut.nodes, start=1):
            label = node.declaration or node.key
            lines.extend(
                [
                    f"### {gap_index}. `{label}`",
                    "",
                    f"- Exact proposition: `{node.expression}`",
                ]
            )
            if node.relpath:
                source = f"{node.relpath}:{node.line}" if node.line else node.relpath
                lines.append(f"- Lean source: `{source}`")
            lines.append("")

        lines.extend(["## Kernel-checked route", ""])
        for route_index, evidence in enumerate(cut.reductions, start=1):
            source = evidence.relpath
            if source and evidence.line:
                source += f":{evidence.line}"
            suffix = f" — `{source}`" if source else ""
            lines.append(f"{route_index}. `{evidence.name}`{suffix}")
            if evidence.provenance == "interface_solver":
                lines.append(
                    f"   - Semantic interface witness: `{evidence.witness or evidence.name}`"
                )
        if cut.discharged:
            lines.extend(
                [
                    "",
                    "## Already discharged interfaces",
                    "",
                    *[f"- `{name}`" for name in cut.discharged],
                ]
            )
        lines.extend(
            [
                "",
                "## Interpretation",
                "",
                "Proving every open gap above is sufficient to complete this checked route to `RiemannHypothesis`.",
                "Absence of an automatic interface witness means only that bounded proof search found none; it is not a mathematical nonexistence claim.",
                "",
            ]
        )
        path.write_text("\n".join(lines), encoding="utf-8")
        report_paths.append(path)
        gap_labels = " + ".join(
            f"`{node.declaration or node.key}`" for node in cut.nodes
        )
        index_rows.append(
            f"| {index} | {gap_count} | {len(cut.reductions)} | {gap_labels} | [{filename}]({filename}) |"
        )

    index_path = output_dir / "index.md"
    counts = {
        gap_count: sum(len(cut.nodes) == gap_count for cut in brief.cuts)
        for gap_count in range(1, (brief.max_gaps or 4) + 1)
    }
    index_lines = [
        "# RH frontier chains",
        "",
        "Automatically generated from compiled Lean corpus snapshot and semantic interface witnesses.",
        "",
        f"- Total bounded minimal cuts: **{brief.total_cuts}**",
        f"- Reports written: **{len(selected)}**",
        f"- Search bound: `max_gaps={brief.max_gaps or 4}`",
        f"- Corpus commit: `{brief.commit or 'not recorded'}`",
        "- Cuts by gap count: "
        + ", ".join(f"**{gap_count}**: {count}" for gap_count, count in counts.items()),
        "",
    ]
    for gap_count in range(1, (brief.max_gaps or 4) + 1):
        index_lines.extend(
            [
                f"## {gap_count}-gap chains",
                "",
                "| Rank | Gaps | Checked reductions | Open interfaces | Report |",
                "|---:|---:|---:|---|---|",
                *[
                    row
                    for row, cut in zip(index_rows, selected)
                    if len(cut.nodes) == gap_count
                ],
                "",
            ]
        )
    index_path.write_text("\n".join(index_lines), encoding="utf-8")
    return (index_path, *report_paths)
