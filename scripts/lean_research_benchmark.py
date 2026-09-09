#!/usr/bin/env python3
"""Fixed-label retrieval benchmark; no Lean, model imports, or search on import.

Run without --run to validate fixtures only. An explicit --run invokes
formal_tools.py research --mode MODE --json --no-refresh once per case/mode.
Example: python3 scripts/lean_research_benchmark.py --run --modes lexical --split dev

Identity is (repository-relative path, declaration name, one-based line).
Only explicitly labelled qualified_name aliases are accepted. candidate_lemmas,
when present, is the primary ranking; otherwise legacy declarations is used.
Direct/exact/broad/contrast metrics use its first 20 distinct identities.
Analogy retrieval round-robins primary and raw source_arguments rankings.
Generated proof_ideas are scored separately as transfer proposals; they never
inflate raw method recall. Groups also include proof ideas and ingredient sets.
Each ranking has a shared 20-identity budget. Exploration,
free text, model relevance scores, and target/metadata fields never earn credit.
Nested evidence may use source/declaration/lemma or sources/evidence/references/
members/lemmas/ingredients/premises or steps[].candidates. Server order within
each channel is preserved; fusion prevents one full channel starving the others.

Recall means fraction of fixed positives recovered, macro-averaged over cases.
Groups are AND across groups, OR within a group. Group coverage measures retrieved
ingredients, not a proved composition or satisfaction of transfer obligations.
Analogy precision is over judged positives/negatives only; judgment coverage and
unjudged counts accompany it. None means no applicable denominator, never success.
Exact preservation conditions on lexical top-20 hits of the SAME exact cases.
Errors remain zero-recall cases, with explicit error and timing records.

Module/family holdout concerns benchmark labels, not removal from searchable
corpus or isolation of transitive imports. These curated labels are incomplete;
neither broad recall nor analogy judgments constitute a whole-corpus audit.

Release controls: lexical; hybrid-statements (hybrid, statements, one round);
hybrid (all views, one round); deep-once (all views, one round); deep (all views,
three rounds). Nonlexical subprocess runs require --retrieval-views; deep-once
also requires --max-rounds 1. Ordinary deep uses the engine's default round limit.
hybrid-all/deep-all are operator aliases for hybrid/deep. Unsupported controls fail;
they are never emulated by
discarding already-retrieved method results. Results must echo retrieval_views
and max_rounds (top-level or retrieval_config/options), provide query_trace,
engine_version, coverage.generation and runtime.fingerprints for release gates.
Gates require every held-out case in all controls, matched source labels and
environment, no errors/partial runs, strictly positive paired mean improvements,
and preservation of every lexical exact hit. Generated proposal relevance does
not prove the transfer. Gates never write release.json or change default mode.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import zip_longest
import math
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time
from collections.abc import Callable, Iterator

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FIXTURE = ROOT / "scripts/tests/fixtures/research_benchmark.json"
SCHEMA_VERSION = 1
EVALUATOR_VERSION = 2
KINDS = {"direct", "exact", "analogy", "group", "broad", "contrast"}
MODES = ("lexical", "hybrid", "deep")
RUN_CONFIGS = {
    "lexical": {"mode": "lexical"},
    "hybrid-statements": {"mode": "hybrid", "retrieval_views": "statements", "max_rounds": 1},
    "hybrid": {"mode": "hybrid", "retrieval_views": "all", "max_rounds": 1},
    "deep-once": {"mode": "deep", "retrieval_views": "all", "max_rounds": 1},
    "deep": {"mode": "deep", "retrieval_views": "all", "max_rounds": 3},
}
RUN_ALIASES = {"hybrid-all": "hybrid", "deep-all": "deep"}
EVIDENCE_KEYS = ("source", "declaration", "lemma", "sources", "evidence",
                 "references", "members", "lemmas", "ingredients", "premises",
                 "steps", "candidates")
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([\w'.«»]+)"
)
Identity = tuple[str, str, int]


def identity(ref: dict) -> Identity:
    """Reject ambiguous or path-traversing provenance rather than fuzzy-match it."""
    if not isinstance(ref, dict):
        raise ValueError("source reference must be an object")
    path, name, line = (ref.get(k) for k in ("relpath", "name", "line"))
    if not isinstance(path, str) or not path or "\\" in path:
        raise ValueError("invalid relpath")
    p = PurePosixPath(path)
    if p.is_absolute() or ".." in p.parts or str(p) != path or p.suffix != ".lean":
        raise ValueError("relpath must be a canonical relative Lean path")
    if not isinstance(name, str) or not name.strip() or type(line) is not int or line < 1:
        raise ValueError("source requires declaration name and positive one-based line")
    return path, name, line


def _case_refs(case: dict) -> Iterator[dict]:
    yield from case["relevant"]
    yield from case.get("excluded", [])
    for group in case.get("premise_groups", []):
        yield from group
    for label in case.get("analogy_labels", []):
        yield label["source"]
        yield label["target"]


def validate_cases(cases: list[dict]) -> None:
    """Validate labels and prevent split leakage even through negative/target refs."""
    if not isinstance(cases, list) or not cases:
        raise ValueError("cases must be a nonempty list")
    ids: set[str] = set()
    owners: dict[tuple[str, str], str] = {}
    for case in cases:
        for field in ("id", "kind", "query", "family", "split"):
            if not isinstance(case.get(field), str) or not case[field].strip():
                raise ValueError(f"missing/non-string {field}")
        if case["id"] in ids:
            raise ValueError(f"duplicate case id: {case['id']}")
        ids.add(case["id"])
        if case["kind"] not in KINDS or case["split"] not in {"dev", "test"}:
            raise ValueError(f"invalid kind/split: {case['id']}")
        if not isinstance(case.get("relevant"), list) or not case["relevant"]:
            raise ValueError(f"empty relevant labels: {case['id']}")
        positives = {identity(r) for r in case["relevant"]}
        negatives = {identity(r) for r in case.get("excluded", [])}
        if len(positives) != len(case["relevant"]) or positives & negatives:
            raise ValueError(f"duplicate/conflicting labels: {case['id']}")
        groups = case.get("premise_groups", [])
        if case["kind"] == "group" and not groups:
            raise ValueError("group cases require premise_groups")
        for group in groups:
            if not isinstance(group, list) or not group:
                raise ValueError("empty/invalid premise group")
            if not {identity(r) for r in group} <= positives:
                raise ValueError("premise alternatives must be relevant labels")
        if case["kind"] == "contrast" and not negatives:
            raise ValueError("contrast requires excluded labels")
        if case["kind"] == "direct":
            tokens = set(re.findall(r"[\w'.«»]+", case["query"].casefold()))
            if any(n.casefold() in tokens for r in case["relevant"]
                   for n in (r["name"], r.get("qualified_name", r["name"]))):
                raise ValueError("direct query leaks a declaration name")
        if case["kind"] == "exact" and case["query"] not in {
            n for r in case["relevant"] for n in (r["name"], r.get("qualified_name"))
        }:
            raise ValueError("exact query must be a labelled identifier")
        if case["kind"] == "analogy":
            labels = case.get("analogy_labels", [])
            if {identity(x["source"]) for x in labels} != positives:
                raise ValueError("every analogy positive needs a fixed source label")
            for label in labels:
                if not label.get("mechanism") or not label.get("transfer_obligations"):
                    raise ValueError("analogy requires mechanism and transfer obligations")
                for field in ("source_subject", "target_subject"):
                    if not label.get(field):
                        raise ValueError("analogy requires both subjects")
                if label["source_subject"] == label["target_subject"]:
                    raise ValueError("analogy subjects must differ")
                if not label.get("proof_anchors"):
                    raise ValueError("analogy requires proof anchors")
        keys = [("family", case["family"]), ("query", case["query"].casefold())]
        keys += [("module", identity(r)[0]) for r in _case_refs(case)]
        # Explicit theorem-family prefixes cover sibling modules with shared names.
        keys += [("theorem_family", r["theorem_family"]) for r in _case_refs(case)
                 if r.get("theorem_family")]
        for key in keys:
            if key in owners and owners[key] != case["split"]:
                raise ValueError(f"split leakage through {key[0]}: {key[1]}")
            owners[key] = case["split"]


def _without_comments(text: str) -> str:
    """Preserve line numbers while masking Lean nested comments and strings."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if not string and pair == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and not string and pair == "--":
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            out.append(" " * (end - i))
            i = end
        elif not depth and string and char == "\\":
            out.append("  ")
            i += 2
        else:
            if not depth and char == '"':
                string = not string
                out.append(" ")
            else:
                out.append("\n" if char == "\n" else " " if depth or string else char)
            i += 1
    return "".join(out)


def validate_fixture(fixture: dict, root: Path = ROOT) -> dict:
    """Read/hash labelled sources only; never invoke Lean or update search caches."""
    if fixture.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("unsupported benchmark schema_version")
    if not isinstance(fixture.get("benchmark_version"), str) or not fixture["benchmark_version"]:
        raise ValueError("missing benchmark_version")
    cases = fixture.get("cases")
    validate_cases(cases)
    files: dict[str, tuple[str, list[str], list[str]]] = {}
    checked: set[Identity] = set()
    for case in cases:
        for ref in _case_refs(case):
            path, name, line = identity(ref)
            if path not in files:
                resolved = (root / path).resolve()
                if not resolved.is_relative_to(root.resolve()):
                    raise ValueError(f"source escapes root: {path}")
                data = resolved.read_bytes()
                text = data.decode("utf-8")
                files[path] = (hashlib.sha256(data).hexdigest(), text.splitlines(),
                               _without_comments(text).splitlines())
            digest, raw, code = files[path]
            if ref.get("source_hash") and ref["source_hash"] != digest:
                raise ValueError(f"source hash drift: {path}")
            match = DECLARATION.match(code[line - 1]) if line <= len(code) else None
            if match is None or match[1] != name:
                raise ValueError(f"declaration mismatch: {path}:{line}: {name}")
            checked.add(identity(ref))
        for label in case.get("analogy_labels", []):
            ref = label["source"]
            _, raw, code = files[ref["relpath"]]
            start = ref["line"] - 1
            end = next((i for i in range(start + 1, len(code))
                        if DECLARATION.match(code[i])), len(code))
            body = "\n".join(code[start:end])
            if ":=" not in body:
                raise ValueError("analogy source has no visible proof body")
            proof = body.split(":=", 1)[1]
            if any(anchor not in proof for anchor in label["proof_anchors"]):
                raise ValueError(f"missing proof anchor: {case['id']}")
    return {"cases": len(cases), "labelled_declarations": len(checked),
            "source_files": len(files), "source_validation": "passed"}


def _evidence(value: object) -> Iterator[dict]:
    if isinstance(value, list):
        for item in value:
            yield from _evidence(item)
    elif isinstance(value, dict):
        if any(k in value for k in ("relpath", "line")):
            yield value
        for key in EVIDENCE_KEYS:
            if key in value:
                yield from _evidence(value[key])


def ranked_identities(result: dict, case: dict, *, extended: bool,
                      channels: tuple[str, ...] | None = None) -> list[Identity]:
    """Normalize evidence, deduplicate before truncation; no free-text matches."""
    if not isinstance(result, dict):
        raise ValueError("search result must be an object")
    if channels is None:
        channels = ("primary",)
        if extended:
            channels += ("source_arguments",)
            if case["kind"] == "group":
                channels += ("proof_ideas", "ingredient_sets")
    streams = [result.get("candidate_lemmas", result.get("declarations", []))
               if channel == "primary" else result.get(channel, []) for channel in channels]
    if any(not isinstance(s, list) for s in streams):
        raise ValueError("retrieval channels must be lists")
    aliases = {identity(r): identity(r) for r in _case_refs(case)}
    for ref in _case_refs(case):
        if ref.get("qualified_name"):
            aliases[(ref["relpath"], ref["qualified_name"], ref["line"])] = identity(ref)
    ranked, seen = [], set()
    fused = (ref for batch in zip_longest(*(_evidence(s) for s in streams))
             for ref in batch if ref is not None)
    for ref in fused:
        try:
            key = identity(ref)
        except ValueError:
            continue
        key = aliases.get(key, key)
        if key not in seen:
            seen.add(key)
            ranked.append(key)
            if len(ranked) == 20:
                break
    return ranked


def _score(case: dict, result: dict) -> dict:
    extended = case["kind"] in {"analogy", "group"}
    ranked = ranked_identities(result, case, extended=extended)
    found = set(ranked)
    relevant = {identity(r) for r in case["relevant"]}
    excluded = {identity(r) for r in case.get("excluded", [])}
    hits, wrong = len(found & relevant), len(found & excluded)
    metrics = {f"{case['kind']}_recall_at20": hits / len(relevant)}
    details = {}
    if case["kind"] == "exact":
        metrics["exact_top1"] = float(bool(ranked and ranked[0] in relevant))
    if case["kind"] == "analogy":
        metrics["analogy_judged_precision_at20"] = hits / (hits + wrong) if hits + wrong else None
        metrics["analogy_judgment_coverage_at20"] = (hits + wrong) / len(found) if found else None
        proposals = result.get("proof_ideas")
        if proposals is not None and not isinstance(proposals, list):
            raise ValueError("proof_ideas must be a list")
        valid = [p for p in proposals or [] if isinstance(p, dict)
                 and p.get("idea_status") == "generated_transfer_proposal"
                 and isinstance(p.get("transfer"), str) and p["transfer"].strip()
                 and all(isinstance(p.get(k), list) and p[k]
                         and all(isinstance(s, str) and s.strip() for s in p[k])
                         for k in ("evidence", "obligations"))]
        transfer = set(ranked_identities({"proof_ideas": valid}, case, extended=False,
                                        channels=("proof_ideas",)))
        good, bad = len(transfer & relevant), len(transfer & excluded)
        metrics["transfer_source_recall_at20"] = good / len(relevant) if proposals is not None else None
        metrics["transfer_judged_precision_at20"] = good / (good + bad) if good + bad else None
        metrics["transfer_judgment_coverage_at20"] = (good + bad) / len(transfer) if transfer else None
        details = {"transfer_channel_available": proposals is not None,
                   "invalid_transfer_proposals": len(proposals or []) - len(valid),
                   "transfer_identities": sorted(transfer)}
    if case.get("premise_groups"):
        covered = sum(bool(found & {identity(r) for r in g}) for g in case["premise_groups"])
        metrics["group_coverage_at20"] = covered / len(case["premise_groups"])
        metrics["group_complete_at20"] = float(covered == len(case["premise_groups"]))
    if excluded:
        metrics["excluded_candidate_rate_at20"] = wrong / len(excluded)
    return {"metrics": metrics, "retrieved": len(found), "relevant_hits": hits,
            "excluded_hits": wrong, "unjudged": len(found - relevant - excluded),
            "retrieved_identities": ranked, **details}


def _aggregate(rows: list[dict]) -> dict:
    names = sorted({key for row in rows for key in row["metrics"]})
    values = {key: [row["metrics"][key] for row in rows
                    if row["metrics"].get(key) is not None] for key in names}
    timings = sorted(row["wall_seconds"] for row in rows)
    return {"case_count": len(rows), "failed_cases": sum("error" in row for row in rows),
            "partial_cases": sum(bool(row.get("partial")) for row in rows),
            "metrics": {k: sum(v) / len(v) if v else None for k, v in values.items()},
            "metric_case_counts": {k: len(v) for k, v in values.items()},
            "budget": {"wall_seconds": sum(timings),
                       "max_query_seconds": max(timings, default=None),
                       "p50_query_seconds": timings[(len(timings) - 1) // 2] if timings else None,
                       "p95_query_seconds": timings[math.ceil(.95 * len(timings)) - 1] if timings else None,
                       "over_120s_cases": sum(t > 120 for t in timings)}}


def case_fingerprint(case: dict) -> str:
    return hashlib.sha256(json.dumps(case, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def release_gates(report: dict, expected_cases: list[dict] | None = None) -> dict:
    """Fail closed using paired per-case evidence, never aggregate scores alone.

    expected_cases must be the FULL versioned fixture, not the executed subset.
    Omission uses the bundled fixture. Two held-out cases per gate kind and two
    held-out families are minimum safeguards, not statistical significance.
    Reports are local measurement records, not cryptographic attestations.
    """
    check_names = ("direct_recall_improvement", "exact_preservation",
                   "method_analogy_improvement", "group_iteration_improvement")
    checks = {name: {"passed": False, "reason": "measurement prerequisites missing"}
              for name in check_names}
    blocked = []
    if expected_cases is None:
        expected_cases = json.loads(DEFAULT_FIXTURE.read_text())["cases"]
    try:
        validate_cases(expected_cases)
    except (ValueError, TypeError, KeyError, AttributeError) as error:
        return {"passed": False, "checks": checks,
                "blocking_reasons": [f"invalid full fixture manifest: {error}"],
                "heldout_case_count": 0, "required_runs": list(RUN_CONFIGS)}
    if not isinstance(report, dict):
        report = {}
    heldout = {c["id"]: c for c in expected_cases if c["split"] == "test"}
    by_kind = {kind: [c for c in heldout.values() if c["kind"] == kind]
               for kind in ("direct", "exact", "analogy", "group")}
    for kind, cases in by_kind.items():
        if len(cases) < 2:
            blocked.append(f"need at least two held-out {kind} cases")
    if len({c["family"] for c in heldout.values()}) < 2:
        blocked.append("need at least two held-out families")
    if report.get("executed") is not True or report.get("evaluator_version") != EVALUATOR_VERSION:
        blocked.append("no compatible executed measurement")
    if report.get("source_validation") != "passed":
        blocked.append("source validation missing")
    if report.get("query_semantics") != "AND":
        blocked.append("release controls require recorded AND semantics")
    runs = report.get("modes", {})
    paired = {}
    environments = set()
    for run, required in RUN_CONFIGS.items():
        value = runs.get(run, {}) if isinstance(runs, dict) else {}
        rows = value.get("cases", []) if isinstance(value, dict) else []
        if not isinstance(rows, list):
            rows = []
        index = {}
        for row in rows:
            if not isinstance(row, dict) or row.get("id") not in heldout:
                continue
            cid = row["id"]
            if cid in index:
                blocked.append(f"{run}/{cid}: duplicate measurement")
            index[cid] = row
        paired[run] = index
        missing = set(heldout) - set(index)
        if missing:
            blocked.append(f"{run}: missing held-out cases: {', '.join(sorted(missing))}")
        for cid, row in index.items():
            prefix = f"{run}/{cid}: "
            case = heldout[cid]
            if (row.get("case_fingerprint") != case_fingerprint(case)
                    or any(row.get(k) != case[k] for k in ("kind", "split", "family"))):
                blocked.append(prefix + "case labels/query differ from fixture")
            if row.get("error") or row.get("partial") or row.get("errors") or row.get("unfinished_stages"):
                blocked.append(prefix + "failed or partial measurement")
            wall = row.get("wall_seconds")
            if type(wall) not in (int, float) or not math.isfinite(wall) or wall < 0:
                blocked.append(prefix + "missing/invalid measured duration")
            try:
                found = row["retrieved_identities"]
                if not isinstance(found, list) or len(found) > 20:
                    raise ValueError()
                identities = {identity(dict(zip(("relpath", "name", "line"), item)))
                              for item in found if isinstance(item, (list, tuple)) and len(item) == 3}
                if len(identities) != len(found):
                    raise ValueError()
                # Recompute scores from fixed labels instead of trusting reported averages.
                recalculated = _score(case, {"candidate_lemmas": [dict(zip(
                    ("relpath", "name", "line"), item)) for item in found]})["metrics"]
                for metric in (f"{case['kind']}_recall_at20", "group_coverage_at20"):
                    if metric in recalculated:
                        measured = row.get("metrics", {}).get(metric)
                        if type(measured) not in (int, float) or measured != recalculated[metric]:
                            raise ValueError()
            except (KeyError, TypeError, ValueError, AttributeError):
                blocked.append(prefix + "missing/inconsistent ranked evidence")
            if run == "lexical":
                continue
            config = row.get("retrieval_config", {})
            if config != required:
                blocked.append(prefix + "retrieval control not confirmed by engine")
            trace = row.get("query_trace", [])
            if (not isinstance(trace, list) or not trace or any(
                    not isinstance(t, dict) or type(t.get("round")) is not int
                    or not 1 <= t["round"] <= required["max_rounds"]
                    or not isinstance(t.get("query"), str) or not t["query"].strip() for t in trace)):
                blocked.append(prefix + "missing/invalid round trace")
            elif trace[0]["round"] != 1 or trace[0]["query"] != case["query"]:
                blocked.append(prefix + "trace does not start with benchmark query")
            counts = row.get("channel_counts", {})
            if run == "hybrid-statements" and (not isinstance(counts, dict) or any(counts.get(k) != 0 for k in
                    ("source_arguments", "proof_ideas", "ingredient_sets"))):
                blocked.append(prefix + "statement-only control includes method/transfer evidence")
            env = row.get("environment", {})
            if (not isinstance(env, dict) or not env.get("engine_version") or type(env.get("corpus_generation")) is not int
                    or not env.get("runtime_fingerprints")):
                blocked.append(prefix + "missing engine/corpus/model fingerprints")
            else:
                environments.add(json.dumps(env, sort_keys=True))
    if len(environments) > 1:
        blocked.append("engine/corpus/model fingerprints differ across controls")

    def improvement(name, kind, metric, baseline, candidate):
        cases = by_kind[kind]
        before = [paired[baseline][c["id"]]["metrics"][metric] for c in cases]
        after = [paired[candidate][c["id"]]["metrics"][metric] for c in cases]
        delta = sum(b - a for a, b in zip(before, after)) / len(cases)
        checks[name] = {"passed": delta > 0, "cases": len(cases),
                        "baseline_run": baseline, "candidate_run": candidate,
                        "baseline": sum(before) / len(cases), "candidate": sum(after) / len(cases),
                        "delta": delta, "reason": "strict paired improvement" if delta > 0 else "no strict improvement"}

    if not blocked:
        improvement("direct_recall_improvement", "direct", "direct_recall_at20", "lexical", "deep")
        improvement("method_analogy_improvement", "analogy", "analogy_recall_at20", "hybrid-statements", "hybrid")
        improvement("group_iteration_improvement", "group", "group_coverage_at20", "deep-once", "deep")
        lost, baseline_hits = [], 0
        for case in by_kind["exact"]:
            relevant = {identity(r) for r in case["relevant"]}
            baseline = {tuple(r) for r in paired["lexical"][case["id"]]["retrieved_identities"]} & relevant
            baseline_hits += len(baseline)
            for run in RUN_CONFIGS.keys() - {"lexical"}:
                found = {tuple(r) for r in paired[run][case["id"]]["retrieved_identities"]}
                if baseline - found:
                    lost.append(f"{run}/{case['id']}")
        checks["exact_preservation"] = {"passed": baseline_hits > 0 and not lost,
                                        "lexical_hits": baseline_hits, "lost": sorted(lost),
                                        "reason": "all lexical hits preserved" if baseline_hits and not lost
                                        else "lost exact hits or vacuous lexical baseline"}
        group_check = checks["group_iteration_improvement"]
        improved = [c for c in by_kind["group"] if
                    paired["deep"][c["id"]]["metrics"]["group_coverage_at20"] >
                    paired["deep-once"][c["id"]]["metrics"]["group_coverage_at20"]]
        if any(not any(t["round"] > 1 for t in paired["deep"][c["id"]]["query_trace"])
               for c in improved):
            group_check.update(passed=False, reason="improved groups have no measured later round")
    return {"passed": not blocked and all(c["passed"] for c in checks.values()),
            "checks": checks, "blocking_reasons": blocked,
            "heldout_case_count": len(heldout), "required_runs": list(RUN_CONFIGS),
            "scope": "paired fixed-label retrieval gates; no significance claim or automatic release acceptance"}


def _rss_high_water() -> dict:
    try:
        import resource
        scale = 1 if sys.platform == "darwin" else 1024
        return {"evaluator_peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * scale,
                "children_peak_rss_bytes": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * scale,
                "scope": "process-lifetime high-water marks, not per-query deltas; external workers excluded"}
    except (ImportError, AttributeError):
        return {"evaluator_peak_rss_bytes": None, "children_peak_rss_bytes": None,
                "scope": "resource.getrusage unavailable"}


def evaluate(cases: list[dict], search: Callable[[str, str], dict],
             modes: tuple[str, ...] = MODES) -> dict:
    """Call search(query, run); named ablations map to RUN_CONFIGS, not new engine modes."""
    validate_cases(cases)
    modes = tuple(RUN_ALIASES.get(mode, mode) for mode in modes)
    if not modes or len(set(modes)) != len(modes) or set(modes) - set(RUN_CONFIGS):
        raise ValueError("modes must be distinct supported benchmark runs")
    results = {}
    for run in modes:
        rows = []
        requested = RUN_CONFIGS[run]
        for case in cases:
            row = {k: case[k] for k in ("id", "kind", "family", "split")}
            row["case_fingerprint"] = case_fingerprint(case)
            started = time.perf_counter()
            try:
                result = search(case["query"], run)
                if isinstance(result, dict):
                    row.update({k: result[k] for k in
                                ("partial", "unfinished_stages", "errors", "elapsed_seconds",
                                 "engine_version", "backend", "query_trace", "benchmark_command")
                                if k in result})
                    config = {**result.get("options", {}), **result.get("retrieval_config", {}), **result}
                    row["retrieval_config"] = {k: config[k] for k in
                                               ("mode", "retrieval_views", "max_rounds") if k in config}
                    row["environment"] = {
                        "engine_version": result.get("engine_version"),
                        "corpus_generation": result.get("coverage", {}).get("generation"),
                        "runtime_fingerprints": result.get("runtime", {}).get("fingerprints")}
                    row["channel_counts"] = {k: len(result.get(k, [])) if isinstance(result.get(k, []), list) else None
                                             for k in ("candidate_lemmas", "source_arguments", "proof_ideas", "ingredient_sets")}
                    if result.get("error"):
                        raise ValueError(str(result["error"]))
                    if result.get("mode", requested["mode"]) != requested["mode"]:
                        raise ValueError(f"requested {requested['mode']}, received {result['mode']}")
                row.update(_score(case, result))
            except Exception as error:
                row.update(_score(case, {}))
                row["error"] = f"{type(error).__name__}: {error}"
            row["wall_seconds"] = time.perf_counter() - started
            rows.append(row)
        results[run] = {"cases": rows, "requested_config": requested.copy()}
    lexical = {r["id"]: r for r in results.get("lexical", {}).get("cases", [])}
    labels = {c["id"]: {identity(r) for r in c["relevant"]} for c in cases}
    for result in results.values():
        for row in result["cases"]:
            if row["kind"] == "exact":
                base = lexical.get(row["id"])
                baseline = set(base["retrieved_identities"]) & labels[row["id"]] if base else set()
                found = set(row["retrieved_identities"])
                row["metrics"]["exact_preservation_at20"] = (
                    len(baseline & found) / len(baseline) if baseline and "error" not in base else None)
        result.update(_aggregate(result["cases"]))
        result["splits"] = {split: _aggregate([r for r in result["cases"] if r["split"] == split])
                            for split in ("dev", "test")}
    report = {"evaluator_version": EVALUATOR_VERSION, "executed": True, "cutoff": 20, "modes": results,
              "ranking_policy": "primary top-20 for direct/exact/broad/contrast; round-robin primary "
                                "and source_arguments for analogy; groups also include proof ideas and ingredients. "
                                "Transfer proposals scored separately, each ranking capped at 20 identities.",
              "memory": _rss_high_water(),
              "limitations": "Fixed incomplete source labels; no whole-corpus audit, proof checking, "
                             "or verification of suggested transfer obligations. Timings include callback overhead."}
    report["release_gates"] = release_gates(report)
    return report


class SubprocessSearch:
    """Opt-in adapter. Unsupported modes fail visibly; never silently use lexical."""

    def __init__(self, root: Path = ROOT, timeout: float = 125, any_terms: bool = False):
        if not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        self.root, self.timeout, self.any_terms = root, timeout, any_terms

    def __call__(self, query: str, mode: str) -> dict:
        mode = RUN_ALIASES.get(mode, mode)
        config = RUN_CONFIGS[mode]
        command = [sys.executable, str(self.root / "scripts/formal_tools.py"), "research", query,
                   "--mode", config["mode"], "--json", "--no-refresh", "--limit", "20", "--explore", "0",
                   "--per-module", "2", "--budget-seconds", "120"]
        if config["mode"] != "lexical":
            command += ["--retrieval-views", config["retrieval_views"]]
            if mode == "deep-once":
                command += ["--max-rounds", str(config["max_rounds"])]
        if self.any_terms:
            command.append("--any")
        env = dict(os.environ, HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1")
        process = subprocess.run(command, cwd=self.root, env=env, capture_output=True,
                                 text=True, timeout=self.timeout, check=False)
        if process.returncode:
            raise RuntimeError(f"research exited {process.returncode}: {process.stderr.strip()[:2000]}")
        result = json.loads(process.stdout)
        if not isinstance(result, dict):
            raise ValueError("research JSON must be an object")
        result["benchmark_command"] = command
        return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run", action="store_true", help="explicitly run retrieval (potentially expensive)")
    parser.add_argument("--modes", nargs="+", choices=(*RUN_CONFIGS, *RUN_ALIASES), default=list(MODES))
    parser.add_argument("--split", choices=("dev", "test", "all"), default="dev")
    parser.add_argument("--case", action="append", default=[], dest="case_ids")
    parser.add_argument("--timeout", type=float, default=125)
    parser.add_argument("--any", action="store_true", dest="any_terms", help="explicit OR semantics; default AND")
    args = parser.parse_args(argv)
    try:
        fixture = json.loads(args.fixture.read_text(encoding="utf-8"))
        validation = validate_fixture(fixture, args.root)
        unknown = set(args.case_ids) - {c["id"] for c in fixture["cases"]}
        if unknown:
            raise ValueError(f"unknown case ids: {sorted(unknown)}")
        cases = [c for c in fixture["cases"] if (args.split == "all" or c["split"] == args.split)
                 and (not args.case_ids or c["id"] in args.case_ids)]
        if not cases:
            raise ValueError("no cases selected")
        report = {"benchmark_version": fixture["benchmark_version"], **validation,
                  "selected_cases": len(cases), "executed": args.run,
                  "query_semantics": "OR (--any)" if args.any_terms else "AND",
                  "fixture_sha256": hashlib.sha256(args.fixture.read_bytes()).hexdigest()}
        if args.run:
            report.update(evaluate(cases, SubprocessSearch(args.root, args.timeout, args.any_terms),
                                   tuple(args.modes)))
        report["release_gates"] = release_gates(report, fixture["cases"])
        print(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False))
        return int(any(m["failed_cases"] for m in report.get("modes", {}).values()))
    except (ValueError, OSError, TypeError, KeyError) as error:
        print(f"benchmark: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
