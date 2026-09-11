from __future__ import annotations

import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_research_benchmark as benchmark


def ref(name, module="Example", line=1):
    return {"relpath": f"formal/{module}.lean", "name": name, "line": line}


def case(kind="direct", relevant=None, **extra):
    return {"id": "query", "kind": kind, "query": "paraphrased mathematical question",
            "family": "example", "split": "dev", "relevant": relevant or [ref("answer")], **extra}


def analogy(**extra):
    source, target = ref("source"), ref("target", "Other")
    return case("analogy", [source], analogy_labels=[{
        "source": source, "target": target, "source_subject": "probability",
        "target_subject": "physics", "mechanism": "sum geometric layers",
        "proof_anchors": ["tsum_geometric"], "transfer_obligations": ["prove ratio < 1"],
    }], **extra)


def run_case(c, result):
    return benchmark.evaluate([c], lambda query, mode: result, ("lexical",))["modes"]["lexical"]


class MetricTests(unittest.TestCase):
    def test_recall_is_fraction_of_positives_not_any_hit(self):
        a, b = ref("a"), ref("b", line=2)
        row = run_case(case(relevant=[a, b]), {"declarations": [a]})
        self.assertEqual(row["metrics"]["direct_recall_at20"], 0.5)
        self.assertEqual(row["metric_case_counts"]["direct_recall_at20"], 1)

    def test_rank_20_included_21_excluded(self):
        answer = ref("answer")
        noise = [ref(f"noise{i}", line=i + 2) for i in range(20)]
        for rank, expected in ((20, 1.0), (21, 0.0)):
            with self.subTest(rank=rank):
                result = {"declarations": noise[:rank - 1] + [answer]}
                self.assertEqual(run_case(case(), result)["metrics"]["direct_recall_at20"], expected)

    def test_deduplicate_before_cutoff_and_canonicalize_fixed_qualified_alias(self):
        answer = dict(ref("answer"), qualified_name="Area.answer")
        result = {"declarations": [ref("noise")] * 25 + [answer, dict(answer, name="Area.answer")]}
        row = run_case(case(relevant=[answer]), result)["cases"][0]
        self.assertEqual((row["retrieved"], row["relevant_hits"]), (2, 1))

    def test_same_name_wrong_file_or_line_does_not_match(self):
        for wrong in (ref("answer", "Wrong"), ref("answer", line=2), ref("Other.answer")):
            with self.subTest(wrong=wrong):
                self.assertEqual(run_case(case(), {"declarations": [wrong]})["metrics"]["direct_recall_at20"], 0)

    def test_candidate_ranking_is_authoritative_even_empty(self):
        for candidates, expected in (([], 0), ([ref("answer")], 1)):
            row = run_case(case(), {"declarations": [ref("answer")], "candidate_lemmas": candidates})
            self.assertEqual(row["metrics"]["direct_recall_at20"], expected)

    def test_exploration_metadata_free_text_and_model_scores_do_not_earn_credit(self):
        result = {"declarations": [{"name": "answer", "score": 1.0}],
                  "exploration": [ref("answer")], "metadata": {"target": ref("answer")},
                  "proof_ideas": ["answer", {"text": "answer", "relevance": 1.0}]}
        self.assertEqual(run_case(case(), result)["metrics"]["direct_recall_at20"], 0)

    def test_all_supported_evidence_channels_resolve_group_members(self):
        a, b, c = ref("a"), ref("b", line=2), ref("c", line=3)
        fixture = case("group", [a, b, c], premise_groups=[[a], [b], [c]])
        result = {"declarations": [a], "proof_ideas": [{"sources": [b]}],
                  "ingredient_sets": [{"members": [{"source": c}]}]}
        row = run_case(fixture, result)
        self.assertEqual(row["metrics"]["group_coverage_at20"], 1)
        self.assertEqual(row["metrics"]["group_complete_at20"], 1)

    def test_alternatives_are_or_within_groups_and_and_across_groups(self):
        a, alternate, b = ref("a"), ref("alternate", line=2), ref("b", line=3)
        fixture = case("group", [a, alternate, b], premise_groups=[[a, alternate], [b]])
        for found, coverage, complete in (([a, alternate], .5, 0), ([alternate, b], 1, 1), ([], 0, 0)):
            with self.subTest(found=found):
                metrics = run_case(fixture, {"ingredient_sets": [{"lemmas": found}]})["metrics"]
                self.assertEqual(metrics["group_coverage_at20"], coverage)
                self.assertEqual(metrics["group_complete_at20"], complete)

    def test_same_stronger_lemma_can_cover_two_explicitly_labelled_groups(self):
        a, b, combined = ref("a"), ref("b", line=2), ref("combined", line=3)
        fixture = case("group", [a, b, combined], premise_groups=[[a, combined], [b, combined]])
        self.assertEqual(run_case(fixture, {"candidate_lemmas": [combined]})["metrics"]["group_coverage_at20"], 1)

    def test_channels_share_one_rank_budget(self):
        noise = [ref(f"noise{i}", line=i + 2) for i in range(20)]
        fixture = analogy()
        idea_noise = [ref(f"idea{i}", "Methods", i + 2) for i in range(20)]
        result = {"declarations": noise, "source_arguments": idea_noise + fixture["relevant"]}
        self.assertEqual(run_case(fixture, result)["metrics"]["analogy_recall_at20"], 0)

    def test_full_candidate_channel_does_not_starve_raw_methods(self):
        fixture = analogy()
        result = {"candidate_lemmas": [ref(f"noise{i}", line=i + 2) for i in range(20)],
                  "source_arguments": fixture["relevant"]}
        self.assertEqual(run_case(fixture, result)["metrics"]["analogy_recall_at20"], 1)

    def test_engine_ingredient_steps_candidates_shape(self):
        a, b = ref("a"), ref("b", line=2)
        fixture = case("group", [a, b], premise_groups=[[a], [b]])
        result = {"candidate_lemmas": [], "proof_ideas": [], "ingredient_sets": [
            {"description": "proposed group", "status": "not_verified", "steps": [
                {"goal": "first", "candidate_ids": ["a"], "candidates": [dict(a, id="a")],
                 "obligations": ["unproved transfer"], "status": "proposed"},
                {"goal": "second", "candidate_ids": ["b"], "candidates": [dict(b, id="b")],
                 "obligations": [], "status": "proposed"}]}]}
        self.assertEqual(run_case(fixture, result)["metrics"]["group_coverage_at20"], 1)

    def test_partial_results_retain_hits_and_are_reported_separately(self):
        result = run_case(case(), {"candidate_lemmas": [ref("answer")], "partial": True,
                                  "unfinished_stages": ["deadline"], "errors": []})
        self.assertEqual(result["metrics"]["direct_recall_at20"], 1)
        self.assertEqual(result["partial_cases"], 1)
        self.assertEqual(result["cases"][0]["unfinished_stages"], ["deadline"])

    def test_completed_retrieval_preserves_index_warnings_for_acceptance(self):
        result = run_case(case(), {"candidate_lemmas": [ref("answer")], "partial": False,
            "index_warnings": ["semantic_index_incomplete"], "index_generation": 42,
            "coverage": {"generation": 41}, "semantic_coverage": {"complete": False, "ready": 99, "expected": 100}})
        row = result['cases'][0]
        self.assertEqual(row['index_warnings'], ['semantic_index_incomplete'])
        self.assertFalse(row['semantic_coverage']['complete'])
        self.assertEqual(row['environment']['corpus_generation'], 42)

    def test_silent_mode_fallback_is_a_failure(self):
        report = benchmark.evaluate([case()], lambda *_: {"mode": "lexical", "declarations": [ref("answer")]}, ("deep",))
        self.assertEqual(report["modes"]["deep"]["failed_cases"], 1)
        self.assertEqual(report["modes"]["deep"]["metrics"]["direct_recall_at20"], 0)

    def test_analogy_relevance_uses_fixed_judgments_and_reports_unjudged(self):
        fixture = analogy(excluded=[ref("bad", line=2)])
        result = {"source_arguments": [{"sources": fixture["relevant"] + fixture["excluded"]
                                  + [ref("unjudged", line=3)], "relevance": 1.0}]}
        row = run_case(fixture, result)["cases"][0]
        self.assertEqual(row["metrics"]["analogy_recall_at20"], 1)
        self.assertEqual(row["metrics"]["analogy_judged_precision_at20"], .5)
        self.assertEqual(row["metrics"]["analogy_judgment_coverage_at20"], 2 / 3)
        self.assertEqual(row["unjudged"], 1)

    def test_transfer_proposals_are_separate_from_raw_method_recall(self):
        fixture = analogy()
        proposal = dict(fixture["relevant"][0], idea_status="generated_transfer_proposal",
                        transfer="sum layer weights", evidence=["tsum_geometric"],
                        obligations=["prove summability"])
        metrics = run_case(fixture, {"proof_ideas": [proposal]})["metrics"]
        self.assertEqual(metrics["analogy_recall_at20"], 0)
        self.assertEqual(metrics["transfer_source_recall_at20"], 1)
        self.assertEqual(metrics["transfer_judged_precision_at20"], 1)
        metrics = run_case(fixture, {"source_arguments": fixture["relevant"]})["metrics"]
        self.assertEqual(metrics["analogy_recall_at20"], 1)
        self.assertIsNone(metrics["transfer_source_recall_at20"])

    def test_empty_transfer_channel_means_zero_recall_but_unvalidated_proposals_do_not_count(self):
        fixture = analogy()
        for proposals in ([], fixture["relevant"], [dict(fixture["relevant"][0], transfer="plausible")]):
            row = run_case(fixture, {"proof_ideas": proposals})["cases"][0]
            self.assertTrue(row["transfer_channel_available"])
            self.assertEqual(row["metrics"]["transfer_source_recall_at20"], 0)
            self.assertEqual(row["invalid_transfer_proposals"], len(proposals))

    def test_no_judgments_is_not_perfect_precision(self):
        row = run_case(analogy(), {"candidate_lemmas": [ref("unjudged")]})
        self.assertIsNone(row["metrics"]["analogy_judged_precision_at20"])
        self.assertEqual(row["metric_case_counts"]["analogy_judged_precision_at20"], 0)
        self.assertEqual(row["metrics"]["analogy_judgment_coverage_at20"], 0)

    def test_contrast_penalizes_wrong_hypothesis_even_when_positive_found(self):
        fixture = case("contrast", excluded=[ref("wrong", line=2)])
        metrics = run_case(fixture, {"declarations": fixture["relevant"] + fixture["excluded"]})["metrics"]
        self.assertEqual(metrics["contrast_recall_at20"], 1)
        self.assertEqual(metrics["excluded_candidate_rate_at20"], 1)

    def test_exact_preservation_conditions_on_lexical_success_and_mode_order_does_not_matter(self):
        first = case("exact", query="answer")
        second = case("exact", [ref("second")], id="second", query="second")
        def search(query, mode):
            return {"declarations": [ref(query)] if ((query == "answer") == (mode == "lexical")) else []}
        report = benchmark.evaluate([first, second], search, ("deep", "lexical"))
        deep = report["modes"]["deep"]
        self.assertEqual(deep["metrics"]["exact_recall_at20"], .5)
        self.assertEqual(deep["metrics"]["exact_preservation_at20"], 0)
        self.assertEqual(deep["metric_case_counts"]["exact_preservation_at20"], 1)
        no_baseline = benchmark.evaluate([first], search, ("deep",))["modes"]["deep"]
        self.assertIsNone(no_baseline["metrics"]["exact_preservation_at20"])

    def test_exact_top1_distinguishes_preserved_but_demoted_identifier(self):
        metrics = run_case(case("exact", query="answer"), {"declarations": [ref("noise"), ref("answer")]})["metrics"]
        self.assertEqual(metrics["exact_top1"], 0)
        self.assertEqual(metrics["exact_recall_at20"], 1)

    def test_failures_are_counted_and_cannot_inflate_aggregate(self):
        good, bad = case(), case(id="bad", query="failing query")
        def search(query, mode):
            if query == bad["query"]:
                raise TimeoutError("budget exhausted")
            return {"declarations": good["relevant"]}
        report = benchmark.evaluate([good, bad], search, ("lexical",))
        result = report["modes"]["lexical"]
        self.assertEqual(result["metrics"]["direct_recall_at20"], .5)
        self.assertEqual(result["failed_cases"], 1)
        self.assertIn("TimeoutError", result["cases"][1]["error"])
        self.assertGreaterEqual(result["budget"]["wall_seconds"], 0)
        json.dumps(report, allow_nan=False)

    def test_malformed_channels_and_error_payloads_fail_visibly(self):
        for payload in (None, {"candidate_lemmas": None}, {"error": "unavailable"}):
            with self.subTest(payload=payload):
                result = run_case(case(), payload)
                self.assertEqual(result["failed_cases"], 1)
                self.assertEqual(result["metrics"]["direct_recall_at20"], 0)

    def test_split_aggregates_remain_separate_and_callback_only_gets_query_mode(self):
        dev = case()
        test = case(relevant=[ref("heldout", "Heldout")], id="test", query="held out query",
                    split="test", family="heldout")
        calls = []
        def search(query, mode):
            calls.append((query, mode))
            return {"declarations": dev["relevant"]}
        result = benchmark.evaluate([dev, test], search, ("lexical",))["modes"]["lexical"]
        self.assertEqual(result["splits"]["dev"]["metrics"]["direct_recall_at20"], 1)
        self.assertEqual(result["splits"]["test"]["metrics"]["direct_recall_at20"], 0)
        self.assertEqual(calls, [(dev["query"], "lexical"), (test["query"], "lexical")])


class FixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(benchmark.DEFAULT_FIXTURE.read_text())

    def test_real_fixture_sources_hashes_and_mechanism_anchors(self):
        result = benchmark.validate_fixture(self.fixture)
        self.assertEqual(result["cases"], 26)
        self.assertEqual(result["source_files"], 7)
        self.assertEqual(result["labelled_declarations"], 34)
        self.assertEqual({c["kind"] for c in self.fixture["cases"]}, benchmark.KINDS)
        for split in ("dev", "test"):
            self.assertEqual({c["kind"] for c in self.fixture["cases"] if c["split"] == split}, benchmark.KINDS)
        for c in self.fixture["cases"]:
            for r in benchmark._case_refs(c):
                self.assertRegex(r["source_hash"], r"^[a-f0-9]{64}$")
                self.assertTrue(r["theorem_family"])

    def test_family_module_theorem_family_and_query_leaks_are_rejected(self):
        dev = case(relevant=[dict(ref("answer"), theorem_family="shared-lemma-family")])
        baseline = case(relevant=[ref("other", "HeldOut")], id="other", family="other", split="test", query="different question")
        variants = [dict(baseline, family=dev["family"]), dict(baseline, relevant=[ref("other")]),
                    dict(baseline, relevant=[dict(ref("other", "Sibling"), theorem_family="shared-lemma-family")]),
                    dict(baseline, query=dev["query"])]
        for test in variants:
            with self.subTest(test=test), self.assertRaisesRegex(ValueError, "leakage"):
                benchmark.validate_cases([dev, test])

    def test_negative_and_analogy_target_cannot_leak_across_splits(self):
        dev = case()
        negative = case("contrast", [ref("other", "Test")], id="test", family="test", split="test",
                        query="different question", excluded=[ref("notRelevant")])
        target = analogy(id="test", family="test", split="test", query="different question")
        target["relevant"] = [ref("source", "Test")]
        target["analogy_labels"][0]["source"] = target["relevant"][0]
        target["analogy_labels"][0]["target"] = ref("target")
        for c in (negative, target):
            with self.subTest(c=c), self.assertRaisesRegex(ValueError, "module"):
                benchmark.validate_cases([dev, c])

    def test_invalid_labels_do_not_create_vacuous_perfect_scores(self):
        examples = [case(relevant=[ref("answer"), ref("answer")]),
                    case("group", premise_groups=[]), case("group", premise_groups=[[]]),
                    case("group", premise_groups=[[ref("unlabelled")]]),
                    case("contrast"), case(excluded=[ref("answer")]),
                    case(query="answer"), case("exact", query="invented_identifier")]
        examples.append(case(relevant=[dict(ref("answer"), qualified_name="Area.answer")], query="Area.answer"))
        for c in examples:
            with self.subTest(c=c), self.assertRaises(ValueError):
                benchmark.validate_cases([c])

    def test_missing_analogy_mechanism_or_obligations_is_rejected(self):
        for field in ("mechanism", "transfer_obligations", "proof_anchors", "source_subject"):
            c = analogy()
            del c["analogy_labels"][0][field]
            with self.subTest(field=field), self.assertRaises(ValueError):
                benchmark.validate_cases([c])

    def test_source_line_name_hash_and_proof_anchor_drift_rejected(self):
        for field, value in (("line", 1), ("name", "not_a_declaration"), ("source_hash", "0" * 64)):
            fixture = copy.deepcopy(self.fixture)
            fixture["cases"][0]["relevant"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                benchmark.validate_fixture(fixture)
        fixture = copy.deepcopy(self.fixture)
        next(c for c in fixture["cases"] if c["kind"] == "analogy")["analogy_labels"][0]["proof_anchors"] = ["invented proof step"]
        with self.assertRaisesRegex(ValueError, "proof anchor"):
            benchmark.validate_fixture(fixture)

    def test_source_reference_cannot_point_into_comment_or_escape_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "formal").mkdir()
            source = b'/- outer /- nested -/\ntheorem fake : True := by trivial\n-/\n'
            (root / "formal/Example.lean").write_bytes(source)
            fake = dict(ref("fake", line=2), source_hash=hashlib.sha256(source).hexdigest())
            fixture = {"schema_version": 1, "benchmark_version": "test", "cases": [case(relevant=[fake])]}
            with self.assertRaisesRegex(ValueError, "declaration mismatch"):
                benchmark.validate_fixture(fixture, root)
        for path in ("../outside.lean", "/tmp/outside.lean", "formal/./Example.lean", "formal\\Example.lean"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                benchmark.identity(dict(ref("answer"), relpath=path))

    def test_unknown_schema_and_duplicate_ids_fail(self):
        with self.assertRaisesRegex(ValueError, "schema"):
            benchmark.validate_fixture(dict(self.fixture, schema_version=999))
        with self.assertRaisesRegex(ValueError, "duplicate case"):
            benchmark.validate_cases([case(), case()])
        for modes in ((), ("lexical", "lexical"), ("invented",)):
            with self.subTest(modes=modes), self.assertRaises(ValueError):
                benchmark.evaluate([case()], lambda *_: {}, modes)


class ReleaseGateTests(unittest.TestCase):
    def setUp(self):
        self.cases = []
        for index in range(2):
            for kind in ("direct", "exact", "analogy", "group"):
                cid = f"{kind}{index}"
                c = analogy() if kind == "analogy" else case(kind)
                if kind == "group":
                    c.update(relevant=[ref("a"), ref("b", line=2)],
                             premise_groups=[[ref("a")], [ref("b", line=2)]])
                c.update(id=cid, split="test", family=f"family{index}",
                         query="answer" if kind == "exact" else f"question {cid}")
                self.cases.append(c)
        # Exact queries may repeat within a split; distinguish them for callback selection.
        self.cases[5].update(query="answer1", relevant=[ref("answer1")])
        by_query = {c["query"]: c for c in self.cases}

        def search(query, run):
            c = by_query[query]
            config = benchmark.RUN_CONFIGS[run]
            found = []
            if c["kind"] == "exact" or (c["kind"] == "direct" and run != "lexical"):
                found = c["relevant"]
            elif c["kind"] == "group":
                found = c["relevant"] if run == "deep" else c["relevant"][:1]
            result = dict(config, candidate_lemmas=found, source_arguments=[], proof_ideas=[],
                          ingredient_sets=[], partial=False, query_trace=[{"round": 1, "query": query}],
                          engine_version="test-engine", coverage={"generation": 7},
                          runtime={"fingerprints": {"embedding": "e", "reranking": "r", "generation": "g"}})
            if run == "deep":
                result["query_trace"].append({"round": 2, "query": "expanded " + query})
            if c["kind"] == "analogy" and run in ("hybrid", "deep-once", "deep"):
                result["source_arguments"] = c["relevant"]
            return result

        self.report = benchmark.evaluate(self.cases, search, tuple(benchmark.RUN_CONFIGS))
        # Unit evidence exercises gate arithmetic; this is not a real corpus measurement.
        self.report.update(source_validation="passed", query_semantics="AND")

    def gates(self, report=None):
        return benchmark.release_gates(self.report if report is None else report, self.cases)

    def replace_ranking(self, run, c, found):
        row = next(r for r in self.report["modes"][run]["cases"] if r["id"] == c["id"])
        row.update(benchmark._score(c, {"candidate_lemmas": found}))

    def test_only_complete_paired_measurements_pass_and_json_roundtrip_preserves_result(self):
        gates = self.gates(json.loads(json.dumps(self.report)))
        self.assertTrue(gates["passed"], gates)
        self.assertTrue(all(c["passed"] for c in gates["checks"].values()))
        self.assertEqual(gates["checks"]["group_iteration_improvement"]["delta"], .5)
        self.assertNotIn("accepted", gates)

    def test_every_missing_heldout_case_or_run_blocks_acceptance(self):
        for run in benchmark.RUN_CONFIGS:
            missing_run = copy.deepcopy(self.report)
            del missing_run["modes"][run]
            self.assertFalse(self.gates(missing_run)["passed"])
            for index in range(len(self.cases)):
                partial = copy.deepcopy(self.report)
                del partial["modes"][run]["cases"][index]
                with self.subTest(run=run, index=index):
                    self.assertFalse(self.gates(partial)["passed"])

    def test_aggregate_only_and_duplicate_evidence_cannot_pass(self):
        report = copy.deepcopy(self.report)
        for result in report["modes"].values():
            result["cases"] = []
            result["metrics"] = {"direct_recall_at20": 1, "exact_preservation_at20": 1}
        self.assertFalse(self.gates(report)["passed"])
        self.report["modes"]["deep"]["cases"].append(self.report["modes"]["deep"]["cases"][0])
        self.assertFalse(self.gates()["passed"])

    def test_empty_manifest_default_manifest_or_dev_only_cannot_autoaccept_custom_measurements(self):
        self.assertFalse(benchmark.release_gates(self.report, [])["passed"])
        self.assertFalse(benchmark.release_gates(self.report)["passed"])
        dev = [dict(c, split="dev") for c in self.cases]
        self.assertFalse(benchmark.release_gates(self.report, dev)["passed"])

    def test_failed_partial_unmeasured_or_mislabeled_runs_fail_closed(self):
        for field, value in (("partial", True), ("error", "timeout"), ("errors", ["failure"]),
                             ("wall_seconds", float("nan")), ("case_fingerprint", "tampered"),
                             ("unfinished_stages", ["models_unavailable"]),
                             ("index_warnings", ["semantic_index_incomplete"]), ("metrics", None)):
            report = copy.deepcopy(self.report)
            report["modes"]["deep"]["cases"][0][field] = value
            with self.subTest(field=field):
                self.assertFalse(self.gates(report)["passed"])
        for field, value in (("executed", False), ("source_validation", None), ("query_semantics", "OR (--any)")):
            with self.subTest(field=field):
                self.assertFalse(self.gates(dict(self.report, **{field: value}))["passed"])

    def test_wrong_or_missing_ablation_controls_and_environment_changes_block(self):
        for field, value in (("retrieval_config", {}), ("query_trace", []),
                             ("environment", {}), ("environment", {"engine_version": "other", "corpus_generation": 8,
                                                                  "runtime_fingerprints": {"model": "changed"}})):
            report = copy.deepcopy(self.report)
            report["modes"]["hybrid"]["cases"][0][field] = value
            with self.subTest(field=field):
                self.assertFalse(self.gates(report)["passed"])
        self.report["modes"]["hybrid-statements"]["cases"][0]["channel_counts"]["source_arguments"] = 1
        self.assertFalse(self.gates()["passed"])
        self.report["modes"]["hybrid-statements"]["cases"][0]["channel_counts"] = None
        self.assertFalse(self.gates()["passed"])

    def test_no_strict_direct_improvement_cannot_pass(self):
        for c in self.cases:
            if c["kind"] == "direct":
                self.replace_ranking("deep", c, [])
        self.assertFalse(self.gates()["checks"]["direct_recall_improvement"]["passed"])
        self.assertFalse(self.gates()["passed"])

    def test_method_gain_cannot_be_substituted_by_generated_proposal_or_aggregate_gain(self):
        for c in self.cases:
            if c["kind"] == "analogy":
                self.replace_ranking("hybrid", c, [])
        self.report["modes"]["hybrid"]["metrics"]["analogy_recall_at20"] = 1
        self.assertFalse(self.gates()["checks"]["method_analogy_improvement"]["passed"])

    def test_iteration_gain_requires_actual_later_round_and_matching_one_round_control(self):
        for row in self.report["modes"]["deep"]["cases"]:
            row["query_trace"] = row["query_trace"][:1]
        self.assertFalse(self.gates()["checks"]["group_iteration_improvement"]["passed"])
        for c in self.cases:
            if c["kind"] == "group":
                self.replace_ranking("deep-once", c, c["relevant"])
        self.assertFalse(self.gates()["checks"]["group_iteration_improvement"]["passed"])

    def test_exact_preservation_is_per_case_and_requires_nonempty_lexical_success(self):
        exact = [c for c in self.cases if c["kind"] == "exact"]
        self.replace_ranking("deep", exact[0], [])
        self.assertFalse(self.gates()["checks"]["exact_preservation"]["passed"])
        for c in exact:
            self.replace_ranking("lexical", c, [])
        self.assertEqual(self.gates()["checks"]["exact_preservation"]["lexical_hits"], 0)
        self.assertFalse(self.gates()["passed"])

    def test_tampered_case_metric_without_corresponding_source_hit_is_rejected(self):
        self.report["modes"]["lexical"]["cases"][0]["metrics"]["direct_recall_at20"] = 1
        self.assertFalse(self.gates()["passed"])


class CLITests(unittest.TestCase):
    def invoke(self, *args):
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = benchmark.main(list(args))
        return status, stdout.getvalue(), stderr.getvalue()

    def test_default_only_validates_and_never_calls_search_or_subprocess(self):
        with patch.object(benchmark, "evaluate", side_effect=AssertionError("expensive evaluation")), \
             patch.object(benchmark.subprocess, "run", side_effect=AssertionError("subprocess")):
            code, output, error = self.invoke()
        self.assertEqual((code, error), (0, ""))
        report = json.loads(output)
        self.assertFalse(report["executed"])
        self.assertEqual(report["selected_cases"], 13)

    def test_explicit_run_filters_cases_and_reports_failures_with_nonzero_exit(self):
        with patch.object(benchmark.SubprocessSearch, "__call__", side_effect=RuntimeError("mode unavailable")) as search:
            code, output, _ = self.invoke("--run", "--modes", "deep", "--split", "test", "--case", "word-identifier")
        self.assertEqual(search.call_args.args, ("hasSum_wordPrior", "deep"))
        self.assertEqual(code, 1)
        self.assertEqual(json.loads(output)["modes"]["deep"]["failed_cases"], 1)

    def test_subprocess_adapter_preserves_query_and_and_semantics(self):
        query = '"mass loss" $(touch never)'
        result = subprocess.CompletedProcess([], 0, '{"declarations": []}', '')
        with patch.object(benchmark.subprocess, "run", return_value=result) as run:
            benchmark.SubprocessSearch()(query, "hybrid")
        args, kwargs = run.call_args
        self.assertIn(query, args[0])
        self.assertIn("--no-refresh", args[0])
        self.assertIn("--json", args[0])
        self.assertNotIn("--any", args[0])
        self.assertFalse(kwargs.get("shell", False))
        self.assertEqual(kwargs["env"]["HF_HUB_OFFLINE"], "1")
        with patch.object(benchmark.subprocess, "run", return_value=result) as run:
            benchmark.SubprocessSearch(any_terms=True)(query, "lexical")
        self.assertIn("--any", run.call_args.args[0])

    def test_subprocess_timeout_bad_json_and_exit_are_errors_not_empty_hits(self):
        for outcome in (subprocess.TimeoutExpired("research", 1),
                        subprocess.CompletedProcess([], 0, 'not json', ''),
                        subprocess.CompletedProcess([], 2, '', 'unrecognized --mode')):
            with self.subTest(outcome=outcome):
                kwargs = {"side_effect": outcome} if isinstance(outcome, Exception) else {"return_value": outcome}
                with patch.object(benchmark.subprocess, "run", **kwargs), self.assertRaises(Exception):
                    benchmark.SubprocessSearch()("query", "deep")

    def test_ablation_adapter_uses_real_controls_without_posthoc_filtering(self):
        payload = subprocess.CompletedProcess([], 0, '{"source_arguments": [{"name": "unfiltered"}]}', '')
        for run, config in benchmark.RUN_CONFIGS.items():
            with self.subTest(run=run), patch.object(benchmark.subprocess, "run", return_value=payload) as execute:
                result = benchmark.SubprocessSearch()("query", run)
            command = execute.call_args.args[0]
            self.assertEqual(command[command.index("--mode") + 1], config["mode"])
            if run == "lexical":
                self.assertNotIn("--retrieval-views", command)
                self.assertNotIn("--max-rounds", command)
            else:
                self.assertEqual(command[command.index("--retrieval-views") + 1], config["retrieval_views"])
            if run == "deep-once":
                self.assertEqual(int(command[command.index("--max-rounds") + 1]), config["max_rounds"])
            else:
                self.assertNotIn("--max-rounds", command)
            self.assertEqual(result["source_arguments"], [{"name": "unfiltered"}])

    def test_four_way_operator_aliases_and_top_level_view_echo(self):
        def search(query, run):
            config = benchmark.RUN_CONFIGS[run]
            return {"mode": config["mode"], "retrieval_views": config.get("retrieval_views", "all"),
                    "declarations": [], "candidate_lemmas": [], "source_arguments": [], "proof_ideas": []}
        with patch.object(benchmark.SubprocessSearch, "__call__", side_effect=search) as called:
            code, output, error = self.invoke("--run", "--split", "test", "--case", "word-identifier",
                                              "--modes", "lexical", "hybrid-statements", "hybrid-all", "deep-all")
        self.assertEqual((code, error), (0, ""))
        self.assertEqual([call.args[1] for call in called.call_args_list],
                         ["lexical", "hybrid-statements", "hybrid", "deep"])
        report = json.loads(output)
        self.assertEqual(report["modes"]["hybrid-statements"]["cases"][0]["retrieval_config"],
                         {"mode": "hybrid", "retrieval_views": "statements"})
        self.assertNotIn("max_rounds", report["modes"]["deep"]["cases"][0]["retrieval_config"])
        self.assertFalse(report["release_gates"]["passed"])

    def test_alias_cannot_duplicate_control_measurements(self):
        with self.assertRaisesRegex(ValueError, "distinct"):
            benchmark.evaluate([case()], lambda *_: {}, ("hybrid", "hybrid-all"))

    def test_deep_all_subprocess_uses_only_current_cli_controls(self):
        payload = subprocess.CompletedProcess([], 0, '{"mode":"deep","retrieval_views":"all"}', '')
        with patch.object(benchmark.subprocess, "run", return_value=payload) as execute:
            result = benchmark.SubprocessSearch()("query", "deep-all")
        command = execute.call_args.args[0]
        self.assertEqual(command[command.index("--mode") + 1], "deep")
        self.assertEqual(command[command.index("--retrieval-views") + 1], "all")
        self.assertNotIn("--max-rounds", command)
        self.assertEqual(result["retrieval_views"], "all")

    def test_invalid_timeouts_cannot_launch_unbounded_search(self):
        for timeout in (0, -1, float("inf"), float("nan")):
            with self.subTest(timeout=timeout), self.assertRaises(ValueError):
                benchmark.SubprocessSearch(timeout=timeout)

    def test_unknown_or_empty_selection_is_actionable_error(self):
        for args in (("--case", "typo"), ("--case", "word-identifier", "--split", "dev")):
            code, output, error = self.invoke(*args)
            self.assertEqual(code, 2)
            self.assertFalse(output)
            self.assertTrue(error)


if __name__ == "__main__":
    unittest.main()
