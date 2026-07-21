from __future__ import annotations

import contextlib
import io
import inspect
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import formal_tools


def write_card(pipeline: Path, stage: str, name: str, body: str) -> None:
    path = pipeline / stage / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(body).lstrip(), encoding="utf-8")


class ResearchBriefTests(unittest.TestCase):
    def test_build_brief_selects_rh_dependency_leaf(self) -> None:
        builder = getattr(formal_tools, "build_research_brief", None)
        self.assertIsNotNone(builder, "formal_tools must expose research-brief generation")

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "rh-goal.md",
                """
                # RH capstone

                - **ID:** rh-goal
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Priority:** P0
                - **Statement:** Prove the Riemann Hypothesis.
                - **Depends on:** bridge
                """,
            )
            write_card(
                pipeline,
                "1-in-progress",
                "bridge.md",
                """
                # Analytic bridge

                - **ID:** bridge
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Transfer the source estimate to the capstone.
                - **Depends on:** kernel
                """,
            )
            write_card(
                pipeline,
                "1-in-progress",
                "kernel.md",
                """
                # Kernel estimate

                - **ID:** kernel
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Establish the endpoint kernel estimate.
                """,
            )
            write_card(
                pipeline,
                "1-in-progress",
                "hurwitz.md",
                """
                # Hurwitz transform

                - **ID:** hurwitz
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Classify a Hurwitz transform.
                """,
            )

            brief = builder(root=root, area="RH", declarations=(), limit=3)

            self.assertEqual(brief.area, "rh_tower")
            self.assertEqual(tuple(node.id for node in brief.frontier), ("kernel",))
            self.assertEqual(brief.selected.id, "kernel")
            self.assertEqual(brief.selected.unblocks, ("bridge", "rh-goal"))

    def test_exact_declaration_removes_duplicate_frontier_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "duplicate.md",
                """
                # Duplicate RH characterization

                - **ID:** duplicate
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Prove `RHTower.rh_iff_tower`.
                """,
            )
            declaration = formal_tools.Declaration(
                "theorem",
                "RHTower.rh_iff_tower",
                "GaloisForLFunctions.RHTower.Core",
                "formal/GaloisForLFunctions/RHTower/Core.lean",
                41,
                "RH iff coherent ladder",
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(declaration,),
                limit=3,
            )

            self.assertEqual(brief.frontier, ())
            self.assertIsNone(brief.selected)
            self.assertEqual(len(brief.prior_work), 1)
            match = brief.prior_work[0]
            self.assertEqual(match.classification, "already_formalized")
            self.assertEqual(match.card_id, "duplicate")
            self.assertEqual(match.declaration_name, "RHTower.rh_iff_tower")
            self.assertEqual(match.relpath, declaration.relpath)
            self.assertEqual(match.line, declaration.line)

    def test_explicit_current_frontier_override_beats_generic_card(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "0-backlog",
                "generic.md",
                """
                # Generic RH route

                - **ID:** generic
                - **Stage:** 0-backlog
                - **Type:** CONJECTURE
                - **Statement:** Find a criterion equivalent to the Riemann Hypothesis.
                """,
            )
            handover = root / "docs" / "handover" / "suzuki.md"
            handover.parent.mkdir(parents=True)
            handover.write_text(
                textwrap.dedent(
                    """
                    # Suzuki RH route

                    **Last updated:** 2026-07-21

                    ## Current exact frontier

                    The honest remaining producer is now source schedule selection and
                    common-gauge parity-pair normality. RH remains open.
                    """
                ).lstrip(),
                encoding="utf-8",
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )

            self.assertEqual(brief.selected.id, "handover:suzuki:5")
            self.assertEqual(brief.selected.source_kind, "frontier_override")
            self.assertEqual(brief.selected.relpath, "docs/handover/suzuki.md")
            self.assertEqual(brief.selected.line, 5)
            self.assertIn("common-gauge parity-pair normality", brief.selected.statement)

    def test_rendered_brief_is_deterministic_and_cites_every_frontier_item(self) -> None:
        renderer = getattr(formal_tools, "render_research_brief", None)
        self.assertIsNotNone(renderer, "formal_tools must expose brief rendering")

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "producer.md",
                """
                # RH source producer

                - **ID:** producer
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Priority:** P0
                - **Statement:** Construct the Riemann Hypothesis source producer.
                """,
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )
            first = renderer(brief)
            second = renderer(brief)

            self.assertEqual(first, second)
            self.assertTrue(first.startswith("# RH Research Brief\n"))
            self.assertIn("## Selected task", first)
            self.assertIn("## Frontier", first)
            self.assertIn("## Prior-work gate", first)
            self.assertIn("## Failed routes", first)
            self.assertIn("## Diagnostics", first)
            self.assertIn(
                "docs/drafts/pipeline/1-in-progress/producer.md:7",
                first,
            )

    def test_relevant_failed_route_includes_killing_mechanism_and_survivor(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "theta-source.md",
                """
                # Theta orientation source

                - **ID:** theta-source
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Construct a theta orientation source for the Riemann Hypothesis.
                """,
            )
            write_card(
                pipeline,
                "5-failed",
                "theta-diagonal.md",
                """
                # Failed theta diagonal projection

                - **ID:** theta-diagonal
                - **Stage:** 5-failed
                - **Type:** FALSIFIED
                - **Statement:** A theta diagonal projection forces the Riemann Hypothesis orientation.

                ## No-go closure
                - **Exact killing theorem/mechanism:** The diagonal projection acts identically but loses orientation.
                - **Strongest positive survivor:** The sharp Lee-Yang cone obeys b <= 3a.
                - **New insight:** Orientation needs a non-diagonal source.
                - **Status:** Retired.
                """,
            )
            write_card(
                pipeline,
                "5-failed",
                "hurwitz-route.md",
                """
                # Failed Hurwitz route

                - **ID:** hurwitz-route
                - **Stage:** 5-failed
                - **Type:** FALSIFIED
                - **Statement:** A Hurwitz interpolation closes a recurrence.
                - **Exact killing theorem/mechanism:** The interpolation is nonunique.
                - **Strongest positive survivor:** A finite recurrence remains.
                """,
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )

            routes = getattr(brief, "failed_routes", None)
            self.assertIsNotNone(routes, "brief must expose relevant failed routes")
            self.assertEqual(len(routes), 1)
            failed = routes[0]
            self.assertEqual(failed.card_id, "theta-diagonal")
            self.assertEqual(
                failed.mechanism,
                "The diagonal projection acts identically but loses orientation.",
            )
            self.assertEqual(
                failed.positive_survivor,
                "The sharp Lee-Yang cone obeys b <= 3a.",
            )
            self.assertEqual(failed.mechanism_evidence.line, 9)
            self.assertEqual(failed.survivor_evidence.line, 10)

    def test_malformed_card_is_quarantined_and_header_stage_wins_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "0-backlog",
                "mismatch.md",
                """
                # Current RH producer

                - **ID:** mismatch
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Build the current Riemann Hypothesis producer.
                """,
            )
            write_card(
                pipeline,
                "1-in-progress",
                "legacy.md",
                """
                # Legacy continuation log

                This fragment has no structured identity or stage.
                """,
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )

            self.assertEqual(brief.selected.id, "mismatch")
            self.assertIn(
                "stage_path_mismatch docs/drafts/pipeline/0-backlog/mismatch.md:4 "
                "header=1-in-progress path=0-backlog",
                brief.diagnostics,
            )
            self.assertIn(
                "missing_required_fields docs/drafts/pipeline/1-in-progress/legacy.md:1",
                brief.diagnostics,
            )

    def test_brief_cli_rejects_unknown_area_without_scanning(self) -> None:
        self.assertIn(
            "argv",
            inspect.signature(formal_tools.main).parameters,
            "main must accept injected argv for deterministic agent and test use",
        )
        stderr = io.StringIO()
        stdout = io.StringIO()
        with (
            mock.patch.object(
                formal_tools,
                "declarations",
                side_effect=AssertionError("corpus scan must not start"),
            ),
            contextlib.redirect_stderr(stderr),
            contextlib.redirect_stdout(stdout),
        ):
            result = formal_tools.main(["brief", "--area", "wat"])

        self.assertEqual(result, 2)
        self.assertEqual(stdout.getvalue(), "")
        self.assertIn("unknown area 'wat'", stderr.getvalue())

    def test_frontier_candidate_retrieves_related_lean_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "gauge-normality.md",
                """
                # Xi common-gauge normality

                - **ID:** gauge-normality
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Construct common-gauge parity-pair normality for Xi.
                """,
            )
            related = formal_tools.Declaration(
                "theorem",
                "suzuki_commonGauge_parityPair_normality_reduction",
                "GaloisForLFunctions.RHTower.SuzukiGauge",
                "formal/GaloisForLFunctions/RHTower/SuzukiGauge.lean",
                71,
                "Common-gauge parity-pair normality reduces Xi recovery to the source estimate.",
            )
            unrelated = formal_tools.Declaration(
                "theorem",
                "add_comm",
                "Mathlib.Algebra.Group.Basic",
                "Mathlib/Algebra/Group/Basic.lean",
                10,
                "Addition is commutative.",
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(unrelated, related),
                limit=3,
            )

            self.assertEqual(brief.selected.id, "gauge-normality")
            matches = [
                match
                for match in brief.prior_work
                if match.card_id == "gauge-normality"
            ]
            self.assertEqual(len(matches), 1)
            self.assertEqual(matches[0].classification, "related_declaration")
            self.assertEqual(matches[0].declaration_name, related.name)

    def test_duplicate_card_identity_is_quarantined(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "0-backlog",
                "first.md",
                """
                # First RH claim

                - **ID:** duplicate-id
                - **Stage:** 0-backlog
                - **Type:** CONJECTURE
                - **Statement:** First Riemann Hypothesis producer.
                """,
            )
            write_card(
                pipeline,
                "1-in-progress",
                "second.md",
                """
                # Conflicting RH claim

                - **ID:** duplicate-id
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Different Riemann Hypothesis producer.
                """,
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )

            self.assertIsNone(brief.selected)
            self.assertEqual(brief.frontier, ())
            self.assertIn(
                "duplicate_card_id duplicate-id "
                "docs/drafts/pipeline/0-backlog/first.md "
                "docs/drafts/pipeline/1-in-progress/second.md",
                brief.diagnostics,
            )

    def test_rightmost_open_handover_marker_beats_older_frontier(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            handover = root / "docs" / "handover" / "rhultra.md"
            handover.parent.mkdir(parents=True)
            handover.write_text(
                textwrap.dedent(
                    """
                    # RH ultra handover

                    **Handover date:** 2026-07-21

                    ## Immediate lane

                    ```text
                    source exterior cube [OPEN]
                    -> integer-polynomial charge domination [OPEN; RIGHTMOST]
                    -> Weil positivity [LEAN-CLOSED]
                    -> RH.
                    ```

                    Attack the rightmost open node first: discharge
                    `XiSquaredEulerApertureIntChargeDominated`. The downstream implication
                    to RH is formally closed.
                    """
                ).lstrip(),
                encoding="utf-8",
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )

            self.assertIsNotNone(brief.selected)
            self.assertEqual(brief.selected.id, "handover:rhultra:9")
            self.assertEqual(brief.selected.source_kind, "rightmost_frontier")
            self.assertIn(
                "XiSquaredEulerApertureIntChargeDominated",
                brief.selected.statement,
            )

    def test_incidental_backticked_variable_is_not_a_duplicate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "coefficient.md",
                """
                # RH coefficient control

                - **ID:** coefficient
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Control coefficient `k` in the Riemann Hypothesis response.
                """,
            )
            declaration = formal_tools.Declaration(
                "theorem",
                "k",
                "GaloisForLFunctions.RHTower.SomeProof",
                "formal/GaloisForLFunctions/RHTower/SomeProof.lean",
                20,
                "An unrelated local helper.",
            )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(declaration,),
                limit=3,
            )

            self.assertIsNotNone(brief.selected)
            self.assertEqual(brief.selected.id, "coefficient")
            self.assertFalse(
                any(
                    match.classification == "already_formalized"
                    for match in brief.prior_work
                )
            )

    def test_markdown_brief_summarizes_large_diagnostic_set(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pipeline = root / "docs" / "drafts" / "pipeline"
            write_card(
                pipeline,
                "1-in-progress",
                "producer.md",
                """
                # RH producer

                - **ID:** producer
                - **Stage:** 1-in-progress
                - **Type:** CONJECTURE
                - **Statement:** Construct a Riemann Hypothesis producer.
                """,
            )
            for index in range(20):
                write_card(
                    pipeline,
                    "1-in-progress",
                    f"legacy-{index:02d}.md",
                    f"# Legacy fragment {index}\n",
                )

            brief = formal_tools.build_research_brief(
                root=root,
                area="RH",
                declarations=(),
                limit=3,
            )
            rendered = formal_tools.render_research_brief(brief)

            self.assertEqual(rendered.count("missing_required_fields"), 12)
            self.assertIn("- ... 8 more diagnostics (use --format json for all)", rendered)


if __name__ == "__main__":
    unittest.main()
