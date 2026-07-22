from __future__ import annotations

import re
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import research_brief  # noqa: E402
from research_brief import (  # noqa: E402
    LeanFrontierExport,
    PropositionRef,
    Reduction,
    ResearchBrief,
)


RH = PropositionRef(
    key="RiemannHypothesis",
    expression="RiemannHypothesis",
    declaration="RiemannHypothesis",
)
FIXTURE_MODULE = "GaloisForLFunctions.RHTower.FrontierChainFixture"
FIXTURE_PATH = "formal/GaloisForLFunctions/RHTower/FrontierChainFixture.lean"


def prop(name: str) -> PropositionRef:
    qualified = name if "." in name else f"RHTower.{name}"
    return PropositionRef(
        key=qualified,
        expression=qualified,
        declaration=qualified,
    )


def reduction(
    name: str,
    premises: tuple[PropositionRef, ...],
    conclusion: PropositionRef,
    *,
    line: int,
) -> Reduction:
    qualified = name if "." in name else f"RHTower.{name}"
    return Reduction(
        name=qualified,
        module=FIXTURE_MODULE,
        type_text=(
            " -> ".join(item.expression for item in premises + (conclusion,))
        ),
        premises=premises,
        conclusions=(conclusion,),
        relation="implication",
        status="live",
        type_dependencies=tuple(
            sorted(
                {
                    item.declaration
                    for item in premises + (conclusion,)
                    if item.declaration
                }
            )
        ),
        proof_dependencies=(f"{qualified}.proof",),
        axioms=(),
        doc=f"Compiled Lean fixture reduction {qualified}.",
        relpath=FIXTURE_PATH,
        line=line,
        provenance="declared",
    )


def export_of(reductions: tuple[Reduction, ...]) -> LeanFrontierExport:
    return LeanFrontierExport(
        schema_version=1,
        area="rh",
        target=RH,
        reductions=reductions,
        commit="fixture-commit-0123456789abcdef",
    )


def main_export() -> LeanFrontierExport:
    a = prop("A")
    a_mid = prop("AMid")
    extra = prop("Extra")
    b = prop("B")
    c = prop("C")
    closed = prop("Closed")
    d, e, f = (prop(name) for name in ("D", "E", "F"))
    def_mid = prop("DEFMid")
    g, h, i, j = (prop(name) for name in ("G", "H", "I", "J"))
    k, ell, m, n, o = (
        prop(name) for name in ("K", "L", "M", "N", "O")
    )
    cycle_open = prop("CycleOpen")
    cycle_x = prop("CycleX")
    cycle_y = prop("CycleY")
    circular = prop("CircularCriterion")

    return export_of(
        (
            reduction("a_to_mid", (a,), a_mid, line=10),
            reduction("a_mid_to_rh", (a_mid,), RH, line=20),
            # This direct route is shorter than the proper-subset route.  It is
            # still not a minimal cut and must be removed by set inclusion.
            reduction("a_and_extra_to_rh", (a, extra), RH, line=30),
            reduction("closed_holds", (), closed, line=40),
            reduction("b_c_closed_to_rh", (b, c, closed), RH, line=50),
            reduction("d_e_f_to_mid", (d, e, f), def_mid, line=60),
            reduction("def_mid_to_rh", (def_mid,), RH, line=70),
            reduction("g_h_i_j_to_rh", (g, h, i, j), RH, line=80),
            reduction("five_gap_to_rh", (k, ell, m, n, o), RH, line=90),
            # Internal SCC with an honest external ingress.  The ingress must
            # survive while the cyclic implementation nodes do not become gaps.
            reduction("cycle_open_to_x", (cycle_open,), cycle_x, line=100),
            reduction("cycle_x_to_y", (cycle_x,), cycle_y, line=110),
            reduction("cycle_y_to_x", (cycle_y,), cycle_x, line=120),
            reduction("cycle_y_to_rh", (cycle_y,), RH, line=130),
            # Pure RH equivalence cycle: neither direction is evidence for RH.
            reduction("rh_to_circular", (RH,), circular, line=140),
            reduction("circular_to_rh", (circular,), RH, line=150),
        )
    )


def tied_export(count: int = 25) -> LeanFrontierExport:
    return export_of(
        tuple(
            reduction(
                f"rank_route_{index:02d}",
                (prop(f"RankGap{index:02d}"),),
                RH,
                line=200 + index,
            )
            for index in range(count)
        )
    )


class FrontierChainEnumerationTests(unittest.TestCase):
    def enumerate(
        self,
        export: LeanFrontierExport,
        *,
        max_gaps: int = 4,
        limit: int | None = None,
    ) -> ResearchBrief:
        function = getattr(research_brief, "enumerate_frontier_chains", None)
        self.assertIsNotNone(
            function,
            "research_brief must expose complete frontier-chain enumeration",
        )
        return function(export, max_gaps=max_gaps, limit=limit)

    def test_groups_complete_minimal_cuts_from_one_through_four_gaps(self) -> None:
        brief = self.enumerate(main_export(), max_gaps=4, limit=None)
        cardinalities = [len(cut.nodes) for cut in brief.cuts]

        # Intermediate interfaces are valid cuts too: proving ``AMid``,
        # ``DEFMid``, or either side of the non-target cycle directly is a
        # sufficient research result.  Enumeration must still be complete and
        # grouped by cardinality.
        self.assertEqual(cardinalities, [1, 1, 1, 1, 1, 1, 2, 3, 4])
        self.assertEqual(Counter(cardinalities), {1: 6, 2: 1, 3: 1, 4: 1})
        self.assertEqual(getattr(brief, "max_gaps", None), 4)
        self.assertFalse(
            any("RHTower.K" == node.key for cut in brief.cuts for node in cut.nodes),
            "five-gap route must not leak through a bounded enumeration",
        )

        two_gap_only = self.enumerate(main_export(), max_gaps=2, limit=None)
        self.assertEqual(
            [len(cut.nodes) for cut in two_gap_only.cuts],
            [1, 1, 1, 1, 1, 1, 2],
        )

    def test_preserves_joint_hyperedge_and_prunes_nonminimal_superset(self) -> None:
        brief = self.enumerate(main_export(), max_gaps=4, limit=None)
        cuts = {frozenset(node.key for node in cut.nodes): cut for cut in brief.cuts}

        joint_key = frozenset(("RHTower.B", "RHTower.C"))
        self.assertIn(joint_key, cuts)
        joint = cuts[joint_key]
        self.assertEqual(joint.via_reductions, ("RHTower.b_c_closed_to_rh",))
        self.assertEqual(joint.discharged, ("RHTower.Closed",))
        self.assertNotIn(frozenset(("RHTower.B",)), cuts)
        self.assertNotIn(frozenset(("RHTower.C",)), cuts)

        self.assertIn(frozenset(("RHTower.A",)), cuts)
        self.assertNotIn(
            frozenset(("RHTower.A", "RHTower.Extra")),
            cuts,
            "proper superset is nonminimal even when its proof path is shorter",
        )

    def test_cycles_do_not_close_rh_or_hide_an_external_ingress(self) -> None:
        brief = self.enumerate(main_export(), max_gaps=4, limit=None)
        all_gaps = {node.key for cut in brief.cuts for node in cut.nodes}

        self.assertFalse(brief.target_proven)
        self.assertIn("RHTower.CycleOpen", all_gaps)
        self.assertNotIn("RHTower.CircularCriterion", all_gaps)
        self.assertIn("RHTower.CircularCriterion", brief.equivalent_criteria)

    def test_top_twenty_order_is_deterministic_and_complete_before_limiting(self) -> None:
        forward_export = tied_export()
        reverse_export = export_of(tuple(reversed(forward_export.reductions)))

        complete = self.enumerate(forward_export, max_gaps=4, limit=None)
        forward = self.enumerate(forward_export, max_gaps=4, limit=20)
        reverse = self.enumerate(reverse_export, max_gaps=4, limit=20)

        self.assertEqual(len(complete.cuts), 25)
        expected = [f"RHTower.RankGap{index:02d}" for index in range(20)]
        self.assertEqual(
            [cut.nodes[0].key for cut in forward.cuts],
            expected,
        )
        self.assertEqual(
            [cut.nodes[0].key for cut in reverse.cuts],
            expected,
        )
        self.assertEqual(
            [cut.via_reductions for cut in forward.cuts],
            [cut.via_reductions for cut in reverse.cuts],
        )


class FrontierChainReportTests(unittest.TestCase):
    def enumerate(
        self,
        export: LeanFrontierExport,
        *,
        limit: int | None = None,
    ) -> ResearchBrief:
        function = getattr(research_brief, "enumerate_frontier_chains", None)
        self.assertIsNotNone(function)
        return function(export, max_gaps=4, limit=limit)

    def write(
        self, brief: ResearchBrief, output_dir: Path, *, limit: int = 20
    ) -> tuple[Path, ...]:
        function = getattr(research_brief, "write_chain_reports", None)
        self.assertIsNotNone(
            function,
            "research_brief must expose deterministic Markdown chain reports",
        )
        return function(brief, output_dir, limit=limit)

    @staticmethod
    def snapshot(output_dir: Path) -> dict[str, str]:
        return {
            path.relative_to(output_dir).as_posix(): path.read_text(encoding="utf-8")
            for path in sorted(output_dir.rglob("*"))
            if path.is_file()
        }

    def test_writes_grouped_index_and_one_evidence_report_per_chain(self) -> None:
        brief = self.enumerate(main_export())
        with tempfile.TemporaryDirectory(prefix="hgt-chain-reports-") as temporary:
            root = Path(temporary)
            first_dir = root / "first"
            second_dir = root / "second"

            paths = self.write(brief, first_dir, limit=20)
            repeated_paths = self.write(brief, second_dir, limit=20)

            self.assertEqual(paths[0], first_dir / "index.md")
            self.assertEqual(len(paths), len(brief.cuts) + 1)
            self.assertEqual(
                {path.resolve() for path in paths},
                {path.resolve() for path in first_dir.glob("*.md")},
            )
            self.assertEqual(
                [path.name for path in paths],
                [path.name for path in repeated_paths],
            )
            self.assertEqual(self.snapshot(first_dir), self.snapshot(second_dir))

            index = paths[0].read_text(encoding="utf-8")
            lower_index = index.lower()
            self.assertIn("compiled lean", lower_index)
            self.assertIn("snapshot", lower_index)
            self.assertIn("max_gaps=4", lower_index)
            self.assertIn("fixture-commit-0123456789abcdef", index)
            for gap_count in range(1, 5):
                self.assertRegex(
                    index,
                    rf"(?m)^## .*\b{gap_count}[- ]gap",
                )

            chain_paths = paths[1:]
            self.assertEqual(len(chain_paths), len(brief.cuts))
            for rank, (path, cut) in enumerate(zip(chain_paths, brief.cuts), start=1):
                self.assertRegex(
                    path.name,
                    rf"^chain-{rank:02d}-[a-z0-9][a-z0-9-]*\.md$",
                )
                self.assertIn(f"]({path.name})", index)
                report = path.read_text(encoding="utf-8")
                lower_report = report.lower()
                self.assertIn("compiled lean", lower_report)
                self.assertIn("snapshot", lower_report)
                self.assertIn("max_gaps=4", lower_report)
                self.assertIn("fixture-commit-0123456789abcdef", report)
                self.assertRegex(
                    report,
                    rf"(?i)gap count[^\n]*{len(cut.nodes)}",
                )
                for node in cut.nodes:
                    self.assertIn(f"`{node.key}`", report)
                    self.assertIn(node.expression, report)
                    self.assertIn(f"{node.relpath}:{node.line}", report)
                positions = [
                    report.index(f"`{name}`") for name in cut.via_reductions
                ]
                self.assertEqual(positions, sorted(positions))
                for discharged in cut.discharged:
                    self.assertIn(f"`{discharged}`", report)

    def test_report_limit_selects_same_deterministic_top_twenty(self) -> None:
        forward_export = tied_export()
        reverse_export = export_of(tuple(reversed(forward_export.reductions)))
        forward = self.enumerate(forward_export, limit=None)
        reverse = self.enumerate(reverse_export, limit=None)

        with tempfile.TemporaryDirectory(prefix="hgt-chain-top20-") as temporary:
            root = Path(temporary)
            forward_paths = self.write(forward, root / "forward", limit=20)
            reverse_paths = self.write(reverse, root / "reverse", limit=20)

            self.assertEqual(len(forward.cuts), 25)
            self.assertEqual(len(forward_paths), 21)
            self.assertEqual(
                [path.name for path in forward_paths],
                [path.name for path in reverse_paths],
            )
            forward_snapshot = self.snapshot(root / "forward")
            reverse_snapshot = self.snapshot(root / "reverse")
            self.assertEqual(forward_snapshot, reverse_snapshot)
            index = forward_paths[0].read_text(encoding="utf-8")
            for selected in range(20):
                self.assertIn(f"RHTower.RankGap{selected:02d}", index)
            for omitted in range(20, 25):
                self.assertNotIn(f"RHTower.RankGap{omitted:02d}", index)


if __name__ == "__main__":
    unittest.main()
