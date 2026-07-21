from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from research_brief import (  # noqa: E402
    LeanFrontierExport,
    PropositionRef,
    Reduction,
    compute_frontier,
    parse_lean_frontier_export,
    render_research_brief,
)


RH = PropositionRef(
    key="RiemannHypothesis",
    expression="RiemannHypothesis",
    declaration="RiemannHypothesis",
)


def prop(name: str) -> PropositionRef:
    return PropositionRef(key=name, expression=name, declaration=name)


def reduction(
    name: str,
    premises: tuple[PropositionRef, ...],
    conclusions: tuple[PropositionRef, ...],
    *,
    status: str = "live",
) -> Reduction:
    return Reduction(
        name=name,
        module="GaloisForLFunctions.RHTower.ResearchFrontier",
        type_text=f"{name} type",
        premises=premises,
        conclusions=conclusions,
        relation="implication",
        status=status,
        type_dependencies=tuple(
            sorted({p.declaration for p in premises + conclusions if p.declaration})
        ),
        proof_dependencies=(),
        doc="synthetic exact Lean reduction",
    )


class LeanResearchFrontierTests(unittest.TestCase):
    def test_nonclassical_open_interface_is_frontier_without_route_prior(self) -> None:
        invariant = prop("RHTower.UnexpectedArithmeticInvariant")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(
                reduction(
                    "RHTower.unexpectedArithmeticInvariant_implies_rh",
                    (invariant,),
                    (RH,),
                ),
            ),
        )

        brief = compute_frontier(export)

        self.assertFalse(brief.target_proven)
        self.assertEqual([node.key for node in brief.frontier], [invariant.key])
        self.assertEqual(
            brief.frontier[0].via_reductions,
            ("RHTower.unexpectedArithmeticInvariant_implies_rh",),
        )

    def test_open_leaf_is_selected_through_multi_step_reduction(self) -> None:
        source = prop("RHTower.SourceEstimate")
        transfer = prop("RHTower.TransferWall")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(
                reduction("RHTower.source_to_transfer", (source,), (transfer,)),
                reduction("RHTower.transfer_to_rh", (transfer,), (RH,)),
            ),
        )

        brief = compute_frontier(export)

        self.assertEqual([node.key for node in brief.frontier], [source.key])
        self.assertEqual(brief.frontier[0].distance_to_target, 2)
        self.assertEqual(
            brief.frontier[0].via_reductions,
            ("RHTower.source_to_transfer", "RHTower.transfer_to_rh"),
        )

    def test_unconditional_reduction_closes_premise_and_target(self) -> None:
        source = prop("RHTower.SourceEstimate")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(
                reduction("RHTower.source_estimate", (), (source,)),
                reduction("RHTower.source_estimate_implies_rh", (source,), (RH,)),
            ),
        )

        brief = compute_frontier(export)

        self.assertTrue(brief.target_proven)
        self.assertEqual(brief.frontier, ())

    def test_retired_reduction_cannot_create_frontier(self) -> None:
        viable = prop("RHTower.ViableWall")
        impossible = prop("RHTower.ImpossibleLegacyWall")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(
                reduction("RHTower.viable_implies_rh", (viable,), (RH,)),
                reduction(
                    "RHTower.legacy_implies_rh",
                    (impossible,),
                    (RH,),
                    status="retired",
                ),
            ),
        )

        brief = compute_frontier(export)

        self.assertEqual([node.key for node in brief.frontier], [viable.key])
        self.assertEqual(brief.retired_reductions, ("RHTower.legacy_implies_rh",))

    def test_frontier_order_is_deterministic_by_unlock_then_name(self) -> None:
        alpha = prop("RHTower.AlphaWall")
        beta = prop("RHTower.BetaWall")
        mid = prop("RHTower.MidWall")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(
                reduction("RHTower.beta_to_mid", (beta,), (mid,)),
                reduction("RHTower.mid_to_rh", (mid,), (RH,)),
                reduction("RHTower.alpha_to_rh", (alpha,), (RH,)),
            ),
        )

        brief = compute_frontier(export)

        self.assertEqual(
            [node.key for node in brief.frontier],
            ["RHTower.BetaWall", "RHTower.AlphaWall"],
        )

    def test_json_parser_rejects_unknown_schema(self) -> None:
        with self.assertRaisesRegex(ValueError, "schema_version"):
            parse_lean_frontier_export(json.dumps({"schema_version": 99}))

    def test_rendered_brief_cites_only_lean_declarations(self) -> None:
        wall = prop("RHTower.TypedWall")
        export = LeanFrontierExport(
            schema_version=1,
            area="rh",
            target=RH,
            reductions=(reduction("RHTower.typedWall_implies_rh", (wall,), (RH,)),),
        )

        rendered = render_research_brief(compute_frontier(export))

        self.assertIn("`RHTower.TypedWall`", rendered)
        self.assertIn("`RHTower.typedWall_implies_rh`", rendered)
        self.assertNotIn("0-backlog", rendered)
        self.assertNotIn("1-in-progress", rendered)
        self.assertNotIn("handover", rendered.lower())


if __name__ == "__main__":
    unittest.main()
