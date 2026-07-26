from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import formal_tools  # noqa: E402
from research_brief import compute_frontier, run_lean_frontier_export  # noqa: E402


class LeanFrontierExporterIntegrationTests(unittest.TestCase):
    def test_real_rh_export_is_compiler_derived(self) -> None:
        export = run_lean_frontier_export(
            ROOT,
            area="RH",
            declarations=formal_tools.declarations(),
            refresh=True,
        )
        by_name = {item.name: item for item in export.reductions}

        connes = by_name[
            "RHTower.connesXiGroundStateLimitWall_implies_riemannHypothesis"
        ]
        self.assertEqual(connes.relation, "implication")
        self.assertEqual(
            [item.key for item in connes.premises],
            ["RHTower.ConnesXiGroundStateLimitWall"],
        )
        self.assertEqual(
            [item.key for item in connes.conclusions], ["RiemannHypothesis"]
        )

        hedenmalm = by_name[
            "RHTower.hedenmalmXiPositiveFormWall_iff_riemannHypothesis"
        ]
        self.assertEqual(hedenmalm.relation, "iff")

        mobius = by_name[
            "RHTower.mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis"
        ]
        self.assertEqual(mobius.relation, "implication")

        legacy = by_name[
            "RHTower.suzukiXiCharacteristicLimitWall_implies_riemannHypothesis"
        ]
        self.assertEqual(legacy.status, "retired")

        brief = compute_frontier(export, limit=256)
        frontier = {node.key for node in brief.frontier}
        equivalent = set(brief.equivalent_criteria)
        self.assertIn("RHTower.ConnesXiGroundStateLimitWall", equivalent)
        self.assertNotIn("RHTower.ConnesXiGroundStateLimitWall", frontier)
        self.assertTrue(
            any(
                key.startswith(
                    "RHTower.MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound"
                )
                for key in frontier
            )
        )
        self.assertNotIn("RHTower.MobiusDiscreteLaplaceHalfDecay", frontier)
        self.assertIn("RHTower.HedenmalmXiPositiveFormWall", equivalent)
        self.assertNotIn("RHTower.HedenmalmXiPositiveFormWall", frontier)
        self.assertNotIn("RHTower.SuzukiXiCharacteristicLimitWall", frontier)


if __name__ == "__main__":
    unittest.main()
