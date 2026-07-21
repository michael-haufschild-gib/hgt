from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from research_brief import EXPORT_SENTINEL, compute_frontier, parse_lean_frontier_export  # noqa: E402


class LeanFrontierExporterIntegrationTests(unittest.TestCase):
    def test_real_rh_export_is_compiler_derived(self) -> None:
        exporter = ROOT / "scripts" / "lean" / "export_research_frontier.lean"
        process = subprocess.run(
            ["lake", "env", "lean", str(exporter)],
            cwd=ROOT / "formal",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=180,
        )
        self.assertEqual(process.returncode, 0, process.stderr or process.stdout)
        payload = next(
            (
                line[len(EXPORT_SENTINEL) :]
                for line in process.stdout.splitlines()
                if line.startswith(EXPORT_SENTINEL)
            ),
            None,
        )
        self.assertIsNotNone(payload, process.stdout)
        export = parse_lean_frontier_export(payload)
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
        self.assertIn("RHTower.ConnesXiGroundStateLimitWall", frontier)
        self.assertIn("RHTower.MobiusDiscreteLaplaceHalfDecay", frontier)
        self.assertNotIn("RHTower.HedenmalmXiPositiveFormWall", frontier)
        self.assertNotIn("RHTower.SuzukiXiCharacteristicLimitWall", frontier)


if __name__ == "__main__":
    unittest.main()
