from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import formal_tools


class OwnedModuleReachabilityTests(unittest.TestCase):
    def test_reports_owned_module_unreachable_from_its_umbrella(self) -> None:
        checker = getattr(formal_tools, "unreachable_owned_modules", None)
        self.assertIsNotNone(checker, "formal_tools must expose owned-module reachability")

        with tempfile.TemporaryDirectory() as tmp:
            formal = Path(tmp) / "formal"
            source = formal / "GaloisForLFunctions"
            area = source / "RHTower"
            area.mkdir(parents=True)

            (source / "RHTower.lean").write_text(
                "import GaloisForLFunctions.RHTower.Direct\n",
                encoding="utf-8",
            )
            (area / "Direct.lean").write_text(
                "import GaloisForLFunctions.RHTower.Nested\n",
                encoding="utf-8",
            )
            (area / "Nested.lean").write_text(
                "import GaloisForLFunctions.RHTower.Direct\n",
                encoding="utf-8",
            )
            (area / "Orphan.lean").write_text("def orphan := 1\n", encoding="utf-8")

            areas = {
                "rh_tower": {
                    "module": "GaloisForLFunctions.RHTower",
                    "path": area,
                }
            }

            self.assertEqual(
                checker(areas, formal=formal, src=source),
                {"rh_tower": ["GaloisForLFunctions.RHTower.Orphan"]},
            )


if __name__ == "__main__":
    unittest.main()
