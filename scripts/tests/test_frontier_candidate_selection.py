from __future__ import annotations

import dataclasses
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import research_brief  # noqa: E402


@dataclasses.dataclass(frozen=True)
class _Declaration:
    kind: str
    name: str
    module: str
    relpath: str
    line: int


class FrontierCandidateSelectionTests(unittest.TestCase):
    def test_producers_include_alias_witness_but_exclude_unrelated_theorem(self) -> None:
        selector = getattr(research_brief, "frontier_export_inputs", None)
        self.assertIsNotNone(
            selector,
            "frontier export needs one bounded candidate-and-producer selector",
        )

        source = """\
def RiemannHypothesis : Prop := False
def Wall : Prop := True
abbrev WallAlias : Prop := Wall
theorem wallAlias_holds : WallAlias := True.intro
theorem wall_reaches_rh (_h : Wall) : RiemannHypothesis := by
  exact False.elim RiemannHypothesis
theorem unrelated : 1 = 1 := rfl
"""
        declarations = (
            _Declaration("def", "RiemannHypothesis", "Fixture", "formal/Fixture.lean", 1),
            _Declaration("def", "Wall", "Fixture", "formal/Fixture.lean", 2),
            _Declaration("abbrev", "WallAlias", "Fixture", "formal/Fixture.lean", 3),
            _Declaration("theorem", "wallAlias_holds", "Fixture", "formal/Fixture.lean", 4),
            _Declaration("theorem", "wall_reaches_rh", "Fixture", "formal/Fixture.lean", 5),
            _Declaration("theorem", "unrelated", "Fixture", "formal/Fixture.lean", 7),
        )

        with tempfile.TemporaryDirectory(prefix="hgt-frontier-selection-") as temporary:
            root = Path(temporary)
            source_path = root / "formal" / "Fixture.lean"
            source_path.parent.mkdir(parents=True)
            source_path.write_text(source, encoding="utf-8")
            ilean = (
                root
                / "formal"
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "Fixture.ilean"
            )
            ilean.parent.mkdir(parents=True)
            ilean.write_text(
                json.dumps(
                    {
                        "decls": {
                            f"Fixture.{declaration.name}": {}
                            for declaration in declarations
                        }
                    }
                ),
                encoding="utf-8",
            )

            candidates, producers = selector(root, declarations)

        self.assertEqual(candidates, ("Fixture.wall_reaches_rh",))
        self.assertEqual(
            producers,
            (
                "Fixture.wallAlias_holds",
                "Fixture.wall_reaches_rh",
            ),
        )

    def test_export_request_uses_constant_size_file_backed_command(self) -> None:
        writer = getattr(research_brief, "write_frontier_export_request", None)
        self.assertIsNotNone(
            writer,
            "large declaration lists must not be embedded in Lean command syntax",
        )

        candidates = tuple(f"Fixture.candidate{index}" for index in range(10_000))
        producers = tuple(f"Fixture.producer{index}" for index in range(10_000))
        with tempfile.TemporaryDirectory(prefix="hgt-frontier-request-") as temporary:
            directory = Path(temporary)
            command = writer(directory, candidates, producers)

            self.assertLess(len(command), 1_024)
            self.assertIn("#export_research_frontier_from_files", command)
            self.assertEqual(
                (directory / "candidate-names.txt").read_text(
                    encoding="utf-8"
                ).splitlines(),
                list(candidates),
            )
            self.assertEqual(
                (directory / "producer-names.txt").read_text(
                    encoding="utf-8"
                ).splitlines(),
                list(producers),
            )


if __name__ == "__main__":
    unittest.main()
