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


class IndexRowExtractionTests(unittest.TestCase):
    """The search index has to see declaration forms the API catalog regex skips."""

    def _index_rows(self, body: str, name: str = "Probe.lean"):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / name
            path.write_text(body, encoding="utf-8")
            stat = path.stat()
            source = formal_tools.SourceFile(name, str(path), stat.st_size, stat.st_mtime_ns)
            return formal_tools.index_rows(source)

    def _rows(self, body: str):
        return self._index_rows(body)[0]

    def _named(self, body: str) -> dict[str, str]:
        return {row.name: row.kind for row in self._rows(body)}

    def test_finds_plain_declarations(self) -> None:
        self.assertEqual(
            self._named("theorem alpha : True := trivial\ndef beta := 1\n"),
            {"alpha": "theorem", "beta": "def"},
        )

    def test_finds_modified_and_attributed_declarations(self) -> None:
        self.assertEqual(
            self._named(
                "noncomputable def gamma := 1\n"
                "private theorem delta : True := trivial\n"
                "@[aesop safe, simp] theorem epsilon : True := trivial\n"
                "instance zeta : Inhabited Nat := ⟨0⟩\n"
                "protected noncomputable def eta := 1\n"
            ),
            {
                "gamma": "noncomputable def",
                "delta": "private theorem",
                "epsilon": "theorem",
                "zeta": "instance",
                "eta": "protected noncomputable def",
            },
        )

    def test_skips_anonymous_and_non_declarations(self) -> None:
        rows = self._rows(
            "example : True := trivial\n"
            "instance : Inhabited Nat := ⟨0⟩\n"
            "import GaloisForLFunctions.Core\n"
            "theorem real_one : True := trivial\n"
        )
        self.assertEqual([row.name for row in rows], ["real_one"])

    def test_ignores_declaration_keywords_inside_comments(self) -> None:
        self.assertEqual(
            self._named("/-- doc mentioning\ntheorem ghost\n-/\ntheorem real_two := 1\n"),
            {"real_two": "theorem"},
        )

    def test_reads_the_docstring_above_an_attribute_line(self) -> None:
        rows = self._rows("/-- The real docstring. -/\n@[simp]\ntheorem theta : True := trivial\n")
        self.assertEqual([(r.name, r.doc) for r in rows], [("theta", "The real docstring.")])

    def test_records_markers_with_their_line_numbers(self) -> None:
        markers = self._index_rows("theorem alpha := 1\n-- TODO close the ladder gap\n")[1]
        self.assertEqual([(m.line, m.text) for m in markers], [(2, "-- TODO close the ladder gap")])

    def test_prose_files_contribute_markers_but_no_declarations(self) -> None:
        decls, markers = self._index_rows("theorem ghost := 1\nTODO write the proof\n", "STATUS.md")
        self.assertEqual(decls, [])
        self.assertEqual([m.line for m in markers], [2])


if __name__ == "__main__":
    unittest.main()
