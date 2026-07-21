from __future__ import annotations

import dataclasses
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal"
sys.path.insert(0, str(ROOT / "scripts"))

from research_brief import (  # noqa: E402
    EXPORT_SENTINEL,
    LeanFrontierExport,
    PropositionRef,
    Reduction,
    compute_frontier,
    parse_lean_frontier_export,
)


FIXTURE_MODULE = "GaloisForLFunctions.FrontierInterfaceSolverFixture"
FIXTURE_NAMESPACE = "RHTower.FrontierInterfaceSolverFixture"

FIXTURE_SOURCE = r"""
import GaloisForLFunctions.Core

def RiemannHypothesis : Prop := False

namespace RHTower.FrontierInterfaceSolverFixture

def ExactWall : Prop := True

theorem exactWall_holds : ExactWall := True.intro

theorem exactWall_reaches_rh
    (_h : ExactWall) (hRH : RiemannHypothesis) : RiemannHypothesis := hRH

def DefeqWall : Prop := True

abbrev DefeqAlias : Prop := DefeqWall

theorem a_defeqAlias_holds : DefeqAlias := True.intro

theorem z_defeqAlias_holds : DefeqAlias := True.intro

theorem defeqWall_reaches_rh
    (_h : DefeqWall) (hRH : RiemannHypothesis) : RiemannHypothesis := hRH

def ParamWall (n : Nat) : Prop := n = n

theorem paramWall_holds (n : Nat) : ParamWall n := rfl

theorem paramWall_seven_reaches_rh
    (_h : ParamWall 7) (hRH : RiemannHypothesis) : RiemannHypothesis := hRH

def ChainBase (n : Nat) : Prop := n = n

def ChainWall : Prop := True

theorem chainBase_holds (n : Nat) : ChainBase n := rfl

theorem chainWall_of_base_seven (_h : ChainBase 7) : ChainWall := True.intro

theorem chainWall_reaches_rh
    (_h : ChainWall) (hRH : RiemannHypothesis) : RiemannHypothesis := hRH

def CircularWall : Prop := RiemannHypothesis

theorem circularWall_of_rh (hRH : RiemannHypothesis) : CircularWall := hRH

theorem rh_of_circularWall (h : CircularWall) : RiemannHypothesis := h

def GenericWall (n : Nat) : Prop := n = 0

theorem genericWall_of_ordinary_hypothesis
    (n : Nat) (h : n = 0) : GenericWall n := h

theorem genericWall_one_reaches_rh
    (_h : GenericWall 1) (hRH : RiemannHypothesis) : RiemannHypothesis := hRH

end RHTower.FrontierInterfaceSolverFixture
""".lstrip()

FIXTURE_THEOREMS = (
    f"{FIXTURE_NAMESPACE}.z_defeqAlias_holds",
    f"{FIXTURE_NAMESPACE}.exactWall_reaches_rh",
    f"{FIXTURE_NAMESPACE}.genericWall_of_ordinary_hypothesis",
    f"{FIXTURE_NAMESPACE}.chainWall_reaches_rh",
    f"{FIXTURE_NAMESPACE}.paramWall_holds",
    f"{FIXTURE_NAMESPACE}.circularWall_of_rh",
    f"{FIXTURE_NAMESPACE}.chainBase_holds",
    f"{FIXTURE_NAMESPACE}.defeqWall_reaches_rh",
    f"{FIXTURE_NAMESPACE}.exactWall_holds",
    f"{FIXTURE_NAMESPACE}.rh_of_circularWall",
    f"{FIXTURE_NAMESPACE}.paramWall_seven_reaches_rh",
    f"{FIXTURE_NAMESPACE}.a_defeqAlias_holds",
    f"{FIXTURE_NAMESPACE}.chainWall_of_base_seven",
    f"{FIXTURE_NAMESPACE}.genericWall_one_reaches_rh",
)


class LeanFrontierInterfaceSolverTests(unittest.TestCase):
    _temporary: tempfile.TemporaryDirectory[str]
    export: LeanFrontierExport
    reversed_export: LeanFrontierExport

    @classmethod
    def setUpClass(cls) -> None:
        cls._temporary = tempfile.TemporaryDirectory(
            prefix="hgt-frontier-interface-solver-"
        )
        cls._temporary_root = Path(cls._temporary.name)
        cls._prepare_project_overlay()
        cls._env = cls._lean_environment(cls._temporary_root)
        cls._compile_fixture()
        cls.export = cls._run_export(FIXTURE_THEOREMS, "forward")
        cls.reversed_export = cls._run_export(
            tuple(reversed(FIXTURE_THEOREMS)), "reversed"
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls._temporary.cleanup()

    @classmethod
    def _prepare_project_overlay(cls) -> None:
        compiled_root = FORMAL / ".lake" / "build" / "lib" / "lean"
        compiled_package = compiled_root / "GaloisForLFunctions"
        overlay_package = cls._temporary_root / "GaloisForLFunctions"
        overlay_package.mkdir()
        for suffix in (".olean", ".ilean"):
            compiled = compiled_root / f"GaloisForLFunctions{suffix}"
            if compiled.exists():
                (cls._temporary_root / compiled.name).symlink_to(compiled)
        for compiled in compiled_package.iterdir():
            (overlay_package / compiled.name).symlink_to(compiled)

    @classmethod
    def _lean_environment(cls, temporary_root: Path) -> dict[str, str]:
        configured = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=FORMAL,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if configured.returncode:
            raise AssertionError(
                "cannot read project LEAN_PATH:\n"
                + (configured.stderr or configured.stdout)
            )
        lean_binary = subprocess.run(
            ["lake", "env", "which", "lean"],
            cwd=FORMAL,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if lean_binary.returncode:
            raise AssertionError(
                "cannot locate project Lean binary:\n"
                + (lean_binary.stderr or lean_binary.stdout)
            )
        cls._lean_binary = lean_binary.stdout.strip()
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(
            (str(temporary_root), configured.stdout.strip())
        )
        return env

    @classmethod
    def _run_lean(cls, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [cls._lean_binary, *arguments],
            cwd=FORMAL,
            env=cls._env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    @classmethod
    def _compile_fixture(cls) -> None:
        source = (
            cls._temporary_root
            / "GaloisForLFunctions"
            / "FrontierInterfaceSolverFixture.lean"
        )
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(FIXTURE_SOURCE, encoding="utf-8")
        olean = source.with_suffix(".olean")
        result = cls._run_lean(
            "-R",
            str(cls._temporary_root),
            "-o",
            str(olean),
            str(source),
        )
        if result.returncode:
            raise AssertionError(
                "temporary Lean frontier fixture failed to compile:\n"
                + (result.stderr or result.stdout)
            )

    @classmethod
    def _run_export(
        cls, theorem_names: tuple[str, ...], label: str
    ) -> LeanFrontierExport:
        exporter = (ROOT / "scripts" / "lean" / "export_research_frontier.lean").read_text(
            encoding="utf-8"
        )
        project_import = "import GaloisForLFunctions\n"
        if project_import not in exporter:
            raise AssertionError("Lean frontier exporter has no project import marker")
        requested = ",\n".join(f"  {json.dumps(name)}" for name in theorem_names)
        generated_source = exporter.replace(
            project_import,
            f"import {FIXTURE_MODULE}\n",
            1,
        ) + f"\n#export_research_frontier [\n{requested}\n]\n"
        generated = cls._temporary_root / f"ExportFrontierInterfaces_{label}.lean"
        generated.write_text(generated_source, encoding="utf-8")
        result = cls._run_lean("-R", str(cls._temporary_root), str(generated))
        if result.returncode:
            raise AssertionError(
                "temporary Lean frontier export failed:\n"
                + (result.stderr or result.stdout)
            )
        payload = next(
            (
                line[len(EXPORT_SENTINEL) :]
                for line in result.stdout.splitlines()
                if line.startswith(EXPORT_SENTINEL)
            ),
            None,
        )
        if payload is None:
            raise AssertionError(
                "temporary Lean frontier export produced no JSON:\n" + result.stdout
            )
        return parse_lean_frontier_export(payload)

    def _declared(self, short_name: str) -> Reduction:
        full_name = f"{FIXTURE_NAMESPACE}.{short_name}"
        return next(item for item in self.export.reductions if item.name == full_name)

    @staticmethod
    def _premise(reduction: Reduction, declaration_suffix: str) -> PropositionRef:
        return next(
            item
            for item in reduction.premises
            if item.declaration and item.declaration.endswith(declaration_suffix)
        )

    def _solver_witnesses(
        self, target: PropositionRef, *, export: LeanFrontierExport | None = None
    ) -> tuple[Reduction, ...]:
        source = export or self.export
        return tuple(
            item
            for item in source.reductions
            if getattr(item, "provenance", "declared") == "interface_solver"
            and not item.premises
            and any(conclusion.key == target.key for conclusion in item.conclusions)
        )

    @staticmethod
    def _brief_for(
        export: LeanFrontierExport,
        target: PropositionRef,
        reductions: tuple[Reduction, ...],
    ):
        return compute_frontier(
            dataclasses.replace(export, target=target, reductions=reductions)
        )

    def test_exact_declared_theorem_closes_interface(self) -> None:
        proof = self._declared("exactWall_holds")
        self.assertEqual(proof.premises, ())
        self.assertEqual(getattr(proof, "provenance", "declared"), "declared")
        target = proof.conclusions[0]

        brief = self._brief_for(self.export, target, (proof,))

        self.assertTrue(brief.target_proven)
        self.assertEqual(brief.frontier, ())

    def test_definitionally_equal_abbrev_proof_closes_named_interface(self) -> None:
        connector = self._declared("defeqWall_reaches_rh")
        target = self._premise(connector, ".DefeqWall")

        witnesses = self._solver_witnesses(target)

        self.assertEqual(len(witnesses), 1)
        witness = witnesses[0]
        expected = f"{FIXTURE_NAMESPACE}.a_defeqAlias_holds"
        self.assertEqual(witness.status, "live")
        self.assertEqual(getattr(witness, "witness", None), expected)
        self.assertEqual(witness.proof_dependencies, (expected,))
        self.assertTrue(witness.name.startswith(f"interface-solver:{expected}=>"))
        self.assertTrue(self._brief_for(self.export, target, witnesses).target_proven)

    def test_polymorphic_theorem_is_specialized_to_exact_interface(self) -> None:
        connector = self._declared("paramWall_seven_reaches_rh")
        target = self._premise(connector, ".ParamWall")

        witnesses = self._solver_witnesses(target)

        self.assertEqual(len(witnesses), 1)
        expected = f"{FIXTURE_NAMESPACE}.paramWall_holds"
        self.assertEqual(getattr(witnesses[0], "witness", None), expected)
        self.assertEqual(witnesses[0].conclusions, (target,))
        self.assertTrue(self._brief_for(self.export, target, witnesses).target_proven)

    def test_specialized_witness_closes_prerequisite_chain(self) -> None:
        step = self._declared("chainWall_of_base_seven")
        base = self._premise(step, ".ChainBase")
        target = step.conclusions[0]
        base_witnesses = self._solver_witnesses(base)
        self.assertEqual(len(base_witnesses), 1)
        self.assertEqual(
            getattr(base_witnesses[0], "witness", None),
            f"{FIXTURE_NAMESPACE}.chainBase_holds",
        )

        brief = self._brief_for(self.export, target, base_witnesses + (step,))

        self.assertTrue(brief.target_proven)
        self.assertEqual(brief.frontier, ())

    def test_rh_cycle_cannot_be_used_as_interface_witness(self) -> None:
        circular_of_rh = self._declared("circularWall_of_rh")
        rh_of_circular = self._declared("rh_of_circularWall")
        circular = circular_of_rh.conclusions[0]
        rh = rh_of_circular.conclusions[0]

        self.assertEqual(self._solver_witnesses(circular), ())
        brief = self._brief_for(
            self.export,
            rh,
            (circular_of_rh, rh_of_circular),
        )

        self.assertFalse(brief.target_proven)
        self.assertEqual(brief.frontier, ())

    def test_solver_witness_selection_is_request_order_independent(self) -> None:
        def signature(export: LeanFrontierExport) -> tuple[tuple[object, ...], ...]:
            return tuple(
                sorted(
                    (
                        item.name,
                        getattr(item, "witness", None),
                        tuple(conclusion.key for conclusion in item.conclusions),
                        item.proof_dependencies,
                    )
                    for item in export.reductions
                    if getattr(item, "provenance", "declared") == "interface_solver"
                )
            )

        self.assertNotEqual(signature(self.export), ())
        self.assertEqual(signature(self.export), signature(self.reversed_export))

    def test_theorem_with_generic_ordinary_hypothesis_does_not_close_interface(self) -> None:
        connector = self._declared("genericWall_one_reaches_rh")
        target = self._premise(connector, ".GenericWall")
        generic_theorem = f"{FIXTURE_NAMESPACE}.genericWall_of_ordinary_hypothesis"

        self.assertNotIn(generic_theorem, {item.name for item in self.export.reductions})
        self.assertEqual(self._solver_witnesses(target), ())
        brief = self._brief_for(self.export, target, ())

        self.assertFalse(brief.target_proven)
        self.assertEqual(brief.cuts, ())


if __name__ == "__main__":
    unittest.main()
