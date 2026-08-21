/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite-field norm sequence for ABHN

For a finite extension of finite fields, the unit norm is surjective and its kernel is the image
of a cyclic coboundary.  This is the residue-field norm sequence that precedes the genuinely
local input of local class field theory.  It does not assert the local invariant theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- The norm on units of a finite-field extension is surjective, expressed in the additive
presentation used for exact sequences. -/
theorem finiteField_cyclicGaloisNormUnits_surjective {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] :
    Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  intro x
  obtain ⟨y, hy⟩ := FiniteField.unitsMap_norm_surjective K L (Additive.toMul x)
  refine ⟨Additive.ofMul y, ?_⟩
  apply Additive.toMul.injective
  change Units.map (Algebra.norm K) y = Additive.toMul x
  exact hy

/-- **Finite-field cyclic norm sequence.** For a chosen generator of the finite Galois group,
the cyclic coboundary has image the norm kernel, and the norm is surjective. -/
theorem finiteField_cyclicGaloisNormSequence {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite L] {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g) :
    Function.Exact (cyclicGaloisAdditiveCoboundary g) (cyclicGaloisAdditiveNormUnits K L) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  exact ⟨cyclicGalois_hilbert90_exact hg, finiteField_cyclicGaloisNormUnits_surjective⟩

/-- Every finite-field extension admits a cyclic norm sequence.  This chooses a generator of
its automatically cyclic Galois group, so no generator hypothesis is required from the caller. -/
theorem finiteField_exists_cyclicGaloisNormSequence {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] :
    ∃ g : Gal(L/K),
      Function.Exact (cyclicGaloisAdditiveCoboundary g) (cyclicGaloisAdditiveNormUnits K L) ∧
        Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact ⟨g, finiteField_cyclicGaloisNormSequence hg⟩

end GaloisForLFunctions.HTGeometry.ABHN
