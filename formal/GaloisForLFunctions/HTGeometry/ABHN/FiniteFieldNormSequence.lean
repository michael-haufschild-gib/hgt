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

/-- The inclusion of base-field units into a Galois extension, in the additive presentation used
for the cyclic norm sequence. -/
noncomputable def cyclicGaloisBaseUnitsMap {K L : Type} [Field K] [Field L] [Algebra K L] :
    Additive Kˣ →+ Additive Lˣ :=
  (Units.map (algebraMap K L)).toAdditive

/-- Base-field units embed into extension-field units. -/
theorem cyclicGaloisBaseUnitsMap_injective {K L : Type} [Field K] [Field L] [Algebra K L] :
    Function.Injective (cyclicGaloisBaseUnitsMap (K := K) (L := L)) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact congrArg Units.val (congrArg Additive.toMul hxy)

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

/-- For a finite-field extension, the kernel of the cyclic coboundary consists exactly of the
base-field units. -/
theorem finiteField_cyclicGaloisBaseUnits_coboundary_exact {K L : Type}
    [Field K] [Field L] [Algebra K L] [Finite L] {g : Gal(L/K)}
    (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g) :
    Function.Exact (cyclicGaloisBaseUnitsMap (K := K) (L := L))
      (cyclicGaloisAdditiveCoboundary g) := by
  intro x
  constructor
  · intro hx
    let u : Lˣ := x.toMul
    have hx' : cyclicGaloisCoboundary g u = 1 := by
      exact congrArg Additive.toMul hx
    have hfixedUnit : Units.map g.toMonoidHom u = u := by
      simpa [cyclicGaloisCoboundary] using (div_eq_one.mp hx').symm
    have hfixed : g (u : L) = (u : L) := by
      simpa using congrArg Units.val hfixedUnit
    have hg_mem : g ∈ MulAction.stabilizer (Gal(L/K)) (u : L) := by
      rw [MulAction.mem_stabilizer_iff]
      exact hfixed
    have hzpowers : Subgroup.zpowers g ≤ MulAction.stabilizer (Gal(L/K)) (u : L) :=
      Subgroup.zpowers_le_of_mem hg_mem
    have hfixed_all : ∀ sigma : Gal(L/K), sigma (u : L) = (u : L) := by
      intro sigma
      exact MulAction.mem_stabilizer_iff.mp (hzpowers (hg sigma))
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (u : L)).mpr hfixed_all
    have ha0 : a ≠ 0 := by
      intro ha0
      have hx0 : (u : L) = 0 := by simpa [ha0] using ha.symm
      exact u.ne_zero hx0
    refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change algebraMap K L a = (u : L)
    exact ha
  · rintro ⟨a, rfl⟩
    apply Additive.toMul.injective
    change cyclicGaloisCoboundary g
      (Units.map (algebraMap K L) (Additive.toMul a)) = 1
    have hfixed : Units.map g.toMonoidHom
        (Units.map (algebraMap K L) (Additive.toMul a)) =
        Units.map (algebraMap K L) (Additive.toMul a) := by
      apply Units.ext
      change g (algebraMap K L ((Additive.toMul a : Kˣ) : K)) =
        algebraMap K L ((Additive.toMul a : Kˣ) : K)
      exact g.commutes _
    rw [cyclicGaloisCoboundary, hfixed]
    exact div_self' _

/-- The full finite-field cyclic norm sequence is exact: base units are the kernel of the
coboundary, Hilbert 90 gives the next exactness, and the norm is surjective. -/
theorem finiteField_cyclicGaloisFullNormSequence {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite L] {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g) :
    Function.Injective (cyclicGaloisBaseUnitsMap (K := K) (L := L)) ∧
      Function.Exact (cyclicGaloisBaseUnitsMap (K := K) (L := L))
        (cyclicGaloisAdditiveCoboundary g) ∧
      Function.Exact (cyclicGaloisAdditiveCoboundary g) (cyclicGaloisAdditiveNormUnits K L) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  exact ⟨cyclicGaloisBaseUnitsMap_injective,
    finiteField_cyclicGaloisBaseUnits_coboundary_exact hg,
    cyclicGalois_hilbert90_exact hg, finiteField_cyclicGaloisNormUnits_surjective⟩

/-- Every finite-field extension admits a cyclic norm sequence.  This chooses a generator of
its automatically cyclic Galois group, so no generator hypothesis is required from the caller. -/
theorem finiteField_exists_cyclicGaloisNormSequence {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] :
    ∃ g : Gal(L/K),
      Function.Exact (cyclicGaloisAdditiveCoboundary g) (cyclicGaloisAdditiveNormUnits K L) ∧
        Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact ⟨g, finiteField_cyclicGaloisNormSequence hg⟩

/-- Every finite-field extension admits its full exact cyclic norm sequence. -/
theorem finiteField_exists_cyclicGaloisFullNormSequence {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] :
    ∃ g : Gal(L/K),
      Function.Injective (cyclicGaloisBaseUnitsMap (K := K) (L := L)) ∧
        Function.Exact (cyclicGaloisBaseUnitsMap (K := K) (L := L))
          (cyclicGaloisAdditiveCoboundary g) ∧
        Function.Exact (cyclicGaloisAdditiveCoboundary g) (cyclicGaloisAdditiveNormUnits K L) ∧
        Function.Surjective (cyclicGaloisAdditiveNormUnits K L) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact ⟨g, finiteField_cyclicGaloisFullNormSequence hg⟩

end GaloisForLFunctions.HTGeometry.ABHN
