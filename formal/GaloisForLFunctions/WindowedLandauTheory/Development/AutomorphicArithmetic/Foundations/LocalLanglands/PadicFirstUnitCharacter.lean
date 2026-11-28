import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicUnitReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicUnitCharacterReduction

/-! A p-adic chart carries first principal units to first principal
units in the completion. Their residue character criterion is
independent of the chart. -/

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Reciprocity

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

theorem kills_firstUnits_iff_padic
    (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) :
    (∀ u : (v.adicCompletion F)ˣ, u ∈ unitsLevel v 1 → χ u = 1) ↔
    ∀ z : ℤ_[p]ˣ, padicUnitReduction z = 1 →
      (χ.comp (Units.map i.toRingHom.toMonoidHom))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom z) = 1 := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := F)).surjective v
  let v := w.maximalIdeal
  obtain ⟨e, he⟩ := exists_padic_residue_equiv_of_completion v i hi
  let f := (i.toRingHom.comp (algebraMap ℤ_[p] ℚ_[p])).toMonoidHom
  let r := padicCompletionIntegersEquiv w i hi
  have hmem (u : unitsLevel (K := F) v 0) :
      u.val ∈ unitsLevel v 1 ↔ finiteCompletionUnitReduction v u = 1 :=
    (mem_unitsLevel_one_iff_lt_one v _).trans (finiteCompletionUnitReduction_eq_one_iff v u).symm
  have hchart (z : ℤ_[p]ˣ) : ∃ u : unitsLevel (K := F) v 0, u.val = Units.map f z ∧
      Units.map e.toRingHom.toMonoidHom (finiteCompletionUnitReduction v u) = padicUnitReduction z := by
    let u := (unitsLevelZeroEquivIntegerUnits v).symm (Units.map r.toRingHom.toMonoidHom z)
    have hu : (u.val : v.adicCompletion F) = i (z.val : ℚ_[p]) := by
      have h := congrArg (fun x : (CompletedIntegers v)ˣ => ((x.val : CompletedIntegers v) : v.adicCompletion F))
        ((unitsLevelZeroEquivIntegerUnits v).apply_symm_apply (Units.map r.toRingHom.toMonoidHom z))
      rwa [unitsLevelZeroEquivIntegerUnits_val] at h
    obtain ⟨z', hz', hzr⟩ := he u
    have hzz' : z' = z := Units.ext (Subtype.ext (i.injective (hz'.symm.trans hu)))
    exact ⟨u, Units.ext hu, hzz' ▸ hzr⟩
  constructor
  · intro h z hz
    obtain ⟨u, hu, hr⟩ := hchart z
    have h0 : finiteCompletionUnitReduction v u = 1 := by
      have h' := (Units.mapEquiv e.toMulEquiv).injective
      apply h'
      rw [map_one]
      exact hr.trans hz
    change χ (Units.map f z) = 1
    rw [← hu]
    exact h _ ((hmem u).mpr h0)
  · intro h u hu
    have hu0 : u ∈ unitsLevel v 0 := unitsLevel_antitone v (by omega : 0 ≤ 1) hu
    let a : unitsLevel (K := F) v 0 := ⟨u, hu0⟩
    obtain ⟨z, hz, hzr⟩ := he a
    have h0 := (hmem a).mp hu
    have hz1 : padicUnitReduction z = 1 := by
      rw [show padicUnitReduction z = Units.map PadicInt.toZMod.toMonoidHom z from rfl,
        ← hzr, h0, map_one]
    have hc : u = Units.map f z := Units.ext hz
    rw [hc]
    exact h z hz1

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.kills_firstUnits_iff_padic
