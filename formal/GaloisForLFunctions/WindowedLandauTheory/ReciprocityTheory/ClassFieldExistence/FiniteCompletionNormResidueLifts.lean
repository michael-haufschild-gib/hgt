import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration

/-! At an unramified finite place, norms of integral units realize
every residue unit. -/

noncomputable section

open NumberField IsDedekindDomain WithZero
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

private theorem lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) :
    x < 1 ↔ x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← exp_log hx, ← exp_zero, exp_lt_exp, exp_le_exp]
    omega

private theorem exists_integral_with_same_norm_residue
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) (x : CompletedIntegers v)
    (hx : completionReduction v x ≠ 0) :
    ∃ y : CompletedIntegers w, Valued.v y.val = 1 ∧
      completionReduction v (completedIntegerNorm v w y) = completionReduction v x := by
  letI := v.isMaximal
  letI := w.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)
    (completionReduction v x)
  have hb0 : b ≠ 0 := fun h => hx (by simpa only [h, Algebra.norm_zero] using hb.symm)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective b
  let y := toCompletedIntegers w r
  have hy : completionReduction w y = b := (completionReduction_toCompletedIntegers w r).trans hr
  refine ⟨y, le_antisymm y.2 (le_of_not_gt ?_), ?_⟩
  · intro h
    apply hb0
    rw [← hy, ← map_zero (completionReduction w), completionReduction_eq_iff]
    simpa only [ZeroMemClass.coe_zero, sub_zero] using h
  · rw [completionReduction_norm_of_unramified v w he, hy, hb]

private theorem unitsLevel_one_div_of_sub_lt_one (x z : (v.adicCompletion K)ˣ)
    (hz : Valued.v z.val = 1) (h : Valued.v (x.val - z.val) < 1) :
    x / z ∈ unitsLevel v 1 := by
  apply (mem_unitsLevel_of_one_le (n := 1) le_rfl).mpr
  apply (lt_one_iff_le_exp_neg_one _).mp
  rw [Units.val_div_eq_div_val]
  rw [show x.val / z.val - 1 = (x.val - z.val) / z.val by
    rw [sub_div, div_self z.ne_zero], map_div₀, hz, div_one]
  exact h

theorem exists_norm_lift_of_residueUnit (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (x : (v.adicCompletion K)ˣ) (hx : x ∈ unitsLevel v 0) :
    ∃ y : (w.adicCompletion L)ˣ, y ∈ unitsLevel w 0 ∧
      x / Units.map (Algebra.norm (v.adicCompletion K)) y ∈ unitsLevel v 1 := by
  have hvx := (mem_unitsLevel.mp hx).1
  let x' : CompletedIntegers v := ⟨x.val, hvx.le⟩
  have hx' : completionReduction v x' ≠ 0 := by
    intro h
    rw [← map_zero (completionReduction v), completionReduction_eq_iff] at h
    have hh : Valued.v x.val < 1 := by simpa only [x', ZeroMemClass.coe_zero, sub_zero] using h
    exact (not_lt_of_ge hvx.ge) hh
  obtain ⟨y', hy, hr⟩ := exists_integral_with_same_norm_residue v w he x' hx'
  have hy0 : y'.val ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact zero_ne_one hy
  let y := Units.mk0 y'.val hy0
  have hsub := (completionReduction_eq_iff v (completedIntegerNorm v w y') x').mp hr
  change Valued.v (Algebra.norm (v.adicCompletion K) y'.val - x.val) < 1 at hsub
  refine ⟨y, mem_unitsLevel.mpr ⟨hy, ?_⟩, unitsLevel_one_div_of_sub_lt_one v x _ ?_ ?_⟩
  · simpa only [y, Units.val_mk0, Nat.cast_zero, neg_zero, exp_zero] using
      Valuation.map_sub_le Valued.v hy.le (show Valued.v (1 : w.adicCompletion L) ≤ 1 by simp)
  · change Valued.v (Algebra.norm (v.adicCompletion K) y'.val) = 1
    rw [valued_finiteCompletion_norm v w, hy, one_pow]
  · change Valued.v (x.val - Algebra.norm (v.adicCompletion K) y'.val) < 1
    rw [Valuation.map_sub_swap]
    exact hsub

end GlobalTheory.Reciprocity
