import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalHeightDerivativeAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

private theorem smoothAFEZetaSquarePrimalHeightDerivativeLSeries_term_succ
    {N : ℕ} (hN : 4 ≤ N) (center y : ℝ) (n : ℕ) :
    LSeries.term (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
        ((y : ℝ) * I) (n + 1) =
      smoothAFEZetaSquarePrimalHeightDerivativeTerm N (y - center) n := by
  have hn : (n + 1 : ℕ) ≠ 0 := by omega
  have hnC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn,
    smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ,
    smoothAFEZetaSquarePrimalNatCoefficient_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  have hphase :
      (n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I) =
        (n + 1 : ℂ) ^ (-linePt (y - center)) := by
    rw [← Complex.cpow_sub _ _ hnC]
    congr 1
    simp only [linePt]
    push_cast
    ring
  calc
    ((((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt center - 1) *
            smoothAFEZetaSquarePrimalCutoff (N : ℝ)
              ((n + 1 : ℝ) * (N : ℝ))) *
          Complex.log (n + 1 : ℂ) * (-I)) /
        (n + 1 : ℂ) ^ ((y : ℝ) * I) =
      ((n + 1).divisors.card : ℂ) *
        ((n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I)) *
        Complex.log (n + 1 : ℂ) * (-I) *
          smoothAFEZetaSquarePrimalCutoff (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by ring
    _ = smoothAFEZetaSquarePrimalHeightDerivativeTerm N (y - center) n := by
      rw [hphase, smoothAFEZetaSquarePrimalCutoff_mul_conductor]
      · unfold smoothAFEZetaSquarePrimalHeightDerivativeTerm
        ring
      · exact_mod_cast (show N ≠ 0 by omega)

/-- The rephased derivative L-series is exactly the literal primal source derivative field. -/
theorem smoothAFEZetaSquarePrimalHeightDerivativeLSeries_eq_sourceField
    {N : ℕ} (hN : 4 ≤ N) (center y : ℝ) :
    LSeries (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
        ((y : ℝ) * I) =
      smoothAFEZetaSquarePrimalHeightDerivativeSourceField N (y - center) := by
  let a : ℕ → ℂ := smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center
  let s : ℂ := (y : ℝ) * I
  have habs : Summable (fun k : ℕ => ‖a k‖) :=
    (summable_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_affine_masses
      hN center).1
  have hterm : Summable (fun k : ℕ => LSeries.term a s k) := by
    rw [← summable_norm_iff]
    refine habs.congr (fun k => ?_)
    rw [LSeries.norm_term_eq]
    by_cases hk : k = 0
    · simp [hk, a]
    · simp [hk, s]
  have hsplit := hterm.sum_add_tsum_nat_add 1
  calc
    LSeries (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
        ((y : ℝ) * I) = ∑' k : ℕ, LSeries.term a s k := by rfl
    _ = ∑' n : ℕ, LSeries.term a s (n + 1) := by
      rw [← hsplit]
      simp [a, s]
    _ = ∑' n : ℕ,
        smoothAFEZetaSquarePrimalHeightDerivativeTerm N (y - center) n := by
      apply tsum_congr
      intro n
      exact smoothAFEZetaSquarePrimalHeightDerivativeLSeries_term_succ hN center y n
    _ = smoothAFEZetaSquarePrimalHeightDerivativeSourceField N (y - center) := rfl

/-- The literal primal derivative source field has the sharp affine `L²` estimate. -/
theorem exists_integral_normSq_smoothAFEZetaSquarePrimalHeightDerivativeSourceField_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ} {center H : ℝ},
      4 ≤ N → 1 ≤ H →
      (∫ t in Set.Icc (center - H) (center + H),
        ‖smoothAFEZetaSquarePrimalHeightDerivativeSourceField N t‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ 6) * H := by
  obtain ⟨B, hB, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquarePrimalHeightDerivativeLSeries_le
  refine ⟨B, hB, ?_⟩
  intro N center H hN hH
  have hbound := hmv (center := -center) hN hH
  have heq : (fun y : ℝ =>
      ‖LSeries (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N (-center))
        ((y : ℝ) * I)‖ ^ 2) =
      (fun y : ℝ =>
        ‖smoothAFEZetaSquarePrimalHeightDerivativeSourceField N (center + y)‖ ^ 2) := by
    funext y
    rw [smoothAFEZetaSquarePrimalHeightDerivativeLSeries_eq_sourceField hN]
    congr 3
    ring
  rw [heq] at hbound
  let F : ℝ → ℝ := fun t =>
    ‖smoothAFEZetaSquarePrimalHeightDerivativeSourceField N t‖ ^ 2
  have hle1 : center - H ≤ center + H := by linarith
  have hle2 : -H ≤ H := by linarith
  have htranslate :
      (∫ t in Set.Icc (center - H) (center + H), F t) =
        ∫ y in Set.Icc (-H) H, F (center + y) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle1,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle2]
    have hshift := intervalIntegral.integral_comp_add_left
      (a := -H) (b := H) F center
    rw [hshift]
    congr 1
  change (∫ t in Set.Icc (center - H) (center + H), F t) ≤ _
  rw [htranslate]
  exact hbound

end RHTower
