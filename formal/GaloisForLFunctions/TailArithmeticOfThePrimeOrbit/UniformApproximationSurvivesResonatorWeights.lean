import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheResonatorMeanOfZeta

/-!
# Uniform approximation with a resonator weight

A squared weight bounded by `W` multiplies the unweighted square-norm
perturbation estimate by `W`. Cauchy–Schwarz gives `W = M Σ|r_m|²`
for a resonator supported on the positive integers up to `M`.
-/

noncomputable section
open Real Finset Filter Topology MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

theorem dyadicSquareMean_nonneg (f : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ dyadicSquareMean f T :=
  div_nonneg (intervalIntegral.integral_nonneg (by linarith only [hT])
    (fun _ _ => sq_nonneg _)) hT

/-- Cauchy–Schwarz costs only the number of possible positive frequencies. -/
theorem norm_headPoly_sq_le_support_energy {A : Finset ℕ}
    (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {M : ℕ}
    (hM : ∀ m ∈ A, m ≤ M) (t : ℝ) :
    ‖headPoly A r t‖ ^ 2 ≤ (M : ℝ) * ∑ m ∈ A, ‖r m‖ ^ 2 := by
  have hsub : A ⊆ Finset.Icc 1 M := fun m hm =>
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hA m hm), hM m hm⟩
  have hcard : (A.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ m ∈ A, ‖r m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_headPoly_le A r t) 2
    _ ≤ (A.card : ℝ) * ∑ m ∈ A, ‖r m‖ ^ 2 := _root_.sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- A bounded squared weight preserves the linear uniform-error estimate. -/
theorem abs_weighted_dyadicSquareMean_sub_le {R f g : ℝ → ℂ}
    (hR : Continuous R) (hf : Continuous f) (hg : Continuous g)
    {W T e : ℝ} (hW : 0 ≤ W) (hT : 0 < T) (he : 0 ≤ e)
    (hweight : ∀ t ∈ Set.Icc T (2 * T), ‖R t‖ ^ 2 ≤ W)
    (hclose : ∀ t ∈ Set.Icc T (2 * T), ‖f t - g t‖ ≤ e) :
    |dyadicSquareMean (fun t => R t * f t) T -
      dyadicSquareMean (fun t => R t * g t) T| ≤
        W * e * (dyadicSquareMean g T + 1 + e) := by
  have hab : T ≤ 2 * T := by linarith only [hT]
  have hf₂ : Continuous (fun t => ‖R t * f t‖ ^ 2) := (hR.mul hf).norm.pow 2
  have hg₂ : Continuous (fun t => ‖R t * g t‖ ^ 2) := (hR.mul hg).norm.pow 2
  have hg₀ : Continuous (fun t => ‖g t‖ ^ 2) := hg.norm.pow 2
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc T (2 * T)) :
      |‖R t * f t‖ ^ 2 - ‖R t * g t‖ ^ 2| ≤
        W * e * ‖g t‖ ^ 2 + W * e * (1 + e) := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul (hweight t ht) (_root_.RHTower.abs_norm_sq_sub_le he (hclose t ht))
      (abs_nonneg _) hW).trans_eq (by ring)
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hf₂.sub hg₂).abs.intervalIntegrable T (2 * T))
    (((continuous_const.mul hg₀).add continuous_const).intervalIntegrable T (2 * T)) hpoint
  have h := (intervalIntegral.abs_integral_le_integral_abs
    (f := fun t => ‖R t * f t‖ ^ 2 - ‖R t * g t‖ ^ 2) hab).trans hbound
  have hgi : IntervalIntegrable (fun t => W * e * ‖g t‖ ^ 2) volume T (2 * T) :=
    (continuous_const.mul hg₀).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hf₂.intervalIntegrable _ _) (hg₂.intervalIntegrable _ _),
    intervalIntegral.integral_add hgi (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
  have hd := div_le_div_of_nonneg_right h hT.le
  unfold dyadicSquareMean
  rw [← sub_div, abs_div, abs_of_pos hT]
  apply hd.trans_eq
  simp only [smul_eq_mul]
  field_simp [hT.ne']
  ring

/-- Uniform approximation transfers through every resonator of bounded support. -/
theorem abs_resonatorMean_sub_le_uniform_error {A : Finset ℕ}
    (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {M : ℕ}
    (hM : ∀ m ∈ A, m ≤ M) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {T e : ℝ} (hT : 0 < T) (he : 0 ≤ e)
    (hclose : ∀ t ∈ Set.Icc T (2 * T), ‖f t - g t‖ ≤ e) :
    |dyadicSquareMean (fun t => headPoly A r t * f t) T -
      dyadicSquareMean (fun t => headPoly A r t * g t) T| ≤
        ((M : ℝ) * e * (dyadicSquareMean g T + 1 + e)) *
          ∑ m ∈ A, ‖r m‖ ^ 2 := by
  have h := abs_weighted_dyadicSquareMean_sub_le (continuous_headPoly A r) hf hg
    (show 0 ≤ (M : ℝ) * ∑ m ∈ A, ‖r m‖ ^ 2 by positivity) hT he
    (fun t _ => norm_headPoly_sq_le_support_energy hA r hM t) hclose
  exact h.trans_eq (by ring)

#print axioms abs_weighted_dyadicSquareMean_sub_le
#print axioms abs_resonatorMean_sub_le_uniform_error

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
