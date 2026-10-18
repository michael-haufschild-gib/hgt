import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzSeed

/-! The actual factorial ramp is the positive-logarithmic restriction of an
explicit arithmetic sum whose Mellin transform vanishes at every zeta zero. -/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.RHTower
noncomputable section
set_option autoImplicit false

def factorialMuntzSum (n : ℕ) : ℝ → ℝ := arithmeticSum (factorialMuntzSeed n)

def factorialMuntzCompletion (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x/2)*factorialMuntzSum n (Real.exp x)/Real.sqrt ((n+1 : ℕ) : ℝ)

theorem factorialMuntzSum_measurable (n : ℕ) : Measurable (factorialMuntzSum n) :=
  measurable_arithmeticSum (factorialMuntzSeed_measurable n) (factorialMuntzSeed_support n)

theorem factorialMuntzSum_abs_le (n : ℕ) (t : ℝ) : |factorialMuntzSum n t| ≤ 10 := by
  have h := abs_arithmeticSum_le (factorialMuntzSeed_measurable n)
    (factorialMuntzSeed_abs_le n) (factorialMuntzSeed_boundedVariation n)
    (factorialMuntzSeed_support n) (factorialMuntzSeed_intervalIntegral n) t
  exact h.trans (by
    have hv := ENNReal.toReal_mono (by norm_num : (10 : ℝ≥0∞) ≠ ⊤)
      (factorialMuntzSeed_variation_le n)
    simpa using hv)

/-- Every premise of the arithmetic-summation Mellin theorem is discharged
for this concrete seed, including zero integral and whole-line variation. -/
theorem factorialMuntzSum_mellin_zero (n : ℕ) :
    ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 →
      mellin (fun t => (factorialMuntzSum n t : ℂ)) ρ = 0 := by
  intro ρ hρ hz
  exact mellin_arithmeticSum_eq_zero_of_zeta_eq_zero
    (factorialMuntzSeed_measurable n) (factorialMuntzSeed_abs_le n)
    (factorialMuntzSeed_boundedVariation n) (factorialMuntzSeed_support n)
    (factorialMuntzSeed_intervalIntegral n) hρ hz

private theorem ramp_term_zero (n K j : ℕ) (hK : 1 ≤ K) (hKN : K ≤ 4*(n+1))
    (hj : K < j) {x : ℝ} (hx : 0 ≤ x) :
    clampedRamp (sourceFactorialCollar (n+1))
      ((j : ℝ)*Real.exp x/(K : ℝ)) = 0 := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hb := sourceFactorialCollar_small_budget (N := n+1) (by omega) hKN
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hjR : (K : ℝ)+1 ≤ j := by exact_mod_cast (show K+1 ≤ j by omega)
  have he : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  apply clampedRamp_eq_zero hε
  apply (le_div_iff₀ hK0).2
  nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg j)]

private theorem sum_ramp_truncate (n K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ 4*(n+1))
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ j ∈ Finset.Icc 1 (4*(n+1)), clampedRamp (sourceFactorialCollar (n+1))
      ((j : ℝ)*Real.exp x/(K : ℝ))) =
    ∑ j ∈ Finset.Icc 1 K, clampedRamp (sourceFactorialCollar (n+1))
      ((j : ℝ)*Real.exp x/(K : ℝ)) := by
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hKN)
  intro j hj hjK
  apply ramp_term_zero n K j hK hKN _ hx
  have hj1 := (Finset.mem_Icc.mp hj).1
  simp only [Finset.mem_Icc, hj1, true_and, not_le] at hjK
  exact hjK

private theorem factorialMuntzSum_eq_finset (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    factorialMuntzSum n (Real.exp x) =
      ∑ j ∈ Finset.Icc 1 (4*(n+1)), factorialMuntzSeed n ((j : ℝ)*Real.exp x) := by
  unfold factorialMuntzSum arithmeticSum
  rw [tsum_eq_sum (s := Finset.range (4*(n+1))) ?_]
  · exact (sum_Icc_eq_sum_range_shift (factorialMuntzSeed n) (Real.exp x) (4*(n+1))).symm
  · intro j hj
    have hj' : 4*(n+1) < j+1 := by simp only [Finset.mem_range] at hj; omega
    have hp : 0 < (((j+1 : ℕ) : ℝ)*Real.exp x) := by positivity
    rw [show (j : ℝ)+1 = ((j+1 : ℕ) : ℝ) by push_cast; rfl,
      factorialMuntzSeed_of_pos n hp]
    have h4 := ramp_term_zero n (4*(n+1)) (j+1) (by omega) le_rfl hj' hx
    have h2 := ramp_term_zero n (2*(n+1)) (j+1) (by omega) (by omega) (by omega) hx
    have h1 := ramp_term_zero n (n+1) (j+1) (by omega) (by omega) (by omega) hx
    push_cast at h4 h2 h1 ⊢
    rw [h4, h2, h1]
    ring

/-- All positive-logarithmic values agree exactly, including integer atoms
and collar endpoints; no limit or unproved identification is used. -/
theorem factorialMuntzCompletion_eq_ramp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    factorialMuntzCompletion n x = sourceFactorialRamp (n+1) x := by
  have he : (∑ j ∈ Finset.Icc 1 (4*(n+1)), factorialMuntzSeed n ((j : ℝ)*Real.exp x)) =
      (∑ j ∈ Finset.Icc 1 (4*(n+1)), clampedRamp (sourceFactorialCollar (n+1))
        ((j : ℝ)*Real.exp x/((4*(n+1) : ℕ) : ℝ)))-
      4*(∑ j ∈ Finset.Icc 1 (2*(n+1)), clampedRamp (sourceFactorialCollar (n+1))
        ((j : ℝ)*Real.exp x/((2*(n+1) : ℕ) : ℝ)))+
      4*(∑ j ∈ Finset.Icc 1 (n+1), clampedRamp (sourceFactorialCollar (n+1))
        ((j : ℝ)*Real.exp x/((n+1 : ℕ) : ℝ))) := by
    have hp : ∀ j ∈ Finset.Icc 1 (4*(n+1)), 0 < (j : ℝ)*Real.exp x := by
      intro j hj
      have : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega)
      positivity
    rw [Finset.sum_congr rfl (fun j hj => factorialMuntzSeed_of_pos n (hp j hj))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h2 := sum_ramp_truncate n (2*(n+1)) (by omega) (by omega) hx
    have h1 := sum_ramp_truncate n (n+1) (by omega) (by omega) hx
    push_cast at h2 h1 ⊢
    rw [h2, h1]
  unfold factorialMuntzCompletion
  rw [factorialMuntzSum_eq_finset n hx, he]
  unfold sourceFactorialRamp rampBiNull smoothFactorialLift
  ring

theorem factorialMuntzCompletion_measurable (n : ℕ) : Measurable (factorialMuntzCompletion n) :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).measurable.mul
    ((factorialMuntzSum_measurable n).comp Real.continuous_exp.measurable)).div_const _

theorem factorialMuntzCompletion_abs_le (n : ℕ) (x : ℝ) :
    |factorialMuntzCompletion n x| ≤ 10*Real.exp (x/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  unfold factorialMuntzCompletion
  rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left (factorialMuntzSum_abs_le n (Real.exp x))
    (Real.exp_pos (x/2)).le]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
