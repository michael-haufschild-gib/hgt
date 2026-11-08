import GaloisForLFunctions.SelbergClass.Primon.KestenMomentPolynomials

/-!
# Exact semicircle moments of the spectral edge gap

The gap `4-x²` in the coordinate `x = 2 cos(πt)` equals `4 sin²(πt)`.
Mixed Wallis integrals therefore evaluate all moments weighted by powers
of this gap. After normalization by the Catalan moment, the result is a
finite product, with an explicit inverse-power bound in the moment order.
-/

open MeasureTheory Set Finset
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Distance of the squared Hecke coordinate from its spectral maximum. -/
def phaseEdgeGap (t : ℝ) : ℝ := 4 - (2 * Real.cos (Real.pi * t)) ^ 2

/-- The spectral edge gap is four times the sine square. -/
theorem phaseEdgeGap_eq_sine_square (t : ℝ) :
    phaseEdgeGap t = 4 * Real.sin (Real.pi * t) ^ 2 := by
  unfold phaseEdgeGap
  nlinarith only [Real.sin_sq_add_cos_sq (Real.pi * t)]

/-- The edge gap is everywhere nonnegative. -/
theorem phaseEdgeGap_nonneg (t : ℝ) : 0 ≤ phaseEdgeGap t := by
  rw [phaseEdgeGap_eq_sine_square]
  positivity

/-- The edge gap is a continuous phase observable. -/
theorem continuous_phaseEdgeGap : Continuous phaseEdgeGap := by
  unfold phaseEdgeGap
  fun_prop

/-- Semicircle moments weighted by a power of the spectral edge gap. -/
def semicircleEdgeMoment (n k : ℕ) : ℝ :=
  ∫ t in Set.Ioo (0 : ℝ) 1, semicirclePhaseDensity t *
    ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)

/-- Catalan moments are strictly positive in every degree. -/
theorem catalan_real_pos (n : ℕ) : 0 < (catalan n : ℝ) := by
  have h := primonMomentValue_pos (0 : NNReal) n
  simpa only [NNReal.coe_zero, primonMomentValue_at_zero] using h

/-- No edge weighting gives the original Catalan moment. -/
theorem semicircleEdgeMoment_zero (n : ℕ) :
    semicircleEdgeMoment n 0 = (catalan n : ℝ) := by
  simp only [semicircleEdgeMoment, pow_zero, mul_one]
  exact semicircleMoment_even n

private theorem mixedEvenTrigHalf (m n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n)) =
      2 * mixedEvenTrigQuarterIntegral m n := by
  let f : ℝ → ℝ := fun x => Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hp : Function.Periodic f Real.pi := by
    intro x
    simp only [f, Real.sin_add_pi, Real.cos_add_pi, pow_mul, neg_sq]
  have hr (x : ℝ) : f (Real.pi - x) = f x := by
    simp only [f, Real.sin_pi_sub, Real.cos_pi_sub, pow_mul, neg_sq]
  have hq := integral_zero_two_pi_eq_four_mul_quarter hc hp hr
  have h2 := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) (0 : ℝ)
    (fun a b => hc.intervalIntegrable a b)
  have hh : (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
    convert h2 using 1 <;> norm_num
  change (∫ x in (0 : ℝ)..Real.pi, f x) =
    2 * ∫ x in (0 : ℝ)..Real.pi / 2, f x
  linarith only [hh, hq]

/-- Edge-weighted moments are mixed Wallis integrals with an explicit scale factor. -/
theorem semicircleEdgeMoment_eq_mixed (n k : ℕ) :
    semicircleEdgeMoment n k =
      (4 / Real.pi) * (4 : ℝ) ^ (n + k) * mixedEvenTrigQuarterIntegral (k + 1) n := by
  let f : ℝ → ℝ := fun x => Real.sin x ^ (2 * (k + 1)) * Real.cos x ^ (2 * n)
  have hpow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have he : (fun t : ℝ => semicirclePhaseDensity t *
      ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)) =
      fun t => (2 * (4 : ℝ) ^ (n + k)) * f (Real.pi * t) := by
    funext t
    dsimp [f]
    rw [semicirclePhaseDensity, phaseEdgeGap_eq_sine_square, mul_pow, mul_pow, hpow,
      show 2 * (k + 1) = 2 * k + 2 by omega,
      pow_add (Real.sin (Real.pi * t)) (2 * k) 2,
      pow_mul (Real.sin (Real.pi * t)) 2 k, pow_add (4 : ℝ) n k]
    ring
  unfold semicircleEdgeMoment
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f Real.pi_ne_zero]
  simp only [mul_zero, mul_one, smul_eq_mul]
  change (2 * (4 : ℝ) ^ (n + k)) * (Real.pi⁻¹ *
    ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * (k + 1)) * Real.cos x ^ (2 * n)) = _
  rw [mixedEvenTrigHalf]
  simp only [div_eq_mul_inv]
  ring

/-- One extra edge-gap factor multiplies the moment by an explicit rational factor. -/
theorem semicircleEdgeMoment_succ (n k : ℕ) :
    semicircleEdgeMoment n (k + 1) =
      (2 * (2 * (k : ℝ) + 3) / ((n : ℝ) + k + 2)) * semicircleEdgeMoment n k := by
  rw [semicircleEdgeMoment_eq_mixed, semicircleEdgeMoment_eq_mixed,
    mixedEvenTrigQuarterIntegral_succ (k + 1) n,
    show n + (k + 1) = (n + k) + 1 by omega, pow_succ]
  push_cast
  rw [show (k : ℝ) + 1 + n + 1 = (n : ℝ) + k + 2 by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every edge-gap moment is a Catalan number times an explicit finite product. -/
theorem semicircleEdgeMoment_eq_prod (n k : ℕ) :
    semicircleEdgeMoment n k = (catalan n : ℝ) *
      ∏ j ∈ range k, 2 * (2 * (j : ℝ) + 3) / ((n : ℝ) + j + 2) := by
  induction k with
  | zero => simp only [semicircleEdgeMoment_zero, prod_range_zero, mul_one]
  | succ k ih => rw [semicircleEdgeMoment_succ, ih, Finset.prod_range_succ]; ring

/-- All edge-gap moments are strictly positive. -/
theorem semicircleEdgeMoment_pos (n k : ℕ) : 0 < semicircleEdgeMoment n k := by
  rw [semicircleEdgeMoment_eq_prod]
  apply mul_pos (catalan_real_pos n)
  exact Finset.prod_pos fun j _ => by positivity

/-- The normalized edge-gap moment is a finite rational product. -/
theorem semicircleEdgeMoment_ratio (n k : ℕ) :
    semicircleEdgeMoment n k / (catalan n : ℝ) =
      ∏ j ∈ range k, 2 * (2 * (j : ℝ) + 3) / ((n : ℝ) + j + 2) := by
  rw [semicircleEdgeMoment_eq_prod, mul_div_cancel_left₀ _ (catalan_real_pos n).ne']

/-- The first normalized edge-gap moment is exactly `6/(n+2)`. -/
theorem semicircleEdgeMoment_ratio_one (n : ℕ) :
    semicircleEdgeMoment n 1 / (catalan n : ℝ) = 6 / ((n : ℝ) + 2) := by
  rw [semicircleEdgeMoment_ratio]
  norm_num

/-- The second normalized edge-gap moment is exactly `60/((n+2)(n+3))`. -/
theorem semicircleEdgeMoment_ratio_two (n : ℕ) :
    semicircleEdgeMoment n 2 / (catalan n : ℝ) =
      60 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  rw [semicircleEdgeMoment_ratio]
  norm_num [Finset.prod_range_succ]
  ring

/-- Numerator of the inverse-power bound for the normalized edge moments. -/
def semicircleEdgeCoefficient (k : ℕ) : ℝ := ∏ j ∈ range k, 2 * (2 * (j : ℝ) + 3)

/-- Edge coefficients are positive at every order, including order zero. -/
theorem semicircleEdgeCoefficient_pos (k : ℕ) : 0 < semicircleEdgeCoefficient k :=
  Finset.prod_pos fun j _ => by positivity

/-- The normalized gap moment has an explicit inverse-power bound in the moment order. -/
theorem semicircleEdgeMoment_ratio_le (n k : ℕ) :
    semicircleEdgeMoment n k / (catalan n : ℝ) ≤
      semicircleEdgeCoefficient k / ((n : ℝ) + 2) ^ k := by
  rw [semicircleEdgeMoment_ratio]
  calc
    _ ≤ ∏ j ∈ range k, 2 * (2 * (j : ℝ) + 3) / ((n : ℝ) + 2) := by
      apply Finset.prod_le_prod (fun j _ => by positivity)
      intro j _
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by have hj := Nat.cast_nonneg (α := ℝ) j; linarith only [hj])
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_range, semicircleEdgeCoefficient]

end
end GaloisForLFunctions.SelbergClass.Primon
