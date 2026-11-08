import GaloisForLFunctions.SelbergClass.Primon.SemicircleEdgeMoments

/-!
# Every-order expansion of finite-prime moments at the spectral edge

The density ratio is `M/(1+aδ)`, with `δ = 4-x²`,
`M = p(p+1)/(p-1)²`, and `a = p/(p-1)²`. Its finite geometric expansion
has a remainder of prescribed sign at every order. Integrating gives
explicit approximations to each normalized even moment, with positive
remainders bounded by the mixed Wallis products.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The ratio of prime and semicircle densities at the spectral endpoints. -/
def kestenEdgeScale (p : Nat.Primes) : ℝ := (p : ℝ) * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2

/-- The coefficient of the edge gap in the normalized density denominator. -/
def kestenEdgeSlope (p : Nat.Primes) : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2

/-- The endpoint density ratio is positive. -/
theorem kestenEdgeScale_pos (p : Nat.Primes) : 0 < kestenEdgeScale p := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  unfold kestenEdgeScale
  exact div_pos (by positivity) (sq_pos_of_pos (by linarith only [hp]))

/-- The density denominator increases strictly with the edge gap. -/
theorem kestenEdgeSlope_pos (p : Nat.Primes) : 0 < kestenEdgeSlope p := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  unfold kestenEdgeSlope
  exact div_pos (by positivity) (sq_pos_of_pos (by linarith only [hp]))

/-- The prime density is a one-pole rational reweighting of the semicircle density. -/
theorem kestenDensity_edge_identity (p : Nat.Primes) (t : ℝ) :
    (1 + kestenEdgeSlope p * phaseEdgeGap t) * kestenMcKayDensity p t =
      kestenEdgeScale p * semicirclePhaseDensity t := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  have h := kestenDensity_quadratic_transform p t
  unfold kestenEdgeScale kestenEdgeSlope phaseEdgeGap
  field_simp [hp1]
  nlinarith only [h]

/-- The endpoint ratio bounds the density ratio everywhere. -/
theorem kestenDensity_le_edgeScale (p : Nat.Primes) (t : ℝ) :
    kestenMcKayDensity p t ≤ kestenEdgeScale p * semicirclePhaseDensity t := by
  have h := kestenDensity_edge_identity p t
  have hn : 0 ≤ kestenEdgeSlope p * phaseEdgeGap t * kestenMcKayDensity p t :=
    mul_nonneg (mul_nonneg (kestenEdgeSlope_pos p).le (phaseEdgeGap_nonneg t))
      (kestenMcKayDensity_nonneg p t)
  nlinarith only [h, hn]

/-- Prime phase moments weighted by a power of the spectral edge gap. -/
def kestenEdgeMoment (p : Nat.Primes) (n k : ℕ) : ℝ :=
  ∫ t in Set.Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
    ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)

private theorem edgeWeight_nonneg (n k : ℕ) (t : ℝ) :
    0 ≤ (2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k := by
  rw [pow_mul]
  exact mul_nonneg (pow_nonneg (sq_nonneg _) n) (pow_nonneg (phaseEdgeGap_nonneg t) k)

private theorem continuous_edgeWeight (n k : ℕ) :
    Continuous (fun t : ℝ => (2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k) := by
  have hx : Continuous (fun t : ℝ => (2 * Real.cos (Real.pi * t)) ^ (2 * n)) := by fun_prop
  exact hx.mul (continuous_phaseEdgeGap.pow k)

private theorem integrable_kestenEdgeWeight (p : Nat.Primes) (n k : ℕ) :
    IntegrableOn (fun t : ℝ => kestenMcKayDensity p t *
      ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)) (Set.Ioo 0 1) :=
  ((continuous_kestenMcKayDensity p).mul (continuous_edgeWeight n k)).continuousOn.integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self

private theorem integrable_semicircleEdgeWeight (n k : ℕ) :
    IntegrableOn (fun t : ℝ => semicirclePhaseDensity t *
      ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)) (Set.Ioo 0 1) := by
  have hs : Continuous semicirclePhaseDensity := by unfold semicirclePhaseDensity; fun_prop
  exact (hs.mul (continuous_edgeWeight n k)).continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

/-- Zeroth edge weight recovers the even prime-phase moment. -/
theorem kestenEdgeMoment_zero (p : Nat.Primes) (n : ℕ) :
    kestenEdgeMoment p n 0 = kestenMoment p (2 * n) := by
  simp only [kestenEdgeMoment, pow_zero, mul_one, kestenMoment]

/-- All edge-weighted prime moments are nonnegative. -/
theorem kestenEdgeMoment_nonneg (p : Nat.Primes) (n k : ℕ) : 0 ≤ kestenEdgeMoment p n k :=
  integral_nonneg fun t => mul_nonneg (kestenMcKayDensity_nonneg p t) (edgeWeight_nonneg n k t)

/-- The endpoint density ratio controls all edge-weighted moments simultaneously. -/
theorem kestenEdgeMoment_le (p : Nat.Primes) (n k : ℕ) :
    kestenEdgeMoment p n k ≤ kestenEdgeScale p * semicircleEdgeMoment n k := by
  unfold kestenEdgeMoment semicircleEdgeMoment
  rw [← integral_const_mul]
  apply integral_mono (integrable_kestenEdgeWeight p n k)
    ((integrable_semicircleEdgeWeight n k).const_mul _)
  intro t
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (kestenDensity_le_edgeScale p t) (edgeWeight_nonneg n k t)

/-- One edge weight transfers the rational density relation to actual integrals. -/
theorem kestenEdgeMoment_step (p : Nat.Primes) (n k : ℕ) :
    kestenEdgeMoment p n k + kestenEdgeSlope p * kestenEdgeMoment p n (k + 1) =
      kestenEdgeScale p * semicircleEdgeMoment n k := by
  have he : (fun t : ℝ => kestenMcKayDensity p t *
      ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k) +
      kestenEdgeSlope p * (kestenMcKayDensity p t *
        ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ (k + 1)))) =
      fun t => kestenEdgeScale p * (semicirclePhaseDensity t *
        ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k)) := by
    funext t
    rw [pow_succ]
    linear_combination ((2 * Real.cos (Real.pi * t)) ^ (2 * n) * phaseEdgeGap t ^ k) *
      (kestenDensity_edge_identity p t)
  have h := congrArg (fun f : ℝ → ℝ => ∫ t in Set.Ioo (0 : ℝ) 1, f t) he
  rw [integral_add (integrable_kestenEdgeWeight p n k)
    ((integrable_kestenEdgeWeight p n (k + 1)).const_mul _),
    integral_const_mul, integral_const_mul] at h
  exact h

/-- Every finite geometric expansion has an exact edge-moment remainder. -/
theorem kestenMoment_edge_expansion (p : Nat.Primes) (n K : ℕ) :
    kestenMoment p (2 * n) =
      kestenEdgeScale p * (∑ j ∈ range K, (-kestenEdgeSlope p) ^ j * semicircleEdgeMoment n j) +
        (-kestenEdgeSlope p) ^ K * kestenEdgeMoment p n K := by
  induction K with
  | zero => simp only [sum_range_zero, pow_zero, mul_zero, one_mul, zero_add, kestenEdgeMoment_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linear_combination ih + (-kestenEdgeSlope p) ^ K * (kestenEdgeMoment_step p n K)

/-- Even prime moment normalized by its Catalan counterpart. -/
def kestenMomentRatio (p : Nat.Primes) (n : ℕ) : ℝ := kestenMoment p (2 * n) / (catalan n : ℝ)

/-- The finite endpoint expansion through orders strictly below `K`. -/
def kestenEdgeApproximation (p : Nat.Primes) (n K : ℕ) : ℝ :=
  kestenEdgeScale p * (∑ j ∈ range K, (-kestenEdgeSlope p) ^ j * semicircleEdgeMoment n j) /
    (catalan n : ℝ)

/-- The positive magnitude of the order-`K` alternating remainder. -/
def kestenEdgeRemainder (p : Nat.Primes) (n K : ℕ) : ℝ :=
  kestenEdgeSlope p ^ K * kestenEdgeMoment p n K / (catalan n : ℝ)

/-- The approximation error has the exact alternating sign and edge-moment magnitude. -/
theorem kestenMomentRatio_eq_edgeApproximation_add (p : Nat.Primes) (n K : ℕ) :
    kestenMomentRatio p n = kestenEdgeApproximation p n K + (-1 : ℝ) ^ K * kestenEdgeRemainder p n K := by
  have hpow : (-kestenEdgeSlope p) ^ K = (-1 : ℝ) ^ K * kestenEdgeSlope p ^ K := by
    rw [← mul_pow]
    congr 1
    ring
  unfold kestenMomentRatio kestenEdgeApproximation kestenEdgeRemainder
  rw [kestenMoment_edge_expansion p n K, hpow]
  ring

/-- Every alternating remainder magnitude is nonnegative. -/
theorem kestenEdgeRemainder_nonneg (p : Nat.Primes) (n K : ℕ) : 0 ≤ kestenEdgeRemainder p n K :=
  div_nonneg (mul_nonneg (pow_nonneg (kestenEdgeSlope_pos p).le K)
    (kestenEdgeMoment_nonneg p n K)) (catalan_real_pos n).le

/-- A normalized Wallis moment controls each alternating remainder. -/
theorem kestenEdgeRemainder_le_moment (p : Nat.Primes) (n K : ℕ) :
    kestenEdgeRemainder p n K ≤ kestenEdgeScale p * kestenEdgeSlope p ^ K *
      (semicircleEdgeMoment n K / (catalan n : ℝ)) := by
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (kestenEdgeMoment_le p n K) (pow_nonneg (kestenEdgeSlope_pos p).le K))
    (catalan_real_pos n).le
  unfold kestenEdgeRemainder
  calc
    _ ≤ kestenEdgeSlope p ^ K * (kestenEdgeScale p * semicircleEdgeMoment n K) / (catalan n : ℝ) := h
    _ = _ := by ring

/-- Every-order explicit inverse-power bound for the alternating remainder. -/
theorem kestenEdgeRemainder_le (p : Nat.Primes) (n K : ℕ) :
    kestenEdgeRemainder p n K ≤
      kestenEdgeScale p * kestenEdgeSlope p ^ K * semicircleEdgeCoefficient K / ((n : ℝ) + 2) ^ K := by
  calc
    _ ≤ kestenEdgeScale p * kestenEdgeSlope p ^ K *
        (semicircleEdgeMoment n K / (catalan n : ℝ)) := kestenEdgeRemainder_le_moment p n K
    _ ≤ kestenEdgeScale p * kestenEdgeSlope p ^ K *
        (semicircleEdgeCoefficient K / ((n : ℝ) + 2) ^ K) :=
      mul_le_mul_of_nonneg_left (semicircleEdgeMoment_ratio_le n K) (by
        exact mul_nonneg (kestenEdgeScale_pos p).le (pow_nonneg (kestenEdgeSlope_pos p).le K))
    _ = _ := by ring

/-- Consecutive positive remainders partition one explicit Wallis term. -/
theorem kestenEdgeRemainder_step (p : Nat.Primes) (n K : ℕ) :
    kestenEdgeRemainder p n K + kestenEdgeRemainder p n (K + 1) =
      kestenEdgeScale p * kestenEdgeSlope p ^ K * (semicircleEdgeMoment n K / (catalan n : ℝ)) := by
  unfold kestenEdgeRemainder
  rw [pow_succ]
  linear_combination (kestenEdgeSlope p ^ K / (catalan n : ℝ)) * (kestenEdgeMoment_step p n K)

/-- At order zero the positive remainder is the whole normalized moment. -/
theorem kestenEdgeRemainder_zero (p : Nat.Primes) (n : ℕ) :
    kestenEdgeRemainder p n 0 = kestenMomentRatio p n := by
  simp only [kestenEdgeRemainder, pow_zero, one_mul, kestenEdgeMoment_zero, kestenMomentRatio]

/-- The empty endpoint approximation is zero. -/
theorem kestenEdgeApproximation_zero (p : Nat.Primes) (n : ℕ) : kestenEdgeApproximation p n 0 = 0 := by
  simp only [kestenEdgeApproximation, sum_range_zero, mul_zero, zero_div]

/-- The first endpoint approximation is the endpoint density ratio. -/
theorem kestenEdgeApproximation_one (p : Nat.Primes) (n : ℕ) :
    kestenEdgeApproximation p n 1 = kestenEdgeScale p := by
  simp only [kestenEdgeApproximation, sum_range_one, pow_zero, one_mul, semicircleEdgeMoment_zero]
  field_simp [(catalan_real_pos n).ne']

/-- The first positive remainder is the gap below the endpoint density ratio. -/
theorem kestenEdgeRemainder_one (p : Nat.Primes) (n : ℕ) :
    kestenEdgeRemainder p n 1 = kestenEdgeScale p - kestenMomentRatio p n := by
  have h := kestenEdgeRemainder_step p n 0
  rw [kestenEdgeRemainder_zero, pow_zero, mul_one, semicircleEdgeMoment_zero,
    div_self (catalan_real_pos n).ne', mul_one] at h
  linarith only [h]

/-- Absolute error bound for every finite endpoint expansion. -/
theorem abs_kestenMomentRatio_sub_edgeApproximation_le (p : Nat.Primes) (n K : ℕ) :
    |kestenMomentRatio p n - kestenEdgeApproximation p n K| ≤
      kestenEdgeScale p * kestenEdgeSlope p ^ K * semicircleEdgeCoefficient K / ((n : ℝ) + 2) ^ K := by
  have he : kestenMomentRatio p n - kestenEdgeApproximation p n K =
      (-1 : ℝ) ^ K * kestenEdgeRemainder p n K := by
    linarith only [kestenMomentRatio_eq_edgeApproximation_add p n K]
  rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (kestenEdgeRemainder_nonneg p n K)]
  exact kestenEdgeRemainder_le p n K

/-- The normalized moment lies below the endpoint ratio with an explicit first-order gap. -/
theorem kestenMomentRatio_edge_bounds (p : Nat.Primes) (n : ℕ) :
    0 ≤ kestenEdgeScale p - kestenMomentRatio p n ∧
      kestenEdgeScale p - kestenMomentRatio p n ≤
        6 * kestenEdgeScale p * kestenEdgeSlope p / ((n : ℝ) + 2) := by
  rw [← kestenEdgeRemainder_one]
  refine ⟨kestenEdgeRemainder_nonneg p n 1, ?_⟩
  have h := kestenEdgeRemainder_le_moment p n 1
  rw [pow_one, semicircleEdgeMoment_ratio_one] at h
  convert h using 1
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
