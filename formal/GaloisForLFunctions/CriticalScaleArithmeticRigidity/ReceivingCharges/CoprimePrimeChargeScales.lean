import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePolynomialScales

/-!
# Coherent fibre moments at polynomial scales

Deleting the finitely many primes of a fixed conductor changes prime
Mertens mass by a bounded amount. The fibre normalizer is asymptotically
the scalar normalizer, and every sublogarithmic moment cost still vanishes.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

/-- Restricting to primes coprime to a conductor only decreases the prime Mertens mass. -/
theorem fibreScale_le_primePoleScale (m Q : ℕ) : fibreScale m Q ≤ primePoleScale Q := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hpP, -⟩ := mem_fibrePrimes.mp hp
    exact mem_filter.mpr ⟨hpI, hpP⟩
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- A fixed conductor's excluded prime mass disappears relative to its fibre normalizer. -/
theorem tendsto_primePoleScale_div_fibreScale {m : ℕ} (hm : 0 < m) :
    Tendsto (fun Q : ℕ => primePoleScale Q / fibreScale m Q) atTop (𝓝 1) := by
  have hB := fibreScale_tendsto_atTop hm
  have hdiff : Tendsto (fun Q : ℕ =>
      (primePoleScale Q - fibreScale m Q) / fibreScale m Q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hB.const_div_atTop (fibreLoss m))
    filter_upwards [hB.eventually (eventually_ge_atTop 1)] with Q hQ
    have hQ0 : 0 < fibreScale m Q := zero_lt_one.trans_le hQ
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sub_nonneg.mpr (fibreScale_le_primePoleScale m Q)), abs_of_pos hQ0]
    apply div_le_div_of_nonneg_right _ hQ0.le
    have h := fibreScale_ge hm Q
    linarith only [h]
  have h := hdiff.add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hB.eventually (eventually_ge_atTop 1)] with Q hQ
  field_simp [(zero_lt_one.trans_le hQ).ne']
  ring

/-- Fibre reciprocal-prime mass is bounded by the scalar one. -/
theorem fibreReciprocal_le (m Q : ℕ) :
    (∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ)) ≤
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hpP, -⟩ := mem_fibrePrimes.mp hp
    exact mem_filter.mpr ⟨hpI, hpP⟩
  · intro p _ _
    positivity

/-- The fibre moment cost differs only by the fixed mode bound and its normalizer ratio. -/
theorem fibreChargeMoment_le_scalar {Q : ℕ} (hQ : 2 ≤ Q) (m : ℕ)
    (hB : 0 < fibreScale m Q) (t : ℝ) :
    fibreChargeMoment m Q t ≤ modeBound m ^ 2 * (primePoleScale Q / fibreScale m Q) ^ 2 *
      (t / primePoleScale Q) ^ 2 *
        (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  have hS := fibreReciprocal_le m Q
  have hS0 : 0 ≤ ∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ) :=
    sum_nonneg fun _ _ => by positivity
  have hquad := add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2) (by norm_num : (0 : ℝ) ≤ 4))
    (mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 2))
  have hscale : (t / fibreScale m Q) ^ 2 =
      (primePoleScale Q / fibreScale m Q) ^ 2 * (t / primePoleScale Q) ^ 2 := by
    field_simp [hB.ne', (primePoleScale_pos hQ).ne']
  calc
    _ ≤ modeBound m ^ 2 * (t / fibreScale m Q) ^ 2 *
        (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hquad (by positivity)
    _ = _ := by rw [hscale]; ring

/-- Every fixed coprime fibre absorbs each sublogarithmic critical-overlap moment cost. -/
theorem tendsto_fibreChargePolynomialMoment_cost {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) {r : ℝ} (hr : r < 1) :
    Tendsto (fun X : ℕ => Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1) *
      fibreChargeMoment m (X ^ a) t) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hratio := (tendsto_primePoleScale_div_fibreScale hm).comp hXa
  have hlim := ((tendsto_primeChargePolynomialMoment_cost ha had t hr).mul
    (hratio.pow 2)).const_mul (modeBound m ^ 2)
  simp only [zero_mul, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2,
    hB.eventually (eventually_ge_atTop 1)] with X hX hb
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hB0 : 0 < fibreScale m (X ^ a) := zero_lt_one.trans_le hb
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)
      (by positivity)) (fibreChargeMoment_nonneg _ _ _))]
  exact (mul_le_mul_of_nonneg_left (fibreChargeMoment_le_scalar hQ m hB0 t)
    (by positivity : 0 ≤ Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1))).trans_eq
      (by dsimp only [Function.comp_def]; ring)

/-- The coprime incidence packet alone has the same vanishing logarithmic moment costs. -/
theorem tendsto_fibreIncidencePolynomialMoment_cost {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) {r : ℝ} (hr : r < 1) :
    Tendsto (fun X : ℕ => Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1) *
      (t / fibreScale m (X ^ a)) ^ 2 *
        (4 * (∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_fibreChargePolynomialMoment_cost hm ha had t hr).const_mul
    ((modeBound m) ^ 2)⁻¹
  simp only [mul_zero] at h
  convert h using 1
  funext X
  unfold fibreChargeMoment
  field_simp [(modeBound_pos hm).ne']

/-- A polynomial horizon logarithm reads the same ratio through the fibre normalizer. -/
theorem tendsto_log_pow_div_fibreScale {m : ℕ} (hm : 0 < m) {a : ℕ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun X : ℕ => Real.log (X ^ d : ℕ) / fibreScale m (X ^ a))
      atTop (𝓝 ((d : ℝ) / a)) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have h := (tendsto_log_pow_div_primePoleScale_pow ha d).mul
    ((tendsto_primePoleScale_div_fibreScale hm).comp hXa)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  change (Real.log (X ^ d : ℕ) / primePoleScale (X ^ a)) *
    (primePoleScale (X ^ a) / fibreScale m (X ^ a)) = _
  field_simp [(primePoleScale_pos hQ).ne']

/-- Fixed excluded primes cost a vanishing logarithmic moment after coherent normalization. -/
theorem tendsto_fibreCharge_log_cost {m : ℕ} (hm : 0 < m) {a : ℕ}
    (ha : 0 < a) (d : ℕ) (t : ℝ) :
    Tendsto (fun X : ℕ => (Real.log (X ^ d : ℕ) + 1) *
      (t / fibreScale m (X ^ a)) ^ 2) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hi := ((fibreScale_tendsto_atTop hm).comp hXa).const_div_atTop (1 : ℝ)
  have h := (((tendsto_log_pow_div_fibreScale hm ha d).add hi).mul hi).const_mul (t ^ 2)
  simp only [mul_zero] at h
  convert h using 1
  funext X
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

#print axioms tendsto_primePoleScale_div_fibreScale
#print axioms tendsto_fibreChargePolynomialMoment_cost
#print axioms tendsto_fibreCharge_log_cost

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
