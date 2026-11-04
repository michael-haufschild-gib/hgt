import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeScaleLimits
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeBoundaryCorrection

/-!
# Polynomial conductor and horizon scales

Integer powers realize fixed logarithmic conductor ratios without floor
errors. The prime Mertens mass reads each exponent exactly in the limit,
and the finite cofactor boundary supplies the half-charge correction.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory

/-- A prime cutoff `X^a` has Mertens mass asymptotic to `a log X`. -/
theorem tendsto_primePoleScale_pow_div_log (a : ℕ) :
    Tendsto (fun X : ℕ => primePoleScale (X ^ a) / Real.log X) atTop (𝓝 (a : ℝ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ (hlog.const_div_atTop
    ((Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)))
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hid : primePoleScale (X ^ a) / Real.log X - (a : ℝ) =
      (primePoleScale (X ^ a) - Real.log (X ^ a : ℕ)) / Real.log X := by
    rw [Nat.cast_pow, Real.log_pow]
    field_simp [hL.ne']
  rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right
    (primePoleScale_logarithmic (Nat.one_le_pow a X (by omega))) hL.le

/-- Ratios of prime Mertens masses recover ratios of positive cutoff exponents. -/
theorem tendsto_primePoleScale_pow_ratio {a : ℕ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun X : ℕ => primePoleScale (X ^ d) / primePoleScale (X ^ a))
      atTop (𝓝 ((d : ℝ) / a)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := (tendsto_primePoleScale_pow_div_log d).div
    (tendsto_primePoleScale_pow_div_log a) haR
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hL : (Real.log (X : ℝ)) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  rw [Pi.div_apply]
  field_simp [hL, (primePoleScale_pos hQ).ne']

/-- The horizon logarithm divided by the cutoff mass reads the exact exponent ratio. -/
theorem tendsto_log_pow_div_primePoleScale_pow {a : ℕ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun X : ℕ => Real.log (X ^ d : ℕ) / primePoleScale (X ^ a))
      atTop (𝓝 ((d : ℝ) / a)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := (tendsto_const_nhds (x := (d : ℝ))).div
    (tendsto_primePoleScale_pow_div_log a) haR
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hL : (Real.log (X : ℝ)) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  rw [Pi.div_apply, Nat.cast_pow, Real.log_pow]
  field_simp [hL, (primePoleScale_pos hQ).ne']

/-- Every fixed polynomial horizon retains the same signed cofactor boundary. -/
theorem tendsto_harmonicPrimeCharge_polynomial_dilation_energy {a d : ℕ}
    (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      jumpEnergy (X ^ d) (normalizedConductorPacket (X ^ a)
        (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  have hQa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hboundary : Tendsto (fun X : ℕ =>
      jumpEnergy (X ^ d) (normalizedConductorPacket (X ^ a)
        (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) -
        (t ^ 2 / primePoleScale (X ^ a)) * Real.log (X ^ d : ℕ))
        atTop (𝓝 (-(t ^ 2 / 2))) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_
      ((primePoleScale_tendsto_atTop.comp hQa).const_div_atTop
        (primeChargeBoundaryConstant * t ^ 2))
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, Function.comp_def] using
      harmonicPrimeCharge_boundary_error_le hQ (Nat.pow_le_pow_right (by omega) had) t
  have h := hboundary.add ((tendsto_log_pow_div_primePoleScale_pow ha d).const_mul (t ^ 2))
  convert h using 1
  · funext X
    ring
  · ring

/-- The same reciprocal-prime moment absorbs sublogarithmic costs at every fixed polynomial scale. -/
theorem tendsto_primeChargePolynomialMoment_cost {a d : ℕ}
    (ha : 0 < a) (had : a ≤ d) (t : ℝ) {r : ℝ} (hr : r < 1) :
    Tendsto (fun X : ℕ =>
      Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1) *
        (t / primePoleScale (X ^ a)) ^ 2 *
        (4 * (∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ))) atTop (𝓝 0) := by
  have hd : 0 < d := ha.trans_le had
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop := tendsto_pow_atTop hd.ne'
  have hcost := ((tendsto_primePoleScale_pow_ratio ha d).pow 2).mul
    ((tendsto_primeChargeMoment_cost t hr).comp hNd)
  simp only [mul_zero] at hcost
  refine squeeze_zero_norm' ?_ hcost
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hQa : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hNd2 : 2 ≤ X ^ d := hX.trans (Nat.le_pow hd)
  have hQN := Nat.pow_le_pow_right (by omega : 0 < X) had
  have hS : (∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ)) ≤
      ∑ p ∈ (Icc 1 (X ^ d)).filter Nat.Prime, 1 / (p : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpX, hpprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨(mem_Icc.mp hpX).1, (mem_Icc.mp hpX).2.trans hQN⟩, hpprime⟩
    · intro p _ _
      positivity
  have hS0 : 0 ≤ ∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ) :=
    sum_nonneg fun p _ => by positivity
  have hquad := add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2)
    (by norm_num : (0 : ℝ) ≤ 4)) (mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1) *
      (t / primePoleScale (X ^ a)) ^ 2 by positivity)
  refine h.trans_eq ?_
  dsimp only [Function.comp_def]
  field_simp [(primePoleScale_pos hQa).ne', (primePoleScale_pos hNd2).ne']

#print axioms tendsto_harmonicPrimeCharge_polynomial_dilation_energy
#print axioms tendsto_primeChargePolynomialMoment_cost

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
