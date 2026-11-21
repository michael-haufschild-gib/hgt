import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorPairOccupation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Occupation bounds in the critical zero-gate window

At complementary length `(log D + y) / D`, the expected number of
covering anchors converges to `exp (-y)`. The pair law gives a positive
lower bound on enclosure throughout this window.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def criticalDimension (n : ℕ) : ℝ := (2 : ℝ) ^ n

private theorem criticalDimension_pos (n : ℕ) : 0 < criticalDimension n := pow_pos (by norm_num) _

private theorem tendsto_criticalDimension : Tendsto criticalDimension atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

private theorem cast_criticalDimension_sub_one (n : ℕ) : ((2 ^ n - 1 : ℕ) : ℝ) = criticalDimension n - 1 := by
  have h : 1 ≤ (2 : ℕ) ^ n := one_le_pow₀ (by norm_num)
  simp only [criticalDimension, Nat.cast_sub h, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

private def criticalArcGap (y : ℝ) (n : ℕ) : ℝ := (Real.log (criticalDimension n) + y) / criticalDimension n

/-- The covering radius corresponding to a gap of `(log D + y) / D`,
clipped to the unit turn at finite dimension. -/
def zeroGateCriticalArcRadius (y : ℝ) (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (1 - criticalArcGap y n)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem tendsto_criticalArcGap (y : ℝ) : Tendsto (criticalArcGap y) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun n => (criticalDimension n)⁻¹) atTop (𝓝 0) := tendsto_criticalDimension.inv_tendsto_atTop
  change Tendsto (fun n => (Real.log (criticalDimension n) + y) / criticalDimension n) atTop (𝓝 0)
  simpa only [Function.comp_apply, div_eq_mul_inv, add_mul, mul_zero, add_zero] using
    (hlog.comp tendsto_criticalDimension).add (hinv.const_mul y)

private theorem eventually_criticalArcGap_mem (y : ℝ) : ∀ᶠ n in atTop, criticalArcGap y n ∈ Ioo (0 : ℝ) (1 / 2) := by
  have hlog : Tendsto (fun n => Real.log (criticalDimension n)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_criticalDimension
  filter_upwards [(tendsto_atTop.mp hlog) (1 - y),
    (tendsto_order.mp (tendsto_criticalArcGap y)).2 (1 / 2) (by norm_num)] with n hlarge hsmall
  exact ⟨div_pos (by linarith only [hlarge]) (criticalDimension_pos n), hsmall⟩

private theorem criticalArcRadius_eq_sub (y : ℝ) (n : ℕ)
    (h : criticalArcGap y n ∈ Ioo (0 : ℝ) (1 / 2)) :
    (zeroGateCriticalArcRadius y n : ℝ) = 1 - criticalArcGap y n := by
  change max 0 (min 1 (1 - criticalArcGap y n)) = _
  rw [min_eq_right (sub_le_self _ h.1.le), max_eq_right (by linarith only [h.2])]

/-- The complementary critical arc length eventually equals the unclipped length. -/
theorem eventually_zeroGateCriticalGap_eq (y : ℝ) :
    ∀ᶠ n in atTop, 1 - (zeroGateCriticalArcRadius y n : ℝ) =
      (Real.log ((2 : ℝ) ^ n) + y) / (2 : ℝ) ^ n := by
  filter_upwards [eventually_criticalArcGap_mem y] with n hn
  change 1 - (zeroGateCriticalArcRadius y n : ℝ) = criticalArcGap y n
  rw [criticalArcRadius_eq_sub y n hn, sub_sub_cancel]

/-- The complementary critical arc length vanishes as the register grows. -/
theorem tendsto_zeroGateCriticalGap (y : ℝ) :
    Tendsto (fun n => 1 - (zeroGateCriticalArcRadius y n : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_criticalArcGap y).congr'
  filter_upwards [eventually_zeroGateCriticalGap_eq y] with n hn
  exact hn.symm

private theorem tendsto_dimension_mul_criticalArcGap_sq (y : ℝ) :
    Tendsto (fun n => criticalDimension n * (criticalArcGap y n) ^ 2) atTop (𝓝 0) := by
  let a (n : ℕ) := (criticalDimension n) ^ (1 / 2 : ℝ)
  have ha : Tendsto a atTop atTop := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_criticalDimension
  have halog : Tendsto (fun n => Real.log (criticalDimension n) / a n) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp tendsto_criticalDimension
  have hainv : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) := ha.inv_tendsto_atTop
  have hsmall : Tendsto (fun n => (Real.log (criticalDimension n) + y) / a n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, add_mul, mul_zero, add_zero] using halog.add (hainv.const_mul y)
  have hsq := hsmall.pow 2
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  apply hsq.congr
  intro n
  have had : (a n) ^ 2 = criticalDimension n := by
    dsimp only [a]
    rw [pow_two, ← Real.rpow_add (criticalDimension_pos n), show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [div_pow, had]
  dsimp only [criticalArcGap]
  field_simp [(criticalDimension_pos n).ne']

private theorem log_one_sub_add_bounds {s : ℝ} (hs : s < 1 / 2) :
    -2 * s ^ 2 ≤ Real.log (1 - s) + s ∧ Real.log (1 - s) + s ≤ 0 := by
  have hp : 0 < 1 - s := by linarith only [hs]
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  have hi : (1 - s)⁻¹ - 1 = s / (1 - s) := by
    apply (eq_div_iff hp.ne').mpr
    rw [sub_mul, inv_mul_cancel₀ hp.ne', one_mul, sub_sub_cancel]
  rw [Real.log_inv, hi] at hl
  have hdiff : s / (1 - s) - s = s ^ 2 / (1 - s) := by
    apply (eq_div_iff hp.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    ring
  have hratio : s ^ 2 / (1 - s) ≤ 2 * s ^ 2 := by
    have h := (div_le_iff₀ hp).mpr (by linarith only [hs] : 1 ≤ 2 * (1 - s))
    calc
      _ = s ^ 2 * (1 / (1 - s)) := by rw [← mul_div_assoc, mul_one]
      _ ≤ s ^ 2 * 2 := mul_le_mul_of_nonneg_left h (sq_nonneg s)
      _ = _ := mul_comm _ _
  exact ⟨by linarith only [hl, hdiff, hratio], by linarith only [hu]⟩

/-- For any fixed number of anchors the power of the remaining arc length
balances the matching power of the register dimension in the critical window. -/
theorem tendsto_zeroGateCriticalAnchorPower (m : ℕ) (y : ℝ) :
    Tendsto (fun n : ℕ => (((2 : ℝ) ^ n) ^ m) *
      (1 - (m : ℝ) * ((Real.log ((2 : ℝ) ^ n) + y) / (2 : ℝ) ^ n)) ^ (2 ^ n - 1))
      atTop (𝓝 (Real.exp (-((m : ℝ) * y)))) := by
  let s (n : ℕ) := (m : ℝ) * criticalArcGap y n
  have hs : Tendsto s atTop (𝓝 0) := by
    change Tendsto (fun n => (m : ℝ) * criticalArcGap y n) atTop (𝓝 0)
    simpa only [mul_zero] using (tendsto_criticalArcGap y).const_mul (m : ℝ)
  have hsmall : ∀ᶠ n in atTop, s n < 1 / 2 := (tendsto_order.mp hs).2 _ (by norm_num)
  have hsq : Tendsto (fun n => criticalDimension n * (s n) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_dimension_mul_criticalArcGap_sq y).const_mul ((m : ℝ) ^ 2)
    rw [mul_zero] at h
    apply h.congr
    intro n
    dsimp only [s]
    ring
  let err (n : ℕ) := (m : ℝ) * Real.log (criticalDimension n) +
    ((2 ^ n - 1 : ℕ) : ℝ) * Real.log (1 - s n) + (m : ℝ) * y
  have herr : Tendsto err atTop (𝓝 0) := by
    have hlo : Tendsto (fun n => s n - 2 * (criticalDimension n * (s n) ^ 2))
        atTop (𝓝 0) := by
      simpa only [mul_zero, sub_zero] using hs.sub (hsq.const_mul 2)
    have hcenter (n : ℕ) : criticalDimension n * s n = (m : ℝ) * (Real.log (criticalDimension n) + y) := by
      dsimp only [s, criticalArcGap]
      rw [mul_comm (criticalDimension n), mul_assoc, div_mul_cancel₀ _ (criticalDimension_pos n).ne']
    have hstate (n : ℕ) : err n = ((2 ^ n - 1 : ℕ) : ℝ) * (Real.log (1 - s n) + s n) + s n := by
      dsimp only [err]
      rw [cast_criticalDimension_sub_one]
      linear_combination -(hcenter n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hs ?_ ?_
    · filter_upwards [hsmall] with n hn
      rw [hstate n]
      have h := mul_le_mul_of_nonneg_left (log_one_sub_add_bounds hn).1
        (Nat.cast_nonneg (2 ^ n - 1) : (0 : ℝ) ≤ ((2 ^ n - 1 : ℕ) : ℝ))
      have hd : ((2 ^ n - 1 : ℕ) : ℝ) ≤ criticalDimension n := by
        rw [cast_criticalDimension_sub_one]
        exact sub_le_self _ zero_le_one
      have hw := mul_le_mul_of_nonpos_right hd
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) (sq_nonneg (s n)))
      linarith only [h, hw]
    · filter_upwards [hsmall] with n hn
      rw [hstate n]
      exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (log_one_sub_add_bounds hn).2)
  have he := Real.continuous_exp.continuousAt.tendsto.comp (herr.sub_const ((m : ℝ) * y))
  rw [zero_sub] at he
  apply he.congr'
  filter_upwards [hsmall] with n hn
  have hp : 0 < 1 - s n := by linarith only [hn]
  change Real.exp (err n - (m : ℝ) * y) = criticalDimension n ^ m * (1 - s n) ^ (2 ^ n - 1)
  dsimp only [err]
  rw [add_sub_cancel_right, Real.exp_add, ← Real.log_pow (criticalDimension n) m,
    Real.exp_log (pow_pos (criticalDimension_pos n) _), ← Real.log_pow (1 - s n) (2 ^ n - 1),
    Real.exp_log (pow_pos hp _)]

/-- The mean number of anchors in the critical window converges to `exp (-y)`. -/
theorem tendsto_zeroGateCriticalAnchorMean (y : ℝ) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * (zeroGateCriticalArcRadius y n : ℝ) ^ (2 ^ n - 1))
      atTop (𝓝 (Real.exp (-y))) := by
  have h := tendsto_zeroGateCriticalAnchorPower 1 y
  simp only [Nat.cast_one, one_mul, pow_one] at h
  apply h.congr'
  filter_upwards [eventually_criticalArcGap_mem y] with n hn
  change (2 : ℝ) ^ n * (1 - criticalArcGap y n) ^ (2 ^ n - 1) =
    (2 : ℝ) ^ n * (zeroGateCriticalArcRadius y n : ℝ) ^ (2 ^ n - 1)
  rw [criticalArcRadius_eq_sub y n hn]

/-- The mean number of ordered pairs of distinct covering anchors converges
to the square of the mean for individual anchors. -/
theorem tendsto_zeroGateCriticalAnchorPairMean (y : ℝ) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1) *
      (2 * (zeroGateCriticalArcRadius y n : ℝ) - 1) ^ (2 ^ n - 1)) atTop (𝓝 (Real.exp (-(2 * y)))) := by
  have hpow : Tendsto (fun n : ℕ => (criticalDimension n) ^ 2 *
      (2 * (zeroGateCriticalArcRadius y n : ℝ) - 1) ^ (2 ^ n - 1)) atTop (𝓝 (Real.exp (-(2 * y)))) := by
    have h := tendsto_zeroGateCriticalAnchorPower 2 y
    rw [Nat.cast_ofNat] at h
    apply h.congr'
    filter_upwards [eventually_criticalArcGap_mem y] with n hn
    have hrad : 2 * (zeroGateCriticalArcRadius y n : ℝ) - 1 = 1 - 2 * criticalArcGap y n := by
      rw [criticalArcRadius_eq_sub y n hn]
      ring
    change criticalDimension n ^ 2 * (1 - 2 * criticalArcGap y n) ^ (2 ^ n - 1) =
      criticalDimension n ^ 2 * (2 * (zeroGateCriticalArcRadius y n : ℝ) - 1) ^ (2 ^ n - 1)
    rw [hrad]
  have hinv : Tendsto (fun n => (criticalDimension n)⁻¹) atTop (𝓝 0) := tendsto_criticalDimension.inv_tendsto_atTop
  have hnorm : Tendsto (fun n => 1 - (criticalDimension n)⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero] using hinv.const_sub 1
  have h := hnorm.mul hpow
  rw [one_mul] at h
  apply h.congr
  intro n
  have hscale : (1 - (criticalDimension n)⁻¹) * (criticalDimension n) ^ 2 =
      criticalDimension n * (criticalDimension n - 1) := by
    rw [sub_mul, one_mul, pow_two, ← mul_assoc, inv_mul_cancel₀ (criticalDimension_pos n).ne', one_mul, mul_sub, mul_one]
  change (1 - (criticalDimension n)⁻¹) * (criticalDimension n ^ 2 * _) =
    (criticalDimension n * (criticalDimension n - 1)) * _
  rw [← mul_assoc, hscale]

/-- In the critical window the anchor mean and its second moment bound the
limiting occupation from above and from below, respectively. -/
theorem eventually_zeroGateCriticalArcMass_bounds (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Real.exp (-y) / (1 + Real.exp (-y)) - ε ≤
        zeroGateFullArcMass n (zeroGateCriticalArcRadius y n) ∧
      zeroGateFullArcMass n (zeroGateCriticalArcRadius y n) ≤ min 1 (Real.exp (-y) + ε) := by
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  let q (n : ℕ) := (2 : ℝ) ^ n * (zeroGateCriticalArcRadius y n : ℝ) ^ (2 ^ n - 1)
  have hq : Tendsto q atTop (𝓝 (Real.exp (-y))) := tendsto_zeroGateCriticalAnchorMean y
  have hsum : Tendsto (fun n => 1 + q n) atTop (𝓝 (1 + Real.exp (-y))) := hq.const_add 1
  have hlim := hq.div hsum (by positivity : 1 + Real.exp (-y) ≠ 0)
  have hl := (tendsto_order.mp hlim).1 _ (sub_lt_self _ hε)
  have hu := (tendsto_order.mp hq).2 _ (lt_add_of_pos_right _ hε)
  filter_upwards [hl, hu, eventually_criticalArcGap_mem y] with n hlow hupp hc
  have hr : (zeroGateCriticalArcRadius y n : ℝ) ∈ Ico (1 / 2 : ℝ) 1 := by
    rw [criticalArcRadius_eq_sub y n hc]
    exact ⟨by linarith only [hc.2], sub_lt_self _ hc.1⟩
  let r : Ico (1 / 2 : ℝ) 1 := ⟨zeroGateCriticalArcRadius y n, hr⟩
  have hprob : zeroGateFullArcMass n (zeroGateCriticalArcRadius y n) ≤ 1 := by
    change (volume (relativeEnclosingUnitArc (fun _ : Fin n => false) (zeroGateCriticalArcRadius y n))).toReal ≤ 1
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) prob_le_one
  exact ⟨hlow.le.trans (zeroGateFullArcMass_ge_anchorMean n r),
    le_min hprob ((zeroGateFullArcMass_bounds n (zeroGateCriticalArcRadius y n)).2.trans hupp.le)⟩

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Almost surely the prefix-wise limits of actual zero-gate return times
obey the critical-window bounds on the same Gaussian chain. -/
theorem gaussian_path_zeroGateCriticalArcOccupation_bounds :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ y a : ℝ,
      (∀ k : ℕ,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        let r := zeroGateCriticalArcRadius y (k + 3)
        Tendsto (fun T => volume.real (zeroGateReturnSet H r ∩ Icc a T) / (T - a)) atTop
          (𝓝 (zeroGateFullArcMass (k + 3) r))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        Real.exp (-y) / (1 + Real.exp (-y)) - ε ≤
          zeroGateFullArcMass (k + 3) (zeroGateCriticalArcRadius y (k + 3)) ∧
        zeroGateFullArcMass (k + 3) (zeroGateCriticalArcRadius y (k + 3)) ≤ min 1 (Real.exp (-y) + ε) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro y a
  have hshift : Tendsto (fun k : ℕ => k + 3) atTop atTop :=
    tendsto_atTop.mpr fun b => (eventually_ge_atTop b).mono fun k hk => by omega
  exact ⟨fun k => hω k (zeroGateCriticalArcRadius y (k + 3)) a,
    fun _ hε => hshift.eventually (eventually_zeroGateCriticalArcMass_bounds y hε)⟩

#print axioms tendsto_zeroGateCriticalAnchorMean
#print axioms tendsto_zeroGateCriticalAnchorPower
#print axioms tendsto_zeroGateCriticalAnchorPairMean
#print axioms eventually_zeroGateCriticalArcMass_bounds
#print axioms gaussian_path_zeroGateCriticalArcOccupation_bounds

end

end GaloisForLFunctions.HTGeometry
