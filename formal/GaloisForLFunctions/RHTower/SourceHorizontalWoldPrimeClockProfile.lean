import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockCubic

/-!
# Full prime-clock profile of the source-horizontal Wold deformation

The cubic remnant is the first nonzero Taylor coefficient of a universal nonlinear profile.
This file first proves the all-order logarithmic Wold moment law needed for the profile.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural-cutoff logarithmic moment of arbitrary nonnegative integral order. -/
def sourceHorizontalWoldNaturalLogMoment (r X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 X,
    Real.log (n : ℝ) ^ r * xiHeatCassiniWoldNatWeight n

theorem sourceHorizontalWoldNaturalLogMoment_zero (X : ℕ) :
    sourceHorizontalWoldNaturalLogMoment 0 X =
      xiHeatCassiniWoldNatWeightSum X := by
  simp [sourceHorizontalWoldNaturalLogMoment,
    xiHeatCassiniWoldNatWeightSum]

private theorem deriv_log_pow {r : ℕ} (_hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    deriv (fun x : ℝ => Real.log x ^ r) t =
      (r : ℝ) * Real.log t ^ (r - 1) / t := by
  have h := (Real.hasDerivAt_log ht.ne').pow r
  change deriv (Real.log ^ r) t = _
  simpa only [div_eq_mul_inv] using h.deriv

private theorem differentiableAt_log_pow {r : ℕ} {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun x : ℝ => Real.log x ^ r) t :=
  (Real.hasDerivAt_log ht.ne').pow r |>.differentiableAt

private theorem continuousOn_log_pow_derivative
    {r : ℕ} (_hr : 0 < r) {X : ℝ} :
    ContinuousOn
      (fun t : ℝ => (r : ℝ) * Real.log t ^ (r - 1) / t)
      (Set.Icc 1 X) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1] : 0 < t)
  exact ((continuousAt_const.mul
    ((Real.continuousAt_log ht0).pow (r - 1))).div continuousAt_id ht0).continuousWithinAt

private theorem integrableOn_deriv_log_pow
    {r : ℕ} (hr : 0 < r) {X : ℝ} (_hX : 1 ≤ X) :
    IntegrableOn (deriv (fun x : ℝ => Real.log x ^ r)) (Set.Icc 1 X) := by
  refine (continuousOn_log_pow_derivative hr (X := X)).integrableOn_Icc.congr_fun
    (fun t ht => ?_) measurableSet_Icc
  exact (deriv_log_pow hr (by linarith [ht.1])).symm

private theorem integral_Ioc_log_pow_derivative
    {r : ℕ} (hr : 0 < r) {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X,
      (r : ℝ) * Real.log t ^ (r - 1) / t) =
        Real.log X ^ r := by
  rw [← intervalIntegral.integral_of_le hX]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log t ^ r)
    (f' := fun t : ℝ => (r : ℝ) * Real.log t ^ (r - 1) / t)
    (a := 1) (b := X)
    (fun t ht => by
      have ht0 : 0 < t := by
        rw [Set.uIcc_of_le hX] at ht
        linarith [ht.1]
      exact ((Real.hasDerivAt_log ht0.ne').pow r).congr_deriv (by
        field_simp [ht0.ne']))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hX).2
      (continuousOn_log_pow_derivative hr (X := X)).integrableOn_Icc)
  simpa [zero_pow (Nat.ne_of_gt hr)] using hftc

private theorem integral_Ioc_log_pow_derivative_mul_log
    {r : ℕ} (hr : 0 < r) {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X,
      ((r : ℝ) * Real.log t ^ (r - 1) / t) * Real.log t) =
        (r : ℝ) / (r + 1 : ℕ) * Real.log X ^ (r + 1) := by
  rw [← intervalIntegral.integral_of_le hX]
  have hcont : ContinuousOn
      (fun t : ℝ => ((r : ℝ) * Real.log t ^ (r - 1) / t) * Real.log t)
      (Set.Icc 1 X) :=
    (continuousOn_log_pow_derivative hr (X := X)).mul (by
      intro t ht
      exact (Real.continuousAt_log
        (ne_of_gt (by linarith [ht.1] : 0 < t))).continuousWithinAt)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ =>
      (r : ℝ) / (r + 1 : ℕ) * Real.log t ^ (r + 1))
    (f' := fun t : ℝ =>
      ((r : ℝ) * Real.log t ^ (r - 1) / t) * Real.log t)
    (a := 1) (b := X)
    (fun t ht => by
      have ht0 : 0 < t := by
        rw [Set.uIcc_of_le hX] at ht
        linarith [ht.1]
      have h := ((Real.hasDerivAt_log ht0.ne').pow (r + 1)).const_mul
        ((r : ℝ) / (r + 1 : ℕ))
      have hpow :
          Real.log t ^ (r - 1) * Real.log t = Real.log t ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel hr]
      have hcast : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      apply h.congr_deriv
      rw [Nat.add_sub_cancel, ← hpow]
      field_simp [ht0.ne', hcast])
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hX).2 hcont.integrableOn_Icc)
  simpa using hftc

/-- Exact Abel formula for every positive logarithmic Wold moment. -/
theorem sourceHorizontalWoldNaturalLogMoment_abel
    (r X : ℕ) (hr : 0 < r) (hX : 1 ≤ X) :
    sourceHorizontalWoldNaturalLogMoment r X =
      Real.log (X : ℝ) ^ r * xiHeatCassiniWoldNatWeightSum X -
        ∫ t in Set.Ioc (1 : ℝ) X,
          ((r : ℝ) * Real.log t ^ (r - 1) / t) *
            xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ := by
  have hzero : xiHeatCassiniWoldNatWeight 0 = 0 := by
    rw [xiHeatCassiniWoldNatWeight, dif_neg (by norm_num : ¬ Nat.Prime 0)]
  have habel := sum_mul_eq_sub_integral_mul₀
    (c := xiHeatCassiniWoldNatWeight)
    (f := fun t : ℝ => Real.log t ^ r)
    hzero (X : ℝ)
    (fun t ht => differentiableAt_log_pow (by linarith [ht.1]))
    (integrableOn_deriv_log_pow hr (by exact_mod_cast hX))
  rw [Nat.floor_natCast] at habel
  rw [sourceHorizontalWoldNaturalLogMoment,
    xiHeatCassiniWoldNatWeightSum]
  rw [habel]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change deriv (fun x : ℝ => Real.log x ^ r) t *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, xiHeatCassiniWoldNatWeight k) =
    ((r : ℝ) * Real.log t ^ (r - 1) / t) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, xiHeatCassiniWoldNatWeight k)
  rw [deriv_log_pow hr (by linarith [ht.1])]

/-- Bounded Wold discrepancy loses exactly one logarithmic degree in every positive moment. -/
theorem abs_integral_sourceHorizontalWoldLogMomentDiscrepancy_le
    {r : ℕ} (hr : 0 < r) {X : ℝ} (hX : 1 ≤ X) :
    |∫ t in Set.Ioc (1 : ℝ) X,
        ((r : ℝ) * Real.log t ^ (r - 1) / t) *
          (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| ≤
      sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ r := by
  let B : ℝ := sourceHorizontalWoldFloorDiscrepancyBound
  let k : ℝ → ℝ := fun t => (r : ℝ) * Real.log t ^ (r - 1) / t
  have hB : 0 ≤ B := sourceHorizontalWoldFloorDiscrepancyBound_nonneg
  have hkInt : IntegrableOn k (Set.Ioc (1 : ℝ) X) :=
    ((continuousOn_log_pow_derivative hr (X := X)).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hmajorInt : IntegrableOn (fun t => B * k t) (Set.Ioc (1 : ℝ) X) :=
    hkInt.const_mul B
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc (1 : ℝ) X),
      ‖k t * (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)‖ ≤
        B * k t := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards with t ht
    have ht1 : 1 ≤ t := ht.1.le
    have htpos : 0 < t := by linarith
    have hk : 0 ≤ k t := by
      dsimp only [k]
      positivity
    have hdisc := abs_xiHeatCassiniWoldNatWeightSum_floor_sub_log_le ht1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    simpa [B, mul_comm] using mul_le_mul_of_nonneg_left hdisc hk
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hmajorInt hbound
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ t in Set.Ioc (1 : ℝ) X,
        ((r : ℝ) * Real.log t ^ (r - 1) / t) *
          (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| =
        |∫ t in Set.Ioc (1 : ℝ) X,
          k t * (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| := by rfl
    _ ≤ ∫ t in Set.Ioc (1 : ℝ) X, B * k t := hnorm
    _ = B * ∫ t in Set.Ioc (1 : ℝ) X, k t := by
      rw [MeasureTheory.integral_const_mul]
    _ = sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ r := by
      rw [integral_Ioc_log_pow_derivative hr hX]

end

end RHTower
