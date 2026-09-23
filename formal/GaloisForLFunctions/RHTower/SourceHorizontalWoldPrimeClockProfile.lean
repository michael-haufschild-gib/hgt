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
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg r)
          (pow_nonneg (Real.log_nonneg ht1) (r - 1))) htpos.le
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

/-- Uniform quantitative all-order log-moment law.  The error is one logarithmic degree below
the main term, with the same discrepancy constant at every positive order. -/
theorem abs_sourceHorizontalWoldNaturalLogMoment_sub_main_le
    (r X : ℕ) (hr : 0 < r) (hX : 1 ≤ X) :
    |sourceHorizontalWoldNaturalLogMoment r X -
        (1 / (r + 1 : ℕ) : ℝ) * Real.log X ^ (r + 1)| ≤
      2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ r := by
  let x : ℝ := X
  let k : ℝ → ℝ := fun t => (r : ℝ) * Real.log t ^ (r - 1) / t
  let A : ℝ → ℝ := fun t => xiHeatCassiniWoldNatWeightSum ⌊t⌋₊
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact_mod_cast hX
  have hdiscX : |xiHeatCassiniWoldNatWeightSum X - Real.log x| ≤
      sourceHorizontalWoldFloorDiscrepancyBound := by
    have h := abs_xiHeatCassiniWoldNatWeightSum_floor_sub_log_le hx
    rw [Nat.floor_natCast] at h
    exact h
  have hkIntIcc : IntegrableOn k (Set.Icc (1 : ℝ) x) :=
    (continuousOn_log_pow_derivative hr (X := x)).integrableOn_Icc
  have hAInt : IntegrableOn (fun t => k t * A t) (Set.Ioc (1 : ℝ) x) := by
    have hraw := integrableOn_mul_sum_Icc
      (c := xiHeatCassiniWoldNatWeight) (a := (1 : ℝ))
      (b := x) (m := 0) (by norm_num) hkIntIcc
    refine (hraw.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
    rfl
  have hlogInt : IntegrableOn (fun t => k t * Real.log t)
      (Set.Ioc (1 : ℝ) x) := by
    have hcont : ContinuousOn (fun t => k t * Real.log t) (Set.Icc (1 : ℝ) x) :=
      (continuousOn_log_pow_derivative hr (X := x)).mul (by
        intro t ht
        exact (Real.continuousAt_log
          (ne_of_gt (by linarith [ht.1] : 0 < t))).continuousWithinAt)
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have herrInt : IntegrableOn (fun t => k t * (A t - Real.log t))
      (Set.Ioc (1 : ℝ) x) := by
    have hsub := hAInt.sub hlogInt
    refine hsub.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]
    ring
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) x, k t * A t) =
        (∫ t in Set.Ioc (1 : ℝ) x, k t * Real.log t) +
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by
    rw [← MeasureTheory.integral_add hlogInt herrInt]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    ring
  have habel := sourceHorizontalWoldNaturalLogMoment_abel r X hr hX
  have hmain := integral_Ioc_log_pow_derivative_mul_log hr hx
  have herr := abs_integral_sourceHorizontalWoldLogMomentDiscrepancy_le hr hx
  have hcast : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  change |sourceHorizontalWoldNaturalLogMoment r X -
      (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1)| ≤
    2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ r
  rw [habel]
  change |Real.log x ^ r * xiHeatCassiniWoldNatWeightSum X -
      (∫ t in Set.Ioc (1 : ℝ) x, k t * A t) -
        (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1)| ≤ _
  rw [hsplit, hmain]
  have hcoeff :
      (r : ℝ) / (r + 1 : ℕ) + (1 / (r + 1 : ℕ) : ℝ) = 1 := by
    field_simp [hcast]
    norm_num
  have hmaincoeff :
      (r : ℝ) / (r + 1 : ℕ) * Real.log x ^ (r + 1) +
          (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1) =
        Real.log x ^ (r + 1) := by
    rw [← add_mul, hcoeff, one_mul]
  have hrewrite :
      Real.log x ^ r * xiHeatCassiniWoldNatWeightSum X -
          ((r : ℝ) / (r + 1 : ℕ) * Real.log x ^ (r + 1) +
            ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)) -
            (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1) =
        Real.log x ^ r *
            (xiHeatCassiniWoldNatWeightSum X - Real.log x) -
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by
    calc
      Real.log x ^ r * xiHeatCassiniWoldNatWeightSum X -
          ((r : ℝ) / (r + 1 : ℕ) * Real.log x ^ (r + 1) +
            ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)) -
            (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1) =
        Real.log x ^ r * xiHeatCassiniWoldNatWeightSum X -
          ((r : ℝ) / (r + 1 : ℕ) * Real.log x ^ (r + 1) +
            (1 / (r + 1 : ℕ) : ℝ) * Real.log x ^ (r + 1)) -
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by ring
      _ = Real.log x ^ r * xiHeatCassiniWoldNatWeightSum X -
          Real.log x ^ (r + 1) -
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by
            rw [hmaincoeff]
      _ = Real.log x ^ r *
            (xiHeatCassiniWoldNatWeightSum X - Real.log x) -
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by
            rw [pow_succ]
            ring
  rw [hrewrite]
  calc
    |Real.log x ^ r *
          (xiHeatCassiniWoldNatWeightSum X - Real.log x) -
        ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)| ≤
      |Real.log x ^ r *
          (xiHeatCassiniWoldNatWeightSum X - Real.log x)| +
        |∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)| :=
      abs_sub _ _
    _ ≤ Real.log x ^ r * sourceHorizontalWoldFloorDiscrepancyBound +
        sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ r := by
      gcongr
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Real.log_nonneg hx) r)]
      exact mul_le_mul_of_nonneg_left hdiscX
        (pow_nonneg (Real.log_nonneg hx) r)
    _ = 2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ r := by
      ring

/-- Every positive fixed log moment has the uniform-distribution coefficient `1/(r+1)`. -/
theorem tendsto_sourceHorizontalWoldNaturalLogMoment_normalized
    (r : ℕ) (hr : 0 < r) :
    Tendsto (fun X : ℕ =>
      sourceHorizontalWoldNaturalLogMoment r X / Real.log X ^ (r + 1))
      atTop (nhds (1 / (r + 1 : ℕ) : ℝ)) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun X : ℕ =>
      (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero'
      (Eventually.of_forall fun X =>
        abs_nonneg (sourceHorizontalWoldNaturalLogMoment r X /
          Real.log X ^ (r + 1) - (1 / (r + 1 : ℕ) : ℝ)))
      (show ∀ᶠ X : ℕ in atTop,
          |sourceHorizontalWoldNaturalLogMoment r X / Real.log X ^ (r + 1) -
            (1 / (r + 1 : ℕ) : ℝ)| ≤
              (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X by
        filter_upwards [eventually_ge_atTop 2] with X hX
        have hlogpos : 0 < Real.log (X : ℝ) :=
          Real.log_pos (by exact_mod_cast hX)
        have hbound :=
          abs_sourceHorizontalWoldNaturalLogMoment_sub_main_le r X hr (by omega)
        calc
          |sourceHorizontalWoldNaturalLogMoment r X / Real.log X ^ (r + 1) -
              (1 / (r + 1 : ℕ) : ℝ)| =
              |sourceHorizontalWoldNaturalLogMoment r X -
                (1 / (r + 1 : ℕ) : ℝ) * Real.log X ^ (r + 1)| /
                  Real.log X ^ (r + 1) := by
                    rw [show sourceHorizontalWoldNaturalLogMoment r X /
                        Real.log X ^ (r + 1) - (1 / (r + 1 : ℕ) : ℝ) =
                          (sourceHorizontalWoldNaturalLogMoment r X -
                            (1 / (r + 1 : ℕ) : ℝ) *
                              Real.log X ^ (r + 1)) /
                            Real.log X ^ (r + 1) by
                          field_simp [hlogpos.ne']]
                    rw [abs_div, abs_of_pos (pow_pos hlogpos (r + 1))]
          _ ≤ (2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ r) /
              Real.log X ^ (r + 1) :=
            div_le_div_of_nonneg_right hbound (pow_pos hlogpos (r + 1)).le
          _ = (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X := by
            rw [pow_succ]
            field_simp [hlogpos.ne'])
      hmajor

/-- At a prime cutoff, every natural log moment is the ordered prime-labelled moment. -/
theorem sourceHorizontalWoldNaturalLogMoment_nthPrime_eq_ordered
    (r N : ℕ) :
    sourceHorizontalWoldNaturalLogMoment r (nthPrimeSubtype N : ℕ) =
      ∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ r := by
  classical
  have hinj : Function.Injective (fun n : ℕ => (nthPrimeSubtype n : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  symm
  calc
    (∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ r) =
      ∑ p ∈ (Finset.range (N + 1)).image
          (fun n => (nthPrimeSubtype n : ℕ)),
        Real.log (p : ℝ) ^ r * xiHeatCassiniWoldNatWeight p := by
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro n hn
            simp only [xiMassNthPrimeLogHeight, xiHeatCassiniWoldNatWeight,
              dif_pos (nthPrimeSubtype n).2]
            change woldCoeff 1 (nthPrimeSubtype n) *
                Real.log (nthPrimeSubtype n : ℝ) ^ r =
              Real.log (nthPrimeSubtype n : ℝ) ^ r *
                woldCoeff 1 (nthPrimeSubtype n)
            ring
          · exact hinj.injOn
    _ = ∑ p ∈ (Finset.Icc 0 (nthPrimeSubtype N : ℕ)).filter Nat.Prime,
        Real.log (p : ℝ) ^ r * xiHeatCassiniWoldNatWeight p := by
          rw [image_range_succ_nthPrimeSubtype_eq_primes_Icc]
    _ = ∑ p ∈ Finset.Icc 0 (nthPrimeSubtype N : ℕ),
        Real.log (p : ℝ) ^ r * xiHeatCassiniWoldNatWeight p := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro p hpIcc hpNotPrimeFilter
          have hnp : ¬ p.Prime := by
            intro hpPrime
            exact hpNotPrimeFilter (Finset.mem_filter.mpr ⟨hpIcc, hpPrime⟩)
          simp [xiHeatCassiniWoldNatWeight, hnp]
    _ = sourceHorizontalWoldNaturalLogMoment r (nthPrimeSubtype N : ℕ) := by
          rw [sourceHorizontalWoldNaturalLogMoment]

/-- Ordered positive log moments have the same universal coefficients. -/
theorem tendsto_sourceHorizontalWoldOrderedLogMoment_normalized
    (r : ℕ) (hr : 0 < r) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range (N + 1),
          woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ r) /
        xiMassNthPrimeLogHeight N ^ (r + 1))
      atTop (nhds (1 / (r + 1 : ℕ) : ℝ)) := by
  have h :=
    (tendsto_sourceHorizontalWoldNaturalLogMoment_normalized r hr).comp
      nthPrimeSubtype_strictMono.tendsto_atTop
  apply h.congr'
  filter_upwards with N
  rw [Function.comp_apply, sourceHorizontalWoldNaturalLogMoment_nthPrime_eq_ordered]
  rfl

/-- Normalized ordered moment coefficient used by the nonlinear prime-clock profile. -/
def sourceHorizontalWoldOrderedNormalizedMoment (N r : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1),
      woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ r) /
    xiMassNthPrimeLogHeight N ^ (r + 1)

private theorem tendsto_sourceHorizontalWoldNaturalMass_normalized :
    Tendsto (fun X : ℕ =>
      xiHeatCassiniWoldNatWeightSum X / Real.log X) atTop (nhds 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff := tendsto_xiHeatCassiniWoldNatWeightSum_sub_log
  have hzero := hdiff.div_atTop hlog
  have hone := hzero.add_const 1
  have heq : (fun X : ℕ =>
      (xiHeatCassiniWoldNatWeightSum X - Real.log X) / Real.log X + 1) =ᶠ[atTop]
        (fun X : ℕ => xiHeatCassiniWoldNatWeightSum X / Real.log X) := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hlog0 : Real.log (X : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hX)).ne'
    field_simp [hlog0]
    ring
  simpa using hone.congr' heq

/-- All ordered normalized moments, including mass (`r=0`), converge to `1/(r+1)`. -/
theorem tendsto_sourceHorizontalWoldOrderedNormalizedMoment (r : ℕ) :
    Tendsto (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N r)
      atTop (nhds (1 / (r + 1 : ℕ) : ℝ)) := by
  cases r with
  | zero =>
      have h := tendsto_sourceHorizontalWoldNaturalMass_normalized.comp
        nthPrimeSubtype_strictMono.tendsto_atTop
      have heq : ((fun X : ℕ =>
          xiHeatCassiniWoldNatWeightSum X / Real.log X) ∘
            fun n => (nthPrimeSubtype n : ℕ)) =
          fun N => sourceHorizontalWoldOrderedNormalizedMoment N 0 := by
        funext N
        rw [Function.comp_apply]
        simp only [sourceHorizontalWoldOrderedNormalizedMoment, pow_zero,
          mul_one, pow_one, Nat.zero_add]
        rw [← xiHeatCassiniOrderedWoldPartialMass]
        rw [xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
          xiMassNthPrimeLogHeight]
      simpa using h.congr' (Eventually.of_forall fun N => congrFun heq N)
  | succ r =>
      exact tendsto_sourceHorizontalWoldOrderedLogMoment_normalized
        (r + 1) (by omega)

theorem sourceHorizontalWoldOrderedNormalizedMoment_nonneg (N r : ℕ) :
    0 ≤ sourceHorizontalWoldOrderedNormalizedMoment N r := by
  rw [sourceHorizontalWoldOrderedNormalizedMoment]
  exact div_nonneg
    (Finset.sum_nonneg fun n _ =>
      mul_nonneg (woldCoeff_nonneg 1 _)
        (pow_nonneg (xiMassNthPrimeLogHeight_pos n).le r))
    (pow_nonneg (xiMassNthPrimeLogHeight_pos N).le (r + 1))

/-- Higher normalized moments are dominated by normalized total Wold mass, uniformly in order. -/
theorem sourceHorizontalWoldOrderedNormalizedMoment_le_mass (N r : ℕ) :
    sourceHorizontalWoldOrderedNormalizedMoment N r ≤
      sourceHorizontalWoldOrderedNormalizedMoment N 0 := by
  have hHN : 0 < xiMassNthPrimeLogHeight N := xiMassNthPrimeLogHeight_pos N
  rw [sourceHorizontalWoldOrderedNormalizedMoment,
    sourceHorizontalWoldOrderedNormalizedMoment]
  simp only [pow_zero, mul_one]
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : n ≤ N := by
    rw [Finset.mem_range] at hn
    omega
  have hheight : xiMassNthPrimeLogHeight n ≤ xiMassNthPrimeLogHeight N :=
    nthPrimeSubtype_log_strictMono.monotone hnN
  have hpow : xiMassNthPrimeLogHeight n ^ r ≤
      xiMassNthPrimeLogHeight N ^ r :=
    pow_le_pow_left₀ (xiMassNthPrimeLogHeight_pos n).le hheight r
  rw [div_le_iff₀ (pow_pos hHN (r + 1))]
  rw [pow_succ]
  field_simp [hHN.ne']
  simpa [pow_succ, mul_assoc] using
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow
        (woldCoeff_nonneg 1 (nthPrimeSubtype n))) hHN.le)

/-- Universal nonlinear profile selected by prime-clock normalization. -/
def sourceHorizontalWoldPrimeClockUniversalProfile (u : ℝ) : ℝ :=
  ∑' k : ℕ,
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      ((1 / (2 * k + 1 : ℕ) : ℝ) - 1)

/-- Finite-stage coefficient series for the centered prime-clock deformation. -/
def sourceHorizontalWoldPrimeClockProfileSeries (N : ℕ) (u : ℝ) : ℝ :=
  ∑' k : ℕ,
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) - 1)

/-- The full finite-stage coefficient profile converges termwise and uniformly summably to the
universal odd source profile.  Thus the cubic survivor is not an isolated jet: every retained odd
jet has a forced coefficient. -/
theorem tendsto_sourceHorizontalWoldPrimeClockProfileSeries (u : ℝ) :
    Tendsto (fun N : ℕ => sourceHorizontalWoldPrimeClockProfileSeries N u) atTop
      (𝓝 (sourceHorizontalWoldPrimeClockUniversalProfile u)) := by
  have hmass : Tendsto
      (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N 0)
      atTop (𝓝 1) := by
    simpa using tendsto_sourceHorizontalWoldOrderedNormalizedMoment 0
  have hmass_lt_two : ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldOrderedNormalizedMoment N 0 < 2 :=
    hmass.eventually_lt_const (by norm_num)
  unfold sourceHorizontalWoldPrimeClockProfileSeries
  unfold sourceHorizontalWoldPrimeClockUniversalProfile
  apply tendsto_tsum_of_dominated_convergence
      (Real.hasSum_sinh |u|).summable
  · intro k
    have hk := tendsto_sourceHorizontalWoldOrderedNormalizedMoment (2 * k)
    exact (tendsto_const_nhds.mul (hk.sub tendsto_const_nhds))
  · filter_upwards [hmass_lt_two] with N hN k
    have hk0 : 0 ≤ sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) :=
      sourceHorizontalWoldOrderedNormalizedMoment_nonneg N (2 * k)
    have hkle : sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) < 2 :=
      (sourceHorizontalWoldOrderedNormalizedMoment_le_mass N (2 * k)).trans_lt hN
    have habs :
        |sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) - 1| ≤ 1 :=
      (abs_le).2 ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
    simp only [Nat.cast_nonneg, abs_of_nonneg]
    exact mul_le_of_le_one_right (by positivity) habs

private theorem sourceHorizontalWoldPrimeClockProfileSeries_term_eq
    (N k : ℕ) (u : ℝ) :
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) - 1) =
      (∑ n ∈ Finset.range (N + 1),
        (woldCoeff 1 (nthPrimeSubtype n) / xiMassNthPrimeLogHeight n) *
          ((u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) ^
              (2 * k + 1) /
            (2 * k + 1).factorial)) -
        u ^ (2 * k + 1) / (2 * k + 1).factorial := by
  have hHN : xiMassNthPrimeLogHeight N ≠ 0 :=
    (xiMassNthPrimeLogHeight_pos N).ne'
  rw [sourceHorizontalWoldOrderedNormalizedMoment, mul_sub, mul_one, mul_div,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hHn : xiMassNthPrimeLogHeight n ≠ 0 :=
    (xiMassNthPrimeLogHeight_pos n).ne'
  rw [div_pow]
  field_simp [hHN, hHn]
  ring

/-- Exact Taylor resummation of the finite source carrier.  No information is discarded: the
coefficient-faithful ordered prime deformation is precisely the all-order moment series. -/
theorem sourceHorizontalWoldPrimeClockProfileSeries_eq_finiteDeformation
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldPrimeClockProfileSeries N u =
      (∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) *
          (Real.sinh
              (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) /
            xiMassNthPrimeLogHeight n)) -
        Real.sinh u := by
  have hprime : ∀ n ∈ Finset.range (N + 1), Summable (fun k : ℕ =>
      (woldCoeff 1 (nthPrimeSubtype n) / xiMassNthPrimeLogHeight n) *
        ((u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) ^
            (2 * k + 1) /
          (2 * k + 1).factorial)) := by
    intro n hn
    exact (Real.hasSum_sinh
      (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N)).summable.mul_left _
  have hfinite : Summable (fun k : ℕ =>
      ∑ n ∈ Finset.range (N + 1),
        (woldCoeff 1 (nthPrimeSubtype n) / xiMassNthPrimeLogHeight n) *
          ((u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) ^
              (2 * k + 1) /
            (2 * k + 1).factorial)) :=
    summable_sum hprime
  have hu : Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial) :=
    (Real.hasSum_sinh u).summable
  rw [sourceHorizontalWoldPrimeClockProfileSeries]
  rw [show (∑' k : ℕ,
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) - 1)) =
      (∑' k : ℕ, ((∑ n ∈ Finset.range (N + 1),
          (woldCoeff 1 (nthPrimeSubtype n) / xiMassNthPrimeLogHeight n) *
            ((u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) ^
                (2 * k + 1) /
              (2 * k + 1).factorial)) -
          u ^ (2 * k + 1) / (2 * k + 1).factorial)) by
    exact tsum_congr fun k =>
      sourceHorizontalWoldPrimeClockProfileSeries_term_eq N k u]
  rw [hfinite.tsum_sub hu]
  rw [Summable.tsum_finsetSum hprime]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_mul_left _
    (Real.hasSum_sinh
      (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N)).summable]
  rw [(Real.hasSum_sinh
    (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N)).tsum_eq]
  have hHn : xiMassNthPrimeLogHeight n ≠ 0 :=
    (xiMassNthPrimeLogHeight_pos n).ne'
  field_simp [hHn]
  exact (Real.hasSum_sinh u).tsum_eq

theorem tendsto_xiMassNthPrimeLogHeight_atTop :
    Tendsto (fun N : ℕ => xiMassNthPrimeLogHeight N) atTop atTop := by
  rw [show (fun N : ℕ => xiMassNthPrimeLogHeight N) =
      (fun x : ℝ => Real.log x) ∘
        (fun N : ℕ => (nthPrimeSubtype N : ℝ)) by
    funext N
    rfl]
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop)

theorem tendsto_sourceHorizontalWoldPrimeClockHolonomy_zero (u : ℝ) :
    Tendsto (fun N : ℕ =>
      xiHeatCassiniWoldLogHolonomyConstant *
        (u / xiMassNthPrimeLogHeight N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => u / xiMassNthPrimeLogHeight N)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
        tendsto_xiMassNthPrimeLogHeight_atTop
  simpa using tendsto_const_nhds.mul hu

/-- Literal source deformation equals its all-order coefficient profile plus a vanishing terminal
holonomy. -/
theorem sourceHorizontalWoldResidualPrimitiveDeformation_primeClock_eq_profile
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldResidualPrimitiveDeformation N
        (u / xiMassNthPrimeLogHeight N) =
      sourceHorizontalWoldPrimeClockProfileSeries N u -
        xiHeatCassiniWoldLogHolonomyConstant *
          (u / xiMassNthPrimeLogHeight N) := by
  rw [sourceHorizontalWoldResidualPrimitiveDeformation_primeClock]
  rw [sourceHorizontalWoldPrimeClockProfileSeries_eq_finiteDeformation]

/-- Full nonlinear source law in the prime-clock window. -/
theorem tendsto_sourceHorizontalWoldResidualPrimitiveDeformation_primeClock
    (u : ℝ) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalWoldResidualPrimitiveDeformation N
        (u / xiMassNthPrimeLogHeight N)) atTop
      (𝓝 (sourceHorizontalWoldPrimeClockUniversalProfile u)) := by
  have hprofile := tendsto_sourceHorizontalWoldPrimeClockProfileSeries u
  have hholonomy := tendsto_sourceHorizontalWoldPrimeClockHolonomy_zero u
  have hsub := hprofile.sub hholonomy
  simpa only [sub_zero] using hsub.congr'
    (Eventually.of_forall fun N =>
      (sourceHorizontalWoldResidualPrimitiveDeformation_primeClock_eq_profile N u).symm)

private theorem summable_sourceHorizontalWoldPrimeClockProfileDeficit
    {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (1 - (1 / (2 * k + 1 : ℕ) : ℝ))) := by
  refine Summable.of_norm_bounded (Real.hasSum_sinh u).summable ?_
  intro k
  have hden : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0))
  have hden0 : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
  have hinv0 : 0 ≤ (1 / (2 * k + 1 : ℕ) : ℝ) := by positivity
  have hinv_le : (1 / (2 * k + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden0).2 hden
  have hcoeff0 : 0 ≤ (1 - (1 / (2 * k + 1 : ℕ) : ℝ)) := by linarith
  have hcoeff1 : (1 - (1 / (2 * k + 1 : ℕ) : ℝ)) ≤ 1 := by linarith
  have hbase0 : 0 ≤ u ^ (2 * k + 1) / (2 * k + 1).factorial := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbase0 hcoeff0)]
  exact mul_le_of_le_one_right hbase0 hcoeff1

/-- Reflection reverses the complete source profile, preserving both orientations. -/
@[simp] theorem sourceHorizontalWoldPrimeClockUniversalProfile_neg (u : ℝ) :
    sourceHorizontalWoldPrimeClockUniversalProfile (-u) =
      -sourceHorizontalWoldPrimeClockUniversalProfile u := by
  unfold sourceHorizontalWoldPrimeClockUniversalProfile
  calc
    (∑' k : ℕ,
        (-u) ^ (2 * k + 1) / (2 * k + 1).factorial *
          ((1 / (2 * k + 1 : ℕ) : ℝ) - 1)) =
        ∑' k : ℕ,
          -(u ^ (2 * k + 1) / (2 * k + 1).factorial *
            ((1 / (2 * k + 1 : ℕ) : ℝ) - 1)) := by
              apply tsum_congr
              intro k
              have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
              rw [hodd.neg_pow]
              ring
    _ = -(∑' k : ℕ,
        u ^ (2 * k + 1) / (2 * k + 1).factorial *
          ((1 / (2 * k + 1 : ℕ) : ℝ) - 1)) := tsum_neg

/-- Positive horizontal rate produces strictly negative source response.  The `k=1` cubic term
already makes the complete nonnegative deficit strict; higher odd orders reinforce it. -/
theorem sourceHorizontalWoldPrimeClockUniversalProfile_neg_of_pos
    {u : ℝ} (hu : 0 < u) :
    sourceHorizontalWoldPrimeClockUniversalProfile u < 0 := by
  let g : ℕ → ℝ := fun k =>
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (1 - (1 / (2 * k + 1 : ℕ) : ℝ))
  have hsum : Summable g :=
    summable_sourceHorizontalWoldPrimeClockProfileDeficit hu.le
  have hg0 : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    have hden : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0))
    have hden0 : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
    have hinv_le : (1 / (2 * k + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hden0).2 hden
    exact mul_nonneg (by positivity) (by linarith)
  have hg1 : 0 < g 1 := by
    dsimp [g]
    norm_num
    positivity
  have hpositive : 0 < ∑' k : ℕ, g k := hsum.tsum_pos hg0 1 hg1
  have heq : sourceHorizontalWoldPrimeClockUniversalProfile u =
      -(∑' k : ℕ, g k) := by
    unfold sourceHorizontalWoldPrimeClockUniversalProfile
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [g]
    ring
  rw [heq]
  exact neg_lt_zero.mpr hpositive

theorem sourceHorizontalWoldPrimeClockUniversalProfile_pos_of_neg
    {u : ℝ} (hu : u < 0) :
    0 < sourceHorizontalWoldPrimeClockUniversalProfile u := by
  have h := sourceHorizontalWoldPrimeClockUniversalProfile_neg_of_pos
    (u := -u) (neg_pos.mpr hu)
  rw [sourceHorizontalWoldPrimeClockUniversalProfile_neg] at h
  linarith

/-- The full coefficient-faithful source profile has exactly one zero. -/
theorem sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff (u : ℝ) :
    sourceHorizontalWoldPrimeClockUniversalProfile u = 0 ↔ u = 0 := by
  constructor
  · intro hzero
    by_contra hu
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · linarith [sourceHorizontalWoldPrimeClockUniversalProfile_pos_of_neg huNeg]
    · linarith [sourceHorizontalWoldPrimeClockUniversalProfile_neg_of_pos huPos]
  · intro hu
    subst u
    simp [sourceHorizontalWoldPrimeClockUniversalProfile]

theorem sourceHorizontalWoldPrimeClockUniversalProfile_mul_rate_neg_iff
    (u : ℝ) :
    sourceHorizontalWoldPrimeClockUniversalProfile u * u < 0 ↔ u ≠ 0 := by
  constructor
  · intro h
    exact fun hu => by simp [hu] at h
  · intro hu
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · exact mul_neg_of_pos_of_neg
        (sourceHorizontalWoldPrimeClockUniversalProfile_pos_of_neg huNeg) huNeg
    · exact mul_neg_of_neg_of_pos
        (sourceHorizontalWoldPrimeClockUniversalProfile_neg_of_pos huPos) huPos

/-- The first surviving nonlinear mode is already coercive.  All later odd modes have the same
sign, so the complete source profile lies below its cubic term on the positive ray. -/
theorem sourceHorizontalWoldPrimeClockUniversalProfile_le_neg_cubic
    {u : ℝ} (hu : 0 ≤ u) :
    sourceHorizontalWoldPrimeClockUniversalProfile u ≤ -(u ^ (3 : ℕ) / 9) := by
  let g : ℕ → ℝ := fun k =>
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (1 - (1 / (2 * k + 1 : ℕ) : ℝ))
  have hsum : Summable g :=
    summable_sourceHorizontalWoldPrimeClockProfileDeficit hu
  have hg0 : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    have hden : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0))
    have hden0 : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
    have hinv_le : (1 / (2 * k + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hden0).2 hden
    exact mul_nonneg (by positivity) (by linarith)
  have hterm : g 1 ≤ ∑' k : ℕ, g k := hsum.le_tsum 1 (fun k _ => hg0 k)
  have hg1 : g 1 = u ^ (3 : ℕ) / 9 := by
    dsimp [g]
    norm_num
    ring
  have heq : sourceHorizontalWoldPrimeClockUniversalProfile u =
      -(∑' k : ℕ, g k) := by
    unfold sourceHorizontalWoldPrimeClockUniversalProfile
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [g]
    ring
  rw [hg1] at hterm
  rw [heq]
  linarith

/-- Reflection-even polar work before specialization to a Xi divisor class. -/
def sourceHorizontalWoldPrimeClockPolarRateWork (u : ℝ) : ℝ :=
  -(Real.log 2 / 2) * u * sourceHorizontalWoldPrimeClockUniversalProfile u

@[simp] theorem sourceHorizontalWoldPrimeClockPolarRateWork_neg (u : ℝ) :
    sourceHorizontalWoldPrimeClockPolarRateWork (-u) =
      sourceHorizontalWoldPrimeClockPolarRateWork u := by
  rw [sourceHorizontalWoldPrimeClockPolarRateWork,
    sourceHorizontalWoldPrimeClockPolarRateWork,
    sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  ring

/-- Positive-ray quantitative source properness. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    Real.log 2 / 18 * u ^ (4 : ℕ) ≤
      sourceHorizontalWoldPrimeClockPolarRateWork u := by
  have hcubic :=
    sourceHorizontalWoldPrimeClockUniversalProfile_le_neg_cubic hu
  have hfactor : 0 ≤ Real.log 2 / 2 * u := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcubic hfactor
  rw [sourceHorizontalWoldPrimeClockPolarRateWork]
  calc
    Real.log 2 / 18 * u ^ (4 : ℕ) =
        -((Real.log 2 / 2 * u) * (-(u ^ (3 : ℕ) / 9))) := by ring
    _ ≤ -((Real.log 2 / 2 * u) *
        sourceHorizontalWoldPrimeClockUniversalProfile u) := neg_le_neg hmul
    _ = -(Real.log 2 / 2) * u *
        sourceHorizontalWoldPrimeClockUniversalProfile u := by ring

/-- Quantitative source properness: polar work dominates a universal quartic.  The quartic is the
product of the complete-resolution linear tail and the first retained nonlinear Wold mode. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower (u : ℝ) :
    Real.log 2 / 18 * u ^ (4 : ℕ) ≤
      sourceHorizontalWoldPrimeClockPolarRateWork u := by
  by_cases hu : 0 ≤ u
  · exact sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower_of_nonneg hu
  · have hneg : 0 ≤ -u := by linarith
    have h :=
      sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower_of_nonneg hneg
    calc
      Real.log 2 / 18 * u ^ (4 : ℕ) = Real.log 2 / 18 * (-u) ^ (4 : ℕ) := by ring
      _ ≤ sourceHorizontalWoldPrimeClockPolarRateWork (-u) := h
      _ = sourceHorizontalWoldPrimeClockPolarRateWork u :=
        sourceHorizontalWoldPrimeClockPolarRateWork_neg u

/-- Every nonzero horizontal grade has unbounded source polar work along an expanding source-scale
orbit.  This is the nonlinear source analogue of global formation properness. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_scale_tendsto
    {d u : ℝ} (hd : 1 < d) (hu : u ≠ 0) :
    Tendsto (fun n : ℕ =>
      sourceHorizontalWoldPrimeClockPolarRateWork (d ^ n * u)) atTop atTop := by
  have hbase : (1 : ℝ) < d ^ (4 : ℕ) := one_lt_pow₀ hd (by norm_num)
  have hpow : Tendsto (fun n : ℕ => (d ^ (4 : ℕ)) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hbase
  have hu4 : 0 < u ^ (4 : ℕ) := by positivity
  have hc : 0 < Real.log 2 / 18 * u ^ (4 : ℕ) := by positivity
  have hlower : Tendsto (fun n : ℕ =>
      (Real.log 2 / 18 * u ^ (4 : ℕ)) * (d ^ (4 : ℕ)) ^ n) atTop atTop :=
    hpow.const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards with n
  calc
    (Real.log 2 / 18 * u ^ (4 : ℕ)) * (d ^ (4 : ℕ)) ^ n =
        Real.log 2 / 18 * (d ^ n * u) ^ (4 : ℕ) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [Nat.mul_comm 4 n]
          ring
    _ ≤ sourceHorizontalWoldPrimeClockPolarRateWork (d ^ n * u) :=
      sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower _

/-- Uniform boundedness of the nonlinear source work on a complete source-generated scale orbit. -/
def SourceHorizontalWoldPrimeClockBoundedPolarScaleWork (d u : ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ,
    sourceHorizontalWoldPrimeClockPolarRateWork (d ^ n * u) ≤ B

/-- Exact source selection law: bounded nonlinear polar work is equivalent to neutral horizontal
grade. -/
theorem sourceHorizontalWoldPrimeClockBoundedPolarScaleWork_iff
    {d u : ℝ} (hd : 1 < d) :
    SourceHorizontalWoldPrimeClockBoundedPolarScaleWork d u ↔ u = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hu
    have htop :=
      sourceHorizontalWoldPrimeClockPolarRateWork_scale_tendsto hd hu
    have hevent := htop.eventually_gt_atTop B
    rcases hevent.exists with ⟨n, hn⟩
    linarith [hB n]
  · rintro rfl
    refine ⟨0, fun n => ?_⟩
    simp [sourceHorizontalWoldPrimeClockPolarRateWork,
      sourceHorizontalWoldPrimeClockUniversalProfile]

/-- Complete source response attached to each multiplicity-labelled Xi divisor class. -/
def sourceZeroHorizontalWoldPrimeClockProfileResponse
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  sourceHorizontalWoldResidualPrimitiveDeformation N
    (primeDepthBVWoldXiCenteredRate q.1 / xiMassNthPrimeLogHeight N)

theorem tendsto_sourceZeroHorizontalWoldPrimeClockProfileResponse
    (q : XiZeroCopy) :
    Tendsto (sourceZeroHorizontalWoldPrimeClockProfileResponse q) atTop
      (𝓝 (sourceHorizontalWoldPrimeClockUniversalProfile
        (primeDepthBVWoldXiCenteredRate q.1))) := by
  change Tendsto (fun N : ℕ =>
    sourceHorizontalWoldResidualPrimitiveDeformation N
      (primeDepthBVWoldXiCenteredRate q.1 / xiMassNthPrimeLogHeight N)) atTop _
  exact tendsto_sourceHorizontalWoldResidualPrimitiveDeformation_primeClock
    (primeDepthBVWoldXiCenteredRate q.1)

/-- Source reflection exchanges the two retained cofinal orientations by exact negation at every
finite cutoff, before scalarization or passage to the horizon. -/
@[simp] theorem sourceZeroHorizontalWoldPrimeClockProfileResponse_reflection
    (q : XiZeroCopy) (N : ℕ) :
    sourceZeroHorizontalWoldPrimeClockProfileResponse
        (xiZeroCopyLineConjEquiv q) N =
      -sourceZeroHorizontalWoldPrimeClockProfileResponse q N := by
  rw [sourceZeroHorizontalWoldPrimeClockProfileResponse,
    sourceZeroHorizontalWoldPrimeClockProfileResponse]
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate]
  have harg :
      -primeDepthBVWoldXiCenteredRate q.1 / xiMassNthPrimeLogHeight N =
        -(primeDepthBVWoldXiCenteredRate q.1 / xiMassNthPrimeLogHeight N) := by ring
  rw [harg, sourceHorizontalWoldResidualPrimitiveDeformation_neg]

/-- The literal all-order Xi response vanishes at the horizon exactly on the critical line. -/
theorem sourceZeroHorizontalWoldPrimeClockProfileLimit_eq_zero_iff
    (q : XiZeroCopy) :
    sourceHorizontalWoldPrimeClockUniversalProfile
        (primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff]
  exact primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- Squaring identifies both reflection transports on the same coefficient-faithful source carrier;
the common value is positive exactly for an off-line divisor class. -/
theorem sourceZeroHorizontalWoldPrimeClockProfileReflectionSquare
    (q : XiZeroCopy) :
    sourceHorizontalWoldPrimeClockUniversalProfile
          (primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1) ^ (2 : ℕ) =
        sourceHorizontalWoldPrimeClockUniversalProfile
          (primeDepthBVWoldXiCenteredRate q.1) ^ (2 : ℕ) := by
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate, sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  ring

theorem sourceZeroHorizontalWoldPrimeClockProfileSquare_pos_iff
    (q : XiZeroCopy) :
    0 < sourceHorizontalWoldPrimeClockUniversalProfile
        (primeDepthBVWoldXiCenteredRate q.1) ^ (2 : ℕ) ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [sq_pos_iff]
  rw [Ne, sourceZeroHorizontalWoldPrimeClockProfileLimit_eq_zero_iff]

/-- Cross-corpus positive polar handoff: pair the ordered complete-resolution tail with the full
Wold horizon response.  Both factors are reflection-odd, so their product retains both source
orientations as one nonnegative work. -/
def sourceZeroHorizontalWoldPrimeClockPolarWork (q : XiZeroCopy) : ℝ :=
  sourceZeroHorizontalTailLog q *
    sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate q.1)

theorem sourceZeroHorizontalWoldPrimeClockPolarWork_closedForm
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalWoldPrimeClockPolarWork q =
      -(Real.log 2 / 2) * primeDepthBVWoldXiCenteredRate q.1 *
        sourceHorizontalWoldPrimeClockUniversalProfile
          (primeDepthBVWoldXiCenteredRate q.1) := by
  rw [sourceZeroHorizontalWoldPrimeClockPolarWork,
    primeDepthBVWoldXiCenteredRate_eq_sourceTailLog K q]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog]

/-- The Xi-specialized polar work is exactly the universal rate work; no divisor label or
multiplicity copy is erased in the specialization. -/
theorem sourceZeroHorizontalWoldPrimeClockPolarWork_eq_rateWork
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalWoldPrimeClockPolarWork q =
      sourceHorizontalWoldPrimeClockPolarRateWork
        (primeDepthBVWoldXiCenteredRate q.1) := by
  rw [sourceZeroHorizontalWoldPrimeClockPolarWork_closedForm K,
    sourceHorizontalWoldPrimeClockPolarRateWork]

/-- Bounded Adams/source-dilation orbit for one multiplicity-labelled Xi class. -/
def sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork
    (d : ℝ) (q : XiZeroCopy) : Prop :=
  SourceHorizontalWoldPrimeClockBoundedPolarScaleWork d
    (primeDepthBVWoldXiCenteredRate q.1)

/-- Pointwise endpoint: bounded nonlinear source work on an expanding orbit forces and is forced
by critical-line placement. -/
theorem sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork_iff
    {d : ℝ} (hd : 1 < d) (q : XiZeroCopy) :
    sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork d q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork,
    sourceHorizontalWoldPrimeClockBoundedPolarScaleWork_iff hd,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global source producer target: every retained divisor class has bounded nonlinear polar work
along the same expanding source-scale orbit. -/
def SourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork (d : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork d q

/-- Exact RH endpoint for source-scale properness.  Remaining mathematical burden is no longer a
sign or classifier: it is a source theorem establishing this global boundedness from the pre-zero
normalized carrier. -/
theorem sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork_iff_riemannHypothesis
    {d : ℝ} (hd : 1 < d) :
    SourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork d ↔
      RiemannHypothesis := by
  constructor
  · intro hbounded
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      exact (sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork_iff hd q).1
        (hbounded q)
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH q
    apply (sourceZeroHorizontalWoldPrimeClockBoundedPolarScaleWork_iff hd q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

@[simp] theorem sourceZeroHorizontalWoldPrimeClockPolarWork_reflection
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalWoldPrimeClockPolarWork
        (xiZeroCopyLineConjEquiv q) =
      sourceZeroHorizontalWoldPrimeClockPolarWork q := by
  rw [sourceZeroHorizontalWoldPrimeClockPolarWork,
    sourceZeroHorizontalWoldPrimeClockPolarWork,
    sourceZeroHorizontalTailLog_reflection K q]
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate, sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  ring

theorem sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff
    (K : ℕ) (q : XiZeroCopy) :
    0 < sourceZeroHorizontalWoldPrimeClockPolarWork q ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [sourceZeroHorizontalWoldPrimeClockPolarWork_closedForm K]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    exact fun hline => by
      have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
        (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
      simp [hrate] at h
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      intro hrate
      exact hline ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate)
    have hproduct :=
      (sourceHorizontalWoldPrimeClockUniversalProfile_mul_rate_neg_iff
        (primeDepthBVWoldXiCenteredRate q.1)).2 hrate
    nlinarith

theorem sourceZeroHorizontalWoldPrimeClockPolarWork_nonneg
    (K : ℕ) (q : XiZeroCopy) :
    0 ≤ sourceZeroHorizontalWoldPrimeClockPolarWork q := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    simp [sourceZeroHorizontalWoldPrimeClockPolarWork_closedForm K, hrate]
  · exact (sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff K q).2 hline |>.le

theorem sourceZeroHorizontalWoldPrimeClockPolarWork_eq_zero_iff
    (K : ℕ) (q : XiZeroCopy) :
    sourceZeroHorizontalWoldPrimeClockPolarWork q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hline
    exact (sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff K q).2 hline |>.ne' hzero
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    simp [sourceZeroHorizontalWoldPrimeClockPolarWork_closedForm K, hrate]

/-- Finite-cutoff mixed source work converges to the positive polar handoff. -/
theorem tendsto_sourceZeroHorizontalWoldPrimeClockPolarWork
    (q : XiZeroCopy) :
    Tendsto (fun N : ℕ =>
      sourceZeroHorizontalTailLog q *
        sourceZeroHorizontalWoldPrimeClockProfileResponse q N) atTop
      (𝓝 (sourceZeroHorizontalWoldPrimeClockPolarWork q)) := by
  exact (tendsto_sourceZeroHorizontalWoldPrimeClockProfileResponse q).const_mul
    (sourceZeroHorizontalTailLog q)

end

end RHTower
