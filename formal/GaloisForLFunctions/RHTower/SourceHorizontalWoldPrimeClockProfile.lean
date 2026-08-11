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
  apply hone.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hlog0 : Real.log (X : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Function.comp_apply]
  field_simp [hlog0]

/-- All ordered normalized moments, including mass (`r=0`), converge to `1/(r+1)`. -/
theorem tendsto_sourceHorizontalWoldOrderedNormalizedMoment (r : ℕ) :
    Tendsto (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N r)
      atTop (nhds (1 / (r + 1 : ℕ) : ℝ)) := by
  cases r with
  | zero =>
      have h := tendsto_sourceHorizontalWoldNaturalMass_normalized.comp
        nthPrimeSubtype_strictMono.tendsto_atTop
      apply h.congr'
      filter_upwards with N
      rw [Function.comp_apply]
      simp only [sourceHorizontalWoldOrderedNormalizedMoment, pow_zero,
        mul_one, pow_one, Nat.zero_add, Nat.cast_one, div_one]
      rw [← xiHeatCassiniOrderedWoldPartialMass]
      rw [xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
        xiMassNthPrimeLogHeight]
  | succ r =>
      exact tendsto_sourceHorizontalWoldOrderedLogMoment_normalized
        (r + 1) (by omega)

end

end RHTower
