import GaloisForLFunctions.RHTower.SourceHorizontalWoldNeutralJetBridge
import Mathlib.NumberTheory.AbelSummation

/-!
# Prime-clock cubic remnant of the source-horizontal Wold deformation

The linear neutral jet of the cofinal residual primitive tends to zero.  Its cubic jet does not.
Abel summation against the uniformly bounded Wold logarithmic discrepancy proves that the
log-square Wold moment has leading term `(log X)^3 / 3`.  Subtracting the terminal prime holonomy
therefore leaves the universal normalized cubic coefficient `-2/3`.

This is an unconditional source-side asymptotic.  No RH statement or critical Abel-variation
hypothesis is used.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural-cutoff log-square moment of the depth-one Wold source. -/
def sourceHorizontalWoldNaturalCubicMoment (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 X,
    Real.log (n : ℝ) ^ 2 * xiHeatCassiniWoldNatWeight n

/-- Uniform discrepancy constant used by the cubic Abel estimate. -/
def sourceHorizontalWoldFloorDiscrepancyBound : ℝ :=
  mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass + 1

theorem sourceHorizontalWoldFloorDiscrepancyBound_nonneg :
    0 ≤ sourceHorizontalWoldFloorDiscrepancyBound := by
  have hM : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  have hT : 0 ≤ xiHeatCassiniWoldNatTraceCorrectionMass :=
    tsum_nonneg xiHeatCassiniWoldNatTraceCorrection_nonneg
  rw [sourceHorizontalWoldFloorDiscrepancyBound]
  positivity

/-- The natural Wold cumulative mass stays within one fixed distance of continuous log height,
including between integer cutoffs. -/
theorem abs_xiHeatCassiniWoldNatWeightSum_floor_sub_log_le
    {t : ℝ} (ht : 1 ≤ t) :
    |xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t| ≤
      sourceHorizontalWoldFloorDiscrepancyBound := by
  have ht0 : 0 ≤ t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hfloorpos : (0 : ℝ) < ⌊t⌋₊ := by
    exact_mod_cast (Nat.zero_lt_of_lt hfloor1)
  have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hratio0 : 0 < t / (⌊t⌋₊ : ℝ) := div_pos (by linarith) hfloorpos
  have hlogdiff : Real.log t - Real.log (⌊t⌋₊ : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hratio0
    rw [Real.log_div (by linarith) hfloorpos.ne'] at h
    have hfloorOne : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor1
    have ht2 : t ≤ 2 * (⌊t⌋₊ : ℝ) := by
      nlinarith
    nlinarith [(div_le_iff₀ hfloorpos).mpr ht2]
  have hW := abs_xiHeatCassiniWoldNatWeightSum_sub_log_le ⌊t⌋₊ hfloor1
  calc
    |xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t| =
        |(xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log ⌊t⌋₊) +
          (Real.log ⌊t⌋₊ - Real.log t)| := by ring_nf
    _ ≤ |xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log ⌊t⌋₊| +
        |Real.log ⌊t⌋₊ - Real.log t| := abs_add_le _ _
    _ ≤ sourceHorizontalWoldFloorDiscrepancyBound := by
      rw [abs_of_nonpos
        (sub_nonpos.mpr (Real.log_le_log hfloorpos hfloorle))]
      rw [sourceHorizontalWoldFloorDiscrepancyBound]
      linarith

private theorem deriv_log_sq {t : ℝ} (ht : 0 < t) :
    deriv (fun x : ℝ => Real.log x ^ 2) t =
      2 * Real.log t / t := by
  have h := (Real.hasDerivAt_log ht.ne').pow 2
  change deriv (Real.log ^ 2) t = 2 * Real.log t / t
  simpa [div_eq_mul_inv] using h.deriv

private theorem differentiableAt_log_sq {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun x : ℝ => Real.log x ^ 2) t :=
  (Real.hasDerivAt_log ht.ne').pow 2 |>.differentiableAt

private theorem integrableOn_deriv_log_sq {X : ℝ} (_hX : 1 ≤ X) :
    IntegrableOn (deriv (fun x : ℝ => Real.log x ^ 2)) (Set.Icc 1 X) := by
  have hcont : ContinuousOn (fun t : ℝ => 2 * Real.log t / t) (Set.Icc 1 X) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1] : 0 < t)
    exact ((continuousAt_const.mul (Real.continuousAt_log ht0)).div
      continuousAt_id ht0).continuousWithinAt
  refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
  exact (deriv_log_sq (by linarith [ht.1])).symm

private theorem continuousOn_two_log_div {X : ℝ} :
    ContinuousOn (fun t : ℝ => 2 * Real.log t / t) (Set.Icc 1 X) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1] : 0 < t)
  exact ((continuousAt_const.mul (Real.continuousAt_log ht0)).div
    continuousAt_id ht0).continuousWithinAt

private theorem integral_Ioc_two_log_div
    {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X, 2 * Real.log t / t) =
      Real.log X ^ 2 := by
  rw [← intervalIntegral.integral_of_le hX]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log t ^ 2)
    (f' := fun t : ℝ => 2 * Real.log t / t)
    (a := 1) (b := X)
    (fun t ht => by
      have ht0 : 0 < t := by
        rw [Set.uIcc_of_le hX] at ht
        linarith [ht.1]
      exact ((Real.hasDerivAt_log ht0.ne').pow 2).congr_deriv (by ring))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hX).2
      (continuousOn_two_log_div (X := X)).integrableOn_Icc)
  simpa using hftc

private theorem integral_Ioc_two_log_sq_div
    {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X,
      (2 * Real.log t / t) * Real.log t) =
        (2 / 3 : ℝ) * Real.log X ^ 3 := by
  rw [← intervalIntegral.integral_of_le hX]
  have hcont : ContinuousOn
      (fun t : ℝ => (2 * Real.log t / t) * Real.log t) (Set.Icc 1 X) := by
    exact (continuousOn_two_log_div (X := X)).mul (by
      intro t ht
      exact (Real.continuousAt_log
        (ne_of_gt (by linarith [ht.1] : 0 < t))).continuousWithinAt)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (2 / 3 : ℝ) * Real.log t ^ 3)
    (f' := fun t : ℝ => (2 * Real.log t / t) * Real.log t)
    (a := 1) (b := X)
    (fun t ht => by
      have ht0 : 0 < t := by
        rw [Set.uIcc_of_le hX] at ht
        linarith [ht.1]
      have h := ((Real.hasDerivAt_log ht0.ne').pow 3).const_mul (2 / 3 : ℝ)
      simpa only [Pi.pow_apply] using h.congr_deriv (by ring))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hX).2 hcont.integrableOn_Icc)
  simpa using hftc

/-- Exact Abel formula for the cubic Wold moment. -/
theorem sourceHorizontalWoldNaturalCubicMoment_abel
    (X : ℕ) (hX : 1 ≤ X) :
    sourceHorizontalWoldNaturalCubicMoment X =
      Real.log (X : ℝ) ^ 2 * xiHeatCassiniWoldNatWeightSum X -
        ∫ t in Set.Ioc (1 : ℝ) X,
          (2 * Real.log t / t) * xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ := by
  have hzero : xiHeatCassiniWoldNatWeight 0 = 0 := by
    rw [xiHeatCassiniWoldNatWeight, dif_neg (by norm_num : ¬ Nat.Prime 0)]
  have habel := sum_mul_eq_sub_integral_mul₀
    (c := xiHeatCassiniWoldNatWeight)
    (f := fun t : ℝ => Real.log t ^ 2)
    hzero (X : ℝ)
    (fun t ht => differentiableAt_log_sq (by linarith [ht.1]))
    (integrableOn_deriv_log_sq (by exact_mod_cast hX))
  rw [Nat.floor_natCast] at habel
  rw [sourceHorizontalWoldNaturalCubicMoment,
    xiHeatCassiniWoldNatWeightSum]
  rw [habel]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change deriv (fun x : ℝ => Real.log x ^ 2) t *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, xiHeatCassiniWoldNatWeight k) =
    (2 * Real.log t / t) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, xiHeatCassiniWoldNatWeight k)
  rw [deriv_log_sq (by linarith [ht.1])]

/-- The Abel error produced by the bounded Wold discrepancy is at most one logarithmic square. -/
theorem abs_integral_sourceHorizontalWoldCubicDiscrepancy_le
    {X : ℝ} (hX : 1 ≤ X) :
    |∫ t in Set.Ioc (1 : ℝ) X,
        (2 * Real.log t / t) *
          (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| ≤
      sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ 2 := by
  let B : ℝ := sourceHorizontalWoldFloorDiscrepancyBound
  let k : ℝ → ℝ := fun t => 2 * Real.log t / t
  have hB : 0 ≤ B := sourceHorizontalWoldFloorDiscrepancyBound_nonneg
  have hkInt : IntegrableOn k (Set.Ioc (1 : ℝ) X) := by
    exact ((continuousOn_two_log_div (X := X)).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hmajorInt : IntegrableOn (fun t => B * k t) (Set.Ioc (1 : ℝ) X) :=
    hkInt.const_mul B
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc (1 : ℝ) X),
      ‖k t * (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)‖ ≤
        B * k t := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards with t ht
    have ht1 : 1 ≤ t := ht.1.le
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
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
        (2 * Real.log t / t) *
          (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| =
        |∫ t in Set.Ioc (1 : ℝ) X,
          k t * (xiHeatCassiniWoldNatWeightSum ⌊t⌋₊ - Real.log t)| := by rfl
    _ ≤ ∫ t in Set.Ioc (1 : ℝ) X, B * k t := hnorm
    _ = B * ∫ t in Set.Ioc (1 : ℝ) X, k t := by
      rw [MeasureTheory.integral_const_mul]
    _ = sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ 2 := by
      rw [integral_Ioc_two_log_div hX]

/-- Quantitative cubic moment law.  Bounded Wold log discrepancy loses one full logarithmic
degree after Abel summation. -/
theorem abs_sourceHorizontalWoldNaturalCubicMoment_sub_main_le
    (X : ℕ) (hX : 1 ≤ X) :
    |sourceHorizontalWoldNaturalCubicMoment X -
        (1 / 3 : ℝ) * Real.log X ^ 3| ≤
      2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ 2 := by
  let x : ℝ := X
  let k : ℝ → ℝ := fun t => 2 * Real.log t / t
  let A : ℝ → ℝ := fun t => xiHeatCassiniWoldNatWeightSum ⌊t⌋₊
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact_mod_cast hX
  have hdiscX : |xiHeatCassiniWoldNatWeightSum X - Real.log x| ≤
      sourceHorizontalWoldFloorDiscrepancyBound := by
    have h := abs_xiHeatCassiniWoldNatWeightSum_floor_sub_log_le hx
    rw [Nat.floor_natCast] at h
    exact h
  have hkIntIcc : IntegrableOn k (Set.Icc (1 : ℝ) x) := by
    exact (continuousOn_two_log_div (X := x)).integrableOn_Icc
  have hAInt : IntegrableOn (fun t => k t * A t) (Set.Ioc (1 : ℝ) x) := by
    have hraw := integrableOn_mul_sum_Icc
      (c := xiHeatCassiniWoldNatWeight) (a := (1 : ℝ))
      (b := x) (m := 0) (by norm_num) hkIntIcc
    refine (hraw.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
    rfl
  have hlogInt : IntegrableOn (fun t => k t * Real.log t) (Set.Ioc (1 : ℝ) x) := by
    have hcont : ContinuousOn (fun t => k t * Real.log t) (Set.Icc (1 : ℝ) x) := by
      exact (continuousOn_two_log_div (X := x)).mul (by
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
  have habel := sourceHorizontalWoldNaturalCubicMoment_abel X hX
  have hmain := integral_Ioc_two_log_sq_div hx
  have herr := abs_integral_sourceHorizontalWoldCubicDiscrepancy_le hx
  change |sourceHorizontalWoldNaturalCubicMoment X -
      (1 / 3 : ℝ) * Real.log x ^ 3| ≤
    2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ 2
  rw [habel]
  change |Real.log x ^ 2 * xiHeatCassiniWoldNatWeightSum X -
      (∫ t in Set.Ioc (1 : ℝ) x, k t * A t) -
        (1 / 3 : ℝ) * Real.log x ^ 3| ≤ _
  rw [hsplit, hmain]
  have hrewrite :
      Real.log x ^ 2 * xiHeatCassiniWoldNatWeightSum X -
          ((2 / 3 : ℝ) * Real.log x ^ 3 +
            ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)) -
            (1 / 3 : ℝ) * Real.log x ^ 3 =
        Real.log x ^ 2 *
            (xiHeatCassiniWoldNatWeightSum X - Real.log x) -
          ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t) := by
    ring
  rw [hrewrite]
  calc
    |Real.log x ^ 2 *
          (xiHeatCassiniWoldNatWeightSum X - Real.log x) -
        ∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)| ≤
      |Real.log x ^ 2 *
          (xiHeatCassiniWoldNatWeightSum X - Real.log x)| +
        |∫ t in Set.Ioc (1 : ℝ) x, k t * (A t - Real.log t)| :=
      abs_sub _ _
    _ ≤ Real.log x ^ 2 * sourceHorizontalWoldFloorDiscrepancyBound +
        sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ 2 := by
      gcongr
      · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left hdiscX (sq_nonneg _)
    _ = 2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log x ^ 2 := by
      ring

/-- The log-square Wold moment has universal leading coefficient `1/3`. -/
theorem tendsto_sourceHorizontalWoldNaturalCubicMoment_normalized :
    Tendsto (fun X : ℕ =>
      sourceHorizontalWoldNaturalCubicMoment X / Real.log X ^ 3)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun X : ℕ =>
      (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero'
      (Eventually.of_forall fun X =>
        abs_nonneg (sourceHorizontalWoldNaturalCubicMoment X /
          Real.log X ^ 3 - (1 / 3 : ℝ)))
      (show ∀ᶠ X : ℕ in atTop,
          |sourceHorizontalWoldNaturalCubicMoment X / Real.log X ^ 3 - (1 / 3 : ℝ)| ≤
            (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X by
        filter_upwards [eventually_ge_atTop 2] with X hX
        have hlogpos : 0 < Real.log (X : ℝ) :=
          Real.log_pos (by exact_mod_cast hX)
        have hbound :=
          abs_sourceHorizontalWoldNaturalCubicMoment_sub_main_le X (by omega)
        calc
          |sourceHorizontalWoldNaturalCubicMoment X / Real.log X ^ 3 - (1 / 3 : ℝ)| =
              |sourceHorizontalWoldNaturalCubicMoment X -
                (1 / 3 : ℝ) * Real.log X ^ 3| / Real.log X ^ 3 := by
                  rw [show sourceHorizontalWoldNaturalCubicMoment X /
                      Real.log X ^ 3 - (1 / 3 : ℝ) =
                        (sourceHorizontalWoldNaturalCubicMoment X -
                          (1 / 3 : ℝ) * Real.log X ^ 3) / Real.log X ^ 3 by
                        field_simp [hlogpos.ne']]
                  rw [abs_div, abs_of_pos (pow_pos hlogpos 3)]
          _ ≤ (2 * sourceHorizontalWoldFloorDiscrepancyBound * Real.log X ^ 2) /
              Real.log X ^ 3 :=
            div_le_div_of_nonneg_right hbound (pow_pos hlogpos 3).le
          _ = (2 * sourceHorizontalWoldFloorDiscrepancyBound) / Real.log X := by
            field_simp [hlogpos.ne'])
      hmajor

/-- At a prime cutoff the natural moment is literally the ordered, prime-labelled Wold moment. -/
theorem sourceHorizontalWoldNaturalCubicMoment_nthPrime_eq_ordered
    (N : ℕ) :
    sourceHorizontalWoldNaturalCubicMoment (nthPrimeSubtype N : ℕ) =
      ∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2 := by
  classical
  have hinj : Function.Injective (fun n : ℕ => (nthPrimeSubtype n : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  symm
  calc
    (∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2) =
      ∑ p ∈ (Finset.range (N + 1)).image
          (fun n => (nthPrimeSubtype n : ℕ)),
        Real.log (p : ℝ) ^ 2 * xiHeatCassiniWoldNatWeight p := by
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro n hn
            simp only [xiMassNthPrimeLogHeight, xiHeatCassiniWoldNatWeight,
              dif_pos (nthPrimeSubtype n).2]
            change woldCoeff 1 (nthPrimeSubtype n) *
                Real.log (nthPrimeSubtype n : ℝ) ^ 2 =
              Real.log (nthPrimeSubtype n : ℝ) ^ 2 *
                woldCoeff 1 (nthPrimeSubtype n)
            ring
          · exact hinj.injOn
    _ = ∑ p ∈ (Finset.Icc 0 (nthPrimeSubtype N : ℕ)).filter Nat.Prime,
        Real.log (p : ℝ) ^ 2 * xiHeatCassiniWoldNatWeight p := by
          rw [image_range_succ_nthPrimeSubtype_eq_primes_Icc]
    _ = ∑ p ∈ Finset.Icc 0 (nthPrimeSubtype N : ℕ),
        Real.log (p : ℝ) ^ 2 * xiHeatCassiniWoldNatWeight p := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro p hpIcc hpNotPrimeFilter
          have hnp : ¬ p.Prime := by
            intro hpPrime
            exact hpNotPrimeFilter (Finset.mem_filter.mpr ⟨hpIcc, hpPrime⟩)
          simp [xiHeatCassiniWoldNatWeight, hnp]
    _ = sourceHorizontalWoldNaturalCubicMoment (nthPrimeSubtype N : ℕ) := by
          rw [sourceHorizontalWoldNaturalCubicMoment]

/-- Cubic coefficient of the cofinal source-horizontal residual primitive.  The terminal
prime-holonomy contributes the subtracted log cube. -/
def sourceHorizontalWoldResidualPrimitiveCubicCoefficient (N : ℕ) : ℝ :=
  sourceHorizontalWoldNaturalCubicMoment (nthPrimeSubtype N : ℕ) -
    xiMassNthPrimeLogHeight N ^ 3

/-- Prime-clock normalization leaves the universal cubic coefficient `-2/3`. -/
theorem tendsto_sourceHorizontalWoldResidualPrimitiveCubicCoefficient_normalized :
    Tendsto (fun N : ℕ =>
      sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
        xiMassNthPrimeLogHeight N ^ 3)
      atTop (𝓝 (-2 / 3 : ℝ)) := by
  have hmoment :=
    tendsto_sourceHorizontalWoldNaturalCubicMoment_normalized.comp
      nthPrimeSubtype_strictMono.tendsto_atTop
  have hsub := hmoment.sub_const (1 : ℝ)
  have hsub' : Tendsto (fun N : ℕ =>
      sourceHorizontalWoldNaturalCubicMoment (nthPrimeSubtype N : ℕ) /
          xiMassNthPrimeLogHeight N ^ 3 - 1)
      atTop (𝓝 ((1 / 3 : ℝ) - 1)) := by
    simpa only [Function.comp_apply, xiMassNthPrimeLogHeight] using hsub
  convert hsub' using 1
  · funext N
    have hH : 0 < xiMassNthPrimeLogHeight N := xiMassNthPrimeLogHeight_pos N
    rw [sourceHorizontalWoldResidualPrimitiveCubicCoefficient]
    field_simp [hH.ne']
  · norm_num

/-- Multiplicity-labelled Xi cubic horizon response. -/
def sourceZeroHorizontalWoldPrimeClockCubicResponse
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  primeDepthBVWoldXiCenteredRate q.1 ^ 3 *
    (sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ 3)

/-- Each Xi copy has a finite, coefficient-faithful cubic horizon limit. -/
theorem tendsto_sourceZeroHorizontalWoldPrimeClockCubicResponse
    (q : XiZeroCopy) :
    Tendsto (sourceZeroHorizontalWoldPrimeClockCubicResponse q) atTop
      (𝓝 ((-2 / 3 : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ 3)) := by
  have h :=
    tendsto_sourceHorizontalWoldResidualPrimitiveCubicCoefficient_normalized.const_mul
      (primeDepthBVWoldXiCenteredRate q.1 ^ 3)
  simpa only [sourceZeroHorizontalWoldPrimeClockCubicResponse, mul_comm] using! h

/-- Line conjugation reverses the complete finite cubic horizon response. -/
@[simp] theorem sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection
    (q : XiZeroCopy) (N : ℕ) :
    sourceZeroHorizontalWoldPrimeClockCubicResponse
        (xiZeroCopyLineConjEquiv q) N =
      -sourceZeroHorizontalWoldPrimeClockCubicResponse q N := by
  rw [sourceZeroHorizontalWoldPrimeClockCubicResponse,
    sourceZeroHorizontalWoldPrimeClockCubicResponse]
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [hrate]
  ring

/-- The universal cubic horizon limit vanishes exactly on the critical line. -/
theorem sourceZeroHorizontalWoldPrimeClockCubicLimit_eq_zero_iff
    (q : XiZeroCopy) :
    (-2 / 3 : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ 3 = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hrpow : primeDepthBVWoldXiCenteredRate q.1 ^ 3 = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hr : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hrpow
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hr
  · intro hline
    have hr : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mpr hline
    rw [hr, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero]

end

end RHTower
