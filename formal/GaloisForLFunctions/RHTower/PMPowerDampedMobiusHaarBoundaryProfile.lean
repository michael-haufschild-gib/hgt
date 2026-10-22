import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPositiveHaarPrefix
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCenteredEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Boundary profile of the positive Haar prefixes: linear energy growth and `L¹` defect

The boundary profile `β(u) = min(1,1/u) − 2 min(1,1/(2u))` equals `−1` on `(0,1/2]`,
`1 − 1/u` on `[1/2,1]` and `0` for `u ≥ 1`; it lies in `L²(0,∞)` with
`∫ β² = 2 − 2 log 2 > 0` and `∫ β = −log 2`. For damping `ε > 0` the rescaled positive Haar
prefixes `P_{N+1}(u/(N+1))/(N+1)` converge to `β(u)/ζ(1+ε)` in `L²(0,∞)` by dominated
convergence, so `‖P_{N+1}‖²/(N+1) → |1/ζ(1+ε)|²(2 − 2 log 2)`. Hence the prefix energies grow
linearly and are unbounded, and since each prefix has integral `0` while the Fermi source has
integral `log 2/ζ(1+ε)`, the prefixes never converge to the source in `L¹(0,∞)`.

## Main results

- `pmPositiveHaarBoundaryProfile_energy`: `∫₀^∞ β(u)² du = 2 − 2 log 2`.
- `pmPositiveHaarBoundaryProfile_integral`: `∫₀^∞ β(u) du = −log 2`.
- `tendsto_pmPowerDampedRescaledHaarPrefix_L2`: for `ε > 0`, the rescaled prefixes converge to `β/ζ(1+ε)` in `L²(0,∞)`.
- `tendsto_pmPowerDampedPositiveHaarPrefix_energy_div`: `‖P_{N+1}‖²/(N+1) → |1/ζ(1+ε)|²(2 − 2 log 2)`.
- `not_bounded_pmPowerDampedPositiveHaarPrefix_energy`: for `ε > 0`, the prefix energies are unbounded.
- `pmPowerDampedPositiveHaarPrefix_L1_defect_lower`: `|log 2/ζ(1+ε)| ≤ ∫₀^∞ |P_N − F_ε|` for every `N`.
- `not_tendsto_pmPowerDampedPositiveHaarPrefix_L1`: for `ε > 0`, `P_N` does not converge to the Fermi source `F_ε` in `L¹(0,∞)`.

## Hypotheses

All results are unconditional; the asymptotic and obstruction statements assume only `0 < ε`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem measurable_pmPositiveHaarBoundaryProfile : Measurable pmPositiveHaarBoundaryProfile := by
  unfold pmPositiveHaarBoundaryProfile
  fun_prop

/-- On `(0,1/2]` the boundary profile equals `−1`. -/
theorem pmPositiveHaarBoundaryProfile_first {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    pmPositiveHaarBoundaryProfile u = -1 := by
  have h1 : (1 : ℝ) ≤ 1 / u := (le_div_iff₀ hu).mpr (by linarith)
  have h2 : (1 : ℝ) ≤ 1 / (2 * u) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  rw [pmPositiveHaarBoundaryProfile, min_eq_left h1, min_eq_left h2]
  norm_num

/-- On `[1/2,1]` the boundary profile equals `1 − 1/u`. -/
theorem pmPositiveHaarBoundaryProfile_middle {u : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    pmPositiveHaarBoundaryProfile u = 1 - 1 / u := by
  have hup : 0 < u := by linarith
  have h1 : (1 : ℝ) ≤ 1 / u := (le_div_iff₀ hup).mpr (by linarith)
  have h2 : 1 / (2 * u) ≤ (1 : ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [pmPositiveHaarBoundaryProfile, min_eq_left h1, min_eq_right h2]
  field_simp

/-- For `u ≥ 1` the boundary profile vanishes. -/
theorem pmPositiveHaarBoundaryProfile_tail {u : ℝ} (hu : 1 ≤ u) :
    pmPositiveHaarBoundaryProfile u = 0 := by
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h1 : 1 / u ≤ (1 : ℝ) := (div_le_iff₀ hup).mpr (by linarith)
  have h2 : 1 / (2 * u) ≤ (1 : ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [pmPositiveHaarBoundaryProfile, min_eq_right h1, min_eq_right h2]
  field_simp
  ring

/-- For `u > 0`, `|β(u)| ≤ min(1,1/u)`. -/
theorem norm_pmPositiveHaarBoundaryProfile_le {u : ℝ} (hu : 0 < u) :
    ‖pmPositiveHaarBoundaryProfile u‖ ≤ min 1 (1 / u) := by
  have ha : 0 ≤ min (1 : ℝ) (1 / u) := by positivity
  have hb : 0 ≤ min (1 : ℝ) (1 / (2 * u)) := by positivity
  have hba : min (1 : ℝ) (1 / (2 * u)) ≤ min 1 (1 / u) :=
    min_le_min_left 1 (one_div_le_one_div_of_le hu (by linarith))
  rw [Real.norm_eq_abs, pmPositiveHaarBoundaryProfile, abs_le]
  constructor <;> linarith

/-- The envelope `min(1,1/u)²` is integrable on `(0,∞)`. -/
theorem integrableOn_pmPositiveHaarEnvelope :
    IntegrableOn (fun u : ℝ => (min 1 (1 / u)) ^ 2) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) := integrable_const _
    refine hi.congr_fun ?_ measurableSet_Ioc
    intro u hu
    have hh : (1 : ℝ) ≤ 1 / u := (le_div_iff₀ hu.1).mpr (by simpa using hu.2)
    simp only [min_eq_left hh, one_pow]
  · have hi : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine hi.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hup : 0 < u := lt_trans one_pos hu
    have hh : 1 / u ≤ (1 : ℝ) := (div_le_iff₀ hup).mpr (by simpa using le_of_lt hu)
    dsimp only
    rw [min_eq_right hh, one_div, inv_sq_eq_rpow hup]

/-- The boundary profile lies in `L²(0,∞)`. -/
theorem memLp_pmPositiveHaarBoundaryProfile :
    MemLp pmPositiveHaarBoundaryProfile 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm measurable_pmPositiveHaarBoundaryProfile.aestronglyMeasurable]
  apply Integrable.mono' integrableOn_pmPositiveHaarEnvelope
    (measurable_pmPositiveHaarBoundaryProfile.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_pmPositiveHaarBoundaryProfile_le hu) 2

theorem measurable_pmPowerDampedRescaledHaarPrefix (ε : ℝ) (N : ℕ) :
    Measurable (pmPowerDampedRescaledHaarPrefix ε N) :=
  ((measurable_pmPowerDampedPositiveHaarPrefix ε (N + 1)).comp
    (measurable_id.div measurable_const)).div measurable_const

/-- For `ε > 0`, the rescaled prefixes `P_{N+1}(u/(N+1))/(N+1)` converge to `β(u)/ζ(1+ε)` in
`L²(0,∞)` (dominated convergence with majorant `36 min(1,1/u)²`). -/
theorem tendsto_pmPowerDampedRescaledHaarPrefix_L2 {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ∫ u in Ioi (0 : ℝ),
      ‖pmPowerDampedRescaledHaarPrefix ε N u -
        pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ^ 2)
      atTop (𝓝 0) := by
  have hp (u : ℝ) (hu : 0 < u) :
      ‖pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ≤
        3 * min 1 (1 / u) :=
    le_of_tendsto' (tendsto_pmPowerDampedRescaledHaarPrefix hε hu).norm
      (norm_pmPowerDampedRescaledHaarPrefix_le hε.le hu)
  have hm (N : ℕ) : Measurable (fun u : ℝ =>
      ‖pmPowerDampedRescaledHaarPrefix ε N u -
        pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ^ 2) :=
    ((measurable_pmPowerDampedRescaledHaarPrefix ε N).sub
      (measurable_const.mul (Complex.measurable_ofReal.comp
        measurable_pmPositiveHaarBoundaryProfile))).norm.pow_const 2
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun _ : ℝ => (0 : ℝ))
    (fun u : ℝ => 36 * (min 1 (1 / u)) ^ 2)
    (fun N => (hm N).aestronglyMeasurable)
    (integrableOn_pmPositiveHaarEnvelope.const_mul 36) ?_ ?_
  · simpa only [integral_zero] using hh
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hq := norm_pmPowerDampedRescaledHaarPrefix_le hε.le hu N
    have hd := norm_sub_le (pmPowerDampedRescaledHaarPrefix ε N u)
      (pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ))
    have he : ‖pmPowerDampedRescaledHaarPrefix ε N u -
        pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ≤
        6 * min 1 (1 / u) := by linarith [hp u hu]
    calc _ ≤ (6 * min 1 (1 / u)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa using ((tendsto_pmPowerDampedRescaledHaarPrefix hε hu).sub_const
      (pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ))).norm.pow 2

/-- The boundary profile has energy `∫₀^∞ β(u)² du = 2 − 2 log 2`. -/
theorem pmPositiveHaarBoundaryProfile_energy :
    (∫ u in Ioi (0 : ℝ), (pmPositiveHaarBoundaryProfile u) ^ 2) = 2 - 2 * Real.log 2 := by
  have hi : IntegrableOn (fun u => (pmPositiveHaarBoundaryProfile u) ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, sq_abs] using
      memLp_pmPositiveHaarBoundaryProfile.norm.integrable_sq
  have hhead : (∫ u in Ioc (0 : ℝ) (1 / 2), (pmPositiveHaarBoundaryProfile u) ^ 2) = 1 / 2 := by
    have he (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) (1 / 2)) :
        (pmPositiveHaarBoundaryProfile u) ^ 2 = 1 := by
      rw [pmPositiveHaarBoundaryProfile_first hu.1 hu.2]
      norm_num
    rw [setIntegral_congr_fun measurableSet_Ioc he,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      intervalIntegral.integral_const]
    norm_num
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    exact (continuousAt_inv₀ (by linarith [hx.1] : x ≠ 0)).continuousWithinAt
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1 / 2) 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hinv2 : IntervalIntegrable (fun x : ℝ => (x⁻¹) ^ 2) volume (1 / 2) 1 :=
    (hc.pow 2).intervalIntegrable_of_Icc (by norm_num)
  have hinv2val : (∫ x : ℝ in (1 / 2)..1, (x⁻¹) ^ 2) = 1 := by
    have h := integral_zpow (a := (1 / 2 : ℝ)) (b := 1) (n := -2)
      (Or.inr ⟨by norm_num, by norm_num [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]⟩)
    norm_num [zpow_neg, inv_pow] at h ⊢
    exact h
  have hmiddle : (∫ u in Ioc (1 / 2 : ℝ) 1, (pmPositiveHaarBoundaryProfile u) ^ 2) =
      3 / 2 - 2 * Real.log 2 := by
    have he (u : ℝ) (hu : u ∈ Ioc (1 / 2 : ℝ) 1) :
        (pmPositiveHaarBoundaryProfile u) ^ 2 = 1 - 2 * u⁻¹ + (u⁻¹) ^ 2 := by
      rw [pmPositiveHaarBoundaryProfile_middle hu.1.le hu.2, one_div]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc he,
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      intervalIntegral.integral_add (intervalIntegrable_const.sub (hinv.const_mul 2)) hinv2,
      intervalIntegral.integral_sub intervalIntegrable_const (hinv.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_inv_of_pos (by norm_num) one_pos, hinv2val]
    norm_num; ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integral_union_eq_left_of_forall measurableSet_Ioi (fun u hu => by
      rw [pmPositiveHaarBoundaryProfile_tail (le_of_lt hu)]; norm_num),
    ← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union]
  · rw [hhead, hmiddle]
    ring
  · exact disjoint_left.mpr (fun u hu hv => (not_lt_of_ge hu.2) hv.1)
  · exact measurableSet_Ioc
  · exact hi.mono_set (fun u hu => hu.1)
  · exact hi.mono_set (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hu.1)

/-- The profile energy `2 − 2 log 2` is positive. -/
theorem pmPositiveHaarBoundaryProfile_energy_pos : 0 < 2 - 2 * Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  linarith

/-- The boundary profile has integral `∫₀^∞ β(u) du = −log 2`. -/
theorem pmPositiveHaarBoundaryProfile_integral :
    (∫ u in Ioi (0 : ℝ), pmPositiveHaarBoundaryProfile u) = -Real.log 2 := by
  have hi : IntegrableOn pmPositiveHaarBoundaryProfile (Ioc (0 : ℝ) 1) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) (integrable_const _)
      measurable_pmPositiveHaarBoundaryProfile.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (norm_pmPositiveHaarBoundaryProfile_le hu.1).trans (min_le_left _ _)
  have hhead : (∫ u in Ioc (0 : ℝ) (1 / 2), pmPositiveHaarBoundaryProfile u) = -1 / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu =>
      pmPositiveHaarBoundaryProfile_first hu.1 hu.2),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      intervalIntegral.integral_const]
    norm_num
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    exact (continuousAt_inv₀ (by linarith [hx.1] : x ≠ 0)).continuousWithinAt
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1 / 2) 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hmiddle : (∫ u in Ioc (1 / 2 : ℝ) 1, pmPositiveHaarBoundaryProfile u) =
      1 / 2 - Real.log 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu =>
      pmPositiveHaarBoundaryProfile_middle hu.1.le hu.2),
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    simp only [one_div]
    simp only [one_div] at hinv
    rw [intervalIntegral.integral_sub intervalIntegrable_const hinv,
      intervalIntegral.integral_const, integral_inv_of_pos (by norm_num) one_pos]
    norm_num
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integral_union_eq_left_of_forall measurableSet_Ioi (fun u hu =>
      pmPositiveHaarBoundaryProfile_tail (le_of_lt hu)),
    ← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union]
  · rw [hhead, hmiddle]
    ring
  · exact disjoint_left.mpr (fun u hu hv => (not_lt_of_ge hu.2) hv.1)
  · exact measurableSet_Ioc
  · exact hi.mono_set (fun u hu => ⟨hu.1, hu.2.trans (by norm_num)⟩)
  · exact hi.mono_set (fun u hu => ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hu.1, hu.2⟩)

/-- Rescaling identity: the energy of the rescaled prefix is `‖P_{N+1}‖²_{L²(0,∞)}/(N+1)`. -/
theorem pmPowerDampedRescaledHaarPrefix_energy (ε : ℝ) (N : ℕ) :
    (∫ u in Ioi (0 : ℝ), ‖pmPowerDampedRescaledHaarPrefix ε N u‖ ^ 2) =
      (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε (N + 1) t‖ ^ 2) / ((N : ℝ) + 1) := by
  have hh := pmBackwardDilation_energy (pmPowerDampedPositiveHaarPrefix ε (N + 1))
    (show (0 : ℝ) < (N : ℝ) + 1 by positivity)
  simpa only [pmPowerDampedRescaledHaarPrefix, pmBackwardDilation, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one, div_eq_mul_inv, mul_comm] using hh

/-- For `ε > 0`, the rescaled prefix energies converge to `|1/ζ(1+ε)|²(2 − 2 log 2)`. -/
theorem tendsto_pmPowerDampedRescaledHaarPrefix_energy {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ∫ u in Ioi (0 : ℝ), ‖pmPowerDampedRescaledHaarPrefix ε N u‖ ^ 2)
      atTop (𝓝 (‖pmPowerDampedDivisorDensity ε‖ ^ 2 * (2 - 2 * Real.log 2))) := by
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u : ℝ => ‖pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ^ 2)
    (fun u : ℝ => 9 * (min 1 (1 / u)) ^ 2)
    (fun N => ((measurable_pmPowerDampedRescaledHaarPrefix ε N).norm.pow_const 2).aestronglyMeasurable)
    (integrableOn_pmPositiveHaarEnvelope.const_mul 9) ?_ ?_
  · have he (u : ℝ) : ‖pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ)‖ ^ 2 =
        ‖pmPowerDampedDivisorDensity ε‖ ^ 2 * (pmPositiveHaarBoundaryProfile u) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simpa only [he, integral_const_mul, pmPositiveHaarBoundaryProfile_energy] using hh
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc _ ≤ (3 * min 1 (1 / u)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_pmPowerDampedRescaledHaarPrefix_le hε.le hu N) 2
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (tendsto_pmPowerDampedRescaledHaarPrefix hε hu).norm.pow 2

/-- For `ε > 0`, `‖P_{N+1}‖²/(N+1) → |1/ζ(1+ε)|²(2 − 2 log 2)`: the prefix energy grows
linearly in `N`. -/
theorem tendsto_pmPowerDampedPositiveHaarPrefix_energy_div {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε (N + 1) t‖ ^ 2) / ((N : ℝ) + 1))
      atTop (𝓝 (‖pmPowerDampedDivisorDensity ε‖ ^ 2 * (2 - 2 * Real.log 2))) := by
  simpa only [pmPowerDampedRescaledHaarPrefix_energy] using
    tendsto_pmPowerDampedRescaledHaarPrefix_energy hε

/-- For `ε > 0`, the energies `‖P_{N+1}‖²_{L²(0,∞)}` tend to infinity. -/
theorem tendsto_pmPowerDampedPositiveHaarPrefix_energy_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε (N + 1) t‖ ^ 2)
      atTop atTop := by
  have hc : 0 < ‖pmPowerDampedDivisorDensity ε‖ ^ 2 * (2 - 2 * Real.log 2) :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (pmPowerDampedDivisorDensity_ne_zero hε)))
      pmPositiveHaarBoundaryProfile_energy_pos
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh := (tendsto_pmPowerDampedPositiveHaarPrefix_energy_div hε).pos_mul_atTop hc hN
  apply hh.congr'
  filter_upwards with N
  exact div_mul_cancel₀ _ (ne_of_gt (show (0 : ℝ) < (N : ℝ) + 1 by positivity))

/-- For `ε > 0`, no real `B` bounds the energies of all positive Haar prefixes `P_N`. -/
theorem not_bounded_pmPowerDampedPositiveHaarPrefix_energy {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ B : ℝ, ∀ N : ℕ,
      (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε N t‖ ^ 2) ≤ B := by
  rintro ⟨B, hB⟩
  have hh := (tendsto_pmPowerDampedPositiveHaarPrefix_energy_atTop hε).eventually
    (eventually_gt_atTop B)
  rcases hh.exists with ⟨N, hN⟩
  exact (not_lt_of_ge (hB (N + 1))) hN

/-- For `ε > 0` and every `N`, `|log 2/ζ(1+ε)| ≤ ∫₀^∞ |P_N(t) − F_ε(t)| dt`, because `P_N` has
integral `0` and the Fermi source has integral `log 2/ζ(1+ε)`. -/
theorem pmPowerDampedPositiveHaarPrefix_L1_defect_lower {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ‖pmPowerDampedDivisorDensity ε * (Real.log 2 : ℂ)‖ ≤
      ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖ := by
  have hh := norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun t => pmPowerDampedPositiveHaarPrefix ε N t - pmPowerDampedFermiSource ε t)
  rw [integral_sub (integrable_pmPowerDampedPositiveHaarPrefix ε N)
    (integrable_pmPowerDampedFermiSource hε), pmPowerDampedPositiveHaarPrefix_integral,
    pmPowerDampedFermiSource_integral hε, zero_sub, norm_neg] at hh
  simpa only [pmPowerDampedDivisorDensity, one_div, div_eq_mul_inv, one_mul, mul_comm] using hh

/-- For `ε > 0`, the positive Haar prefixes do not converge to the power-damped Fermi source in
`L¹(0,∞)`. -/
theorem not_tendsto_pmPowerDampedPositiveHaarPrefix_L1 {ε : ℝ} (hε : 0 < ε) :
    ¬ Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ),
      ‖pmPowerDampedPositiveHaarPrefix ε N t - pmPowerDampedFermiSource ε t‖) atTop (𝓝 0) := by
  intro ht
  have hc : 0 < ‖pmPowerDampedDivisorDensity ε * (Real.log 2 : ℂ)‖ := by
    apply norm_pos_iff.mpr
    apply mul_ne_zero (pmPowerDampedDivisorDensity_ne_zero hε)
    exact_mod_cast (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall (pmPowerDampedPositiveHaarPrefix_L1_defect_lower hε))
  exact (not_le_of_gt hc) hh

end RHTower
