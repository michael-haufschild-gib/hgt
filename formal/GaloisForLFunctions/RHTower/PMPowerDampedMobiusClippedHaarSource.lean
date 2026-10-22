import GaloisForLFunctions.RHTower.PMPowerDampedMobiusHaarBoundaryProfile
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy

/-!
# Clipped centered sources and repaired Haar prefixes

The clipped centered source `G_{ε,a}(t) = R_ε(min(a, 1/t))` freezes the divisor remainder
`R_ε(x) = ∑_{n ≤ x} c_ε(n) - x/ζ(1+ε)` at height `a`: it is the constant `R_ε(a)` on `(0, 1/a]`
and agrees with the centered source `G_ε(t) = R_ε(1/t)` for `t ≥ 1/a`. The linear bound
`|R_ε(x)| ≤ (1 + |1/ζ(1+ε)|) x` shows `G_{ε,a} ∈ L²(0, ∞)` for every `ε ≥ 0`, `a > 0`, with
energy `|R_ε(a)|²/a + ∫_{t > 1/a} |G_ε(t)|² dt`. The repaired Haar prefix (the positive Haar
prefix minus a density-weighted boundary profile) equals the dyadic difference
`G_{ε,N}(t) - 2 G_{ε,N}(2t)`, so it is square integrable and coincides with `F_ε(t)` once
`N ≥ 1/t`. The forward dyadic difference `f(t) - 2 f(2t)` has `L²` norm between
`(√2 - 1) ‖f‖` and `(√2 + 1) ‖f‖`.

## Main results

- `memLp_pmPowerDampedClippedCenteredSource`: `G_{ε,a} ∈ L²(0, ∞)` for `ε ≥ 0`, `a > 0`.
- `pmPowerDampedRepairedHaarPrefix_eq_clipped`: the repaired prefix equals
  `G_{ε,N}(t) - 2 G_{ε,N}(2t)` for `N ≥ 1`, `t > 0`.
- `memLp_pmPowerDampedRepairedHaarPrefix`: the repaired prefix is in `L²(0, ∞)`.
- `pmPowerDampedClippedCenteredSource_energy`: `‖G_{ε,a}‖₂² = ∫_{(0,a]} |R_ε(x)|²/x² dx + |R_ε(a)|²/a`.
- `pmPowerDampedClippedCenteredSource_physical_energy`:
  `‖G_{ε,a}‖₂² = |R_ε(a)|²/a + ∫_{t > 1/a} |G_ε(t)|² dt`.
- `pmForwardDyadicDifference_lpNorm_bounds`: `(√2 - 1)‖f‖₂ ≤ ‖f - 2 f(2·)‖₂ ≤ (√2 + 1)‖f‖₂`.
- `tendsto_pmPowerDampedRepairedHaarPrefix`: the repaired prefixes converge pointwise to `F_ε(t)`.

## Hypotheses

All results are unconditional. They assume only `0 ≤ ε`, positivity of the clipping height `a`
or `N ≥ 1`, positivity of `t`, and, for the dyadic difference bounds, measurability and square
integrability of `f`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- The clipped centered source `G_{ε,a}(t) = R_ε(min(a, 1/t))`. -/
def pmPowerDampedClippedCenteredSource (ε a t : ℝ) : ℂ :=
  pmPowerDampedDivisorRemainder ε (min a (1 / t))

theorem measurable_pmPowerDampedClippedCenteredSource (ε a : ℝ) :
    Measurable (pmPowerDampedClippedCenteredSource ε a) := by
  exact (measurable_pmPowerDampedDivisorRemainder ε).comp
    (measurable_const.min (measurable_const.div measurable_id))

/-- For `a > 0` and `t ∈ (0, 1/a]`, the clipped source is the constant `R_ε(a)`. -/
theorem pmPowerDampedClippedCenteredSource_initial (ε : ℝ) {a t : ℝ}
    (ha : 0 < a) (ht : t ∈ Ioc 0 (1 / a)) :
    pmPowerDampedClippedCenteredSource ε a t = pmPowerDampedDivisorRemainder ε a := by
  have h : a ≤ 1 / t := (le_div_iff₀ ht.1).mpr (by simpa only [mul_comm] using (le_div_iff₀ ha).mp ht.2)
  rw [pmPowerDampedClippedCenteredSource, min_eq_left h]

/-- For `a > 0` and `t ≥ 1/a`, the clipped source equals the centered source `G_ε(t)`. -/
theorem pmPowerDampedClippedCenteredSource_tail (ε : ℝ) {a t : ℝ}
    (ha : 0 < a) (ht : 1 / a ≤ t) :
    pmPowerDampedClippedCenteredSource ε a t = pmPowerDampedCenteredSource ε t := by
  have ht0 : 0 < t := lt_of_lt_of_le (one_div_pos.mpr ha) ht
  have h : 1 / t ≤ a := (div_le_iff₀ ht0).mpr (by simpa only [mul_comm] using (div_le_iff₀ ha).mp ht)
  rw [pmPowerDampedClippedCenteredSource, min_eq_right h]
  rfl

theorem pm_scaled_min_inv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    a * min 1 (1 / (a * t)) = min a (1 / t) := by
  rw [mul_min_of_nonneg _ _ ha.le, mul_one]
  congr 1
  field_simp

/-- For `a > 0`, `t ↦ min(a, 1/t)²` is integrable on `(0, ∞)`. -/
theorem integrableOn_pm_clipped_inv_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (min a (1 / t)) ^ 2) (Ioi (0 : ℝ)) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => (min 1 (1 / t)) ^ 2) 0 ha).mpr
    (by simpa only [mul_zero] using integrableOn_pmPositiveHaarEnvelope)
  have h : IntegrableOn (fun t : ℝ => a ^ 2 * (min 1 (1 / (a * t))) ^ 2)
      (Ioi (0 : ℝ)) := hi.const_mul (a ^ 2)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  dsimp only
  rw [← mul_pow, pm_scaled_min_inv ha]

/-- Linear bound on the remainder: for `ε ≥ 0` and `x ≥ 0`,
`|R_ε(x)| ≤ (1 + |1/ζ(1+ε)|) x`. -/
theorem norm_pmPowerDampedDivisorRemainder_le {ε : ℝ} (hε : 0 ≤ ε)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖pmPowerDampedDivisorRemainder ε x‖ ≤ (1 + ‖pmPowerDampedDivisorDensity ε‖) * x := by
  calc
    _ ≤ ‖(pmPowerDampedDivisorSum ε x : ℂ)‖ +
        ‖pmPowerDampedDivisorDensity ε * (x : ℂ)‖ := norm_sub_le _ _
    _ = pmPowerDampedDivisorSum ε x + ‖pmPowerDampedDivisorDensity ε‖ * x := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (pmPowerDampedDivisorSum_nonneg hε x),
        abs_of_nonneg hx]
    _ ≤ x + ‖pmPowerDampedDivisorDensity ε‖ * x :=
      by linarith [pmPowerDampedDivisorSum_le hε hx]
    _ = _ := by ring

/-- For `ε ≥ 0` and `a > 0`, the clipped centered source `G_{ε,a}` lies in `L²(0, ∞)`. -/
theorem memLp_pmPowerDampedClippedCenteredSource {ε a : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) :
    MemLp (pmPowerDampedClippedCenteredSource ε a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_pmPowerDampedClippedCenteredSource ε a).aestronglyMeasurable]
  apply Integrable.mono'
    ((integrableOn_pm_clipped_inv_sq ha).const_mul ((1 + ‖pmPowerDampedDivisorDensity ε‖) ^ 2))
    ((measurable_pmPowerDampedClippedCenteredSource ε a).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have ht0 : 0 < t := ht
  have hn : 0 ≤ min a (1 / t) := le_min ha.le (by positivity)
  calc
    _ ≤ ((1 + ‖pmPowerDampedDivisorDensity ε‖) * min a (1 / t)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pmPowerDampedDivisorRemainder_le hε hn) 2
    _ = _ := mul_pow _ _ _

/-- The repaired Haar prefix `∑_{n ≤ N} c_ε(n) H(n t) - N B(N t)/ζ(1+ε)`, where
`B(u) = min(1, 1/u) - 2 min(1, 1/(2u))` is the positive Haar boundary profile. -/
def pmPowerDampedRepairedHaarPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  pmPowerDampedPositiveHaarPrefix ε N t -
    pmPowerDampedDivisorDensity ε * (N : ℂ) * (pmPositiveHaarBoundaryProfile ((N : ℝ) * t) : ℂ)

/-- For `N ≥ 1` and `t > 0`, the repaired Haar prefix is the dyadic difference of the clipped
source: `G_{ε,N}(t) - 2 G_{ε,N}(2t)`. -/
theorem pmPowerDampedRepairedHaarPrefix_eq_clipped (ε : ℝ) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedRepairedHaarPrefix ε N t =
      pmPowerDampedClippedCenteredSource ε N t -
        2 * pmPowerDampedClippedCenteredSource ε N (2 * t) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : (N : ℝ) * pmPositiveHaarBoundaryProfile ((N : ℝ) * t) =
      min (N : ℝ) (1 / t) - 2 * min (N : ℝ) (1 / (2 * t)) := by
    rw [pmPositiveHaarBoundaryProfile, mul_sub, pm_scaled_min_inv hNp]
    rw [show (2 : ℝ) * ((N : ℝ) * t) = (N : ℝ) * (2 * t) by ring,
      show (N : ℝ) * (2 * min 1 (1 / ((N : ℝ) * (2 * t)))) =
        2 * ((N : ℝ) * min 1 (1 / ((N : ℝ) * (2 * t)))) by ring,
      pm_scaled_min_inv hNp]
  rw [pmPowerDampedRepairedHaarPrefix, pmPowerDampedPositiveHaarPrefix_eq_clipped_counts ε N ht]
  simp only [pmPowerDampedClippedCenteredSource, pmPowerDampedDivisorRemainder]
  have hbc := congrArg (fun x : ℝ => (x : ℂ)) hb
  push_cast at hbc
  linear_combination -pmPowerDampedDivisorDensity ε * hbc

/-- For `ε ≥ 0` and `N ≥ 1`, the repaired Haar prefix lies in `L²(0, ∞)`. -/
theorem memLp_pmPowerDampedRepairedHaarPrefix {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) :
    MemLp (pmPowerDampedRepairedHaarPrefix ε N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hf := memLp_pmPowerDampedClippedCenteredSource hε hNp
  have hd := (pm_memLp_pos_dilate (measurable_pmPowerDampedClippedCenteredSource ε N) hf
    (by norm_num : (0 : ℝ) < 2)).const_mul (2 : ℂ)
  apply (memLp_congr_ae ?_).mp (hf.sub hd)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (pmPowerDampedRepairedHaarPrefix_eq_clipped ε hN ht).symm

/-- For `ε ≥ 0` and `a > 0`, `∫_0^∞ |G_{ε,a}(t)|² dt = ∫_{(0,a]} |R_ε(x)|²/x² dx + |R_ε(a)|²/a`. -/
theorem pmPowerDampedClippedCenteredSource_energy {ε a : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedClippedCenteredSource ε a t‖ ^ 2) =
      (∫ x in Ioc (0 : ℝ) a, ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) +
        ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 / a := by
  have hi : IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε (min a x)‖ ^ 2 / x ^ 2)
      (Ioi (0 : ℝ)) :=
    (pm_integrable_normSq_reciprocal_iff
      (fun x => pmPowerDampedDivisorRemainder ε (min a x))).mp
      (memLp_pmPowerDampedClippedCenteredSource hε ha).norm.integrable_sq
  have hhead := hi.mono_set (show Ioc 0 a ⊆ Ioi (0 : ℝ) from fun _ hx => hx.1)
  have htail := hi.mono_set (Ioi_subset_Ioi ha.le)
  have he := pm_integral_normSq_reciprocal
    (fun x => pmPowerDampedDivisorRemainder ε (min a x))
  change (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedClippedCenteredSource ε a t‖ ^ 2) = _ at he
  rw [he, ← Ioc_union_Ioi_eq_Ioi ha.le,
    setIntegral_union (by simp) measurableSet_Ioi hhead htail]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [min_eq_right hx.2]
  · have ht : (∫ x in Ioi a, ‖pmPowerDampedDivisorRemainder ε (min a x)‖ ^ 2 / x ^ 2) =
        ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 * ∫ x in Ioi a, x ^ (-2 : ℝ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := ha.trans hx
      dsimp only
      rw [min_eq_left (le_of_lt hx), div_eq_mul_inv, ← inv_pow, inv_sq_eq_rpow hx0]
    rw [ht, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- For `ε ≥ 0` and `a > 0`, `∫_0^∞ |G_{ε,a}(t)|² dt = |R_ε(a)|²/a + ∫_{t > 1/a} |G_ε(t)|² dt`. -/
theorem pmPowerDampedClippedCenteredSource_physical_energy {ε a : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖pmPowerDampedClippedCenteredSource ε a t‖ ^ 2) =
      ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 / a +
        ∫ t in Ioi (1 / a), ‖pmPowerDampedCenteredSource ε t‖ ^ 2 := by
  have hi : IntegrableOn (fun t => ‖pmPowerDampedClippedCenteredSource ε a t‖ ^ 2)
      (Ioi (0 : ℝ)) := (memLp_pmPowerDampedClippedCenteredSource hε ha).norm.integrable_sq
  have hcut : 0 ≤ 1 / a := by positivity
  rw [← Ioc_union_Ioi_eq_Ioi hcut,
    setIntegral_union (by simp) measurableSet_Ioi
      (hi.mono_set (fun _ hx => hx.1)) (hi.mono_set (Ioi_subset_Ioi hcut))]
  congr 1
  · have he (t : ℝ) (ht : t ∈ Ioc 0 (1 / a)) :
        ‖pmPowerDampedClippedCenteredSource ε a t‖ ^ 2 =
          ‖pmPowerDampedDivisorRemainder ε a‖ ^ 2 := by
      rw [pmPowerDampedClippedCenteredSource_initial ε ha ht]
    rw [setIntegral_congr_fun measurableSet_Ioc he,
      ← intervalIntegral.integral_of_le hcut, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [pmPowerDampedClippedCenteredSource_tail ε ha (le_of_lt ht)]

/-- The forward dyadic difference `(Δ f)(t) = f(t) - 2 f(2t)`. -/
def pmForwardDyadicDifference (f : ℝ → ℂ) (t : ℝ) : ℂ := f t - 2 * f (2 * t)

theorem measurable_pmForwardDyadicDifference {f : ℝ → ℂ} (hm : Measurable f) :
    Measurable (pmForwardDyadicDifference f) :=
  hm.sub (measurable_const.mul (hm.comp (measurable_const.mul measurable_id)))

theorem pmForwardDyadicDifference_eq (f : ℝ → ℂ) :
    pmForwardDyadicDifference f = f - pmBackwardDilation f (1 / 2) := by
  funext t
  simp only [pmForwardDyadicDifference, Pi.sub_apply, pmBackwardDilation,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  congr 1
  rw [show t / (1 / 2 : ℝ) = 2 * t by ring]
  ring

theorem memLp_pmForwardDyadicDifference {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (pmForwardDyadicDifference f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [pmForwardDyadicDifference_eq]
  exact hf.sub (memLp_pmBackwardDilation hm hf (by norm_num))

/-- For measurable `f ∈ L²(0, ∞)`, `t ↦ 2 f(2t)` has norm `√2 ‖f‖₂`. -/
theorem pmBackwardDilation_half_lpNorm {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    lpNorm (pmBackwardDilation f (1 / 2)) 2 (volume.restrict (Ioi (0 : ℝ))) =
      Real.sqrt 2 * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have h := pmBackwardDilation_lpNorm_sq hm hf (a := 1 / 2) (by norm_num)
  norm_num at h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg := lpNorm_nonneg (f := pmBackwardDilation f (1 / 2))
    (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
  have hprod := mul_nonneg (Real.sqrt_nonneg 2)
    (lpNorm_nonneg (f := f) (p := 2) (μ := volume.restrict (Ioi (0 : ℝ))))
  nlinarith [sq_nonneg (lpNorm (pmBackwardDilation f (1 / 2)) 2
    (volume.restrict (Ioi (0 : ℝ))) + Real.sqrt 2 * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))))]

/-- Two-sided norm bounds for the dyadic difference on `L²(0, ∞)`:
`(√2 - 1) ‖f‖₂ ≤ ‖f(·) - 2 f(2·)‖₂ ≤ (√2 + 1) ‖f‖₂`. -/
theorem pmForwardDyadicDifference_lpNorm_bounds {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (Real.sqrt 2 - 1) * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) ≤
        lpNorm (pmForwardDyadicDifference f) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      lpNorm (pmForwardDyadicDifference f) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
        (Real.sqrt 2 + 1) * lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [pmForwardDyadicDifference_eq]
  have hu := lpNorm_sub_le hf (g := pmBackwardDilation f (1 / 2)) (by norm_num)
  have hl := lpNorm_le_lpNorm_add_lpNorm_sub hf
    (f := pmBackwardDilation f (1 / 2)) (by norm_num)
  rw [pmBackwardDilation_half_lpNorm hm hf] at hu hl
  constructor <;> linarith

theorem measurable_pmPowerDampedRepairedHaarPrefix (ε : ℝ) (N : ℕ) :
    Measurable (pmPowerDampedRepairedHaarPrefix ε N) := by
  exact (measurable_pmPowerDampedPositiveHaarPrefix ε N).sub
    (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_pmPositiveHaarBoundaryProfile.comp (measurable_const.mul measurable_id))))

/-- For `t > 0` and `N ≥ 1/t`, the repaired Haar prefix equals the Fermi source `F_ε(t)`. -/
theorem pmPowerDampedRepairedHaarPrefix_eq_source (ε : ℝ) (N : ℕ)
    {t : ℝ} (ht : 0 < t) (hN : 1 / t ≤ (N : ℝ)) :
    pmPowerDampedRepairedHaarPrefix ε N t = pmPowerDampedFermiSource ε t := by
  have hNt : 1 ≤ (N : ℝ) * t := (div_le_iff₀ ht).mp hN
  rw [pmPowerDampedRepairedHaarPrefix,
    pmPowerDampedPositiveHaarPrefix_eq_source ε N ht hN,
    pmPositiveHaarBoundaryProfile_tail hNt]
  simp

/-- For `t > 0`, the repaired Haar prefixes converge to `F_ε(t)` as `N → ∞` (they are
eventually constant). -/
theorem tendsto_pmPowerDampedRepairedHaarPrefix (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmPowerDampedRepairedHaarPrefix ε N t) atTop
      (𝓝 (pmPowerDampedFermiSource ε t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (1 / t))]
    with N hN
  exact (pmPowerDampedRepairedHaarPrefix_eq_source ε N ht hN).symm

end RHTower
