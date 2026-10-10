import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailSelberg

/-!
# The cosine producer down to the critical scale

For `h > 0` a non-real zero `z` of `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2` lies in the defect disk of a
zero `w` of `Ξ` with `|Im w| > h`. In `s = ½ + iz` coordinates: there is a zero `ρ` of `ξ` with

  `|Re ρ − ½| > h`   and   `|Re z − Im ρ| ≤ √((Re ρ − ½)² − h²) ≤ |Re ρ − ½|`

(`exists_xiZero_shadow_of_cosineShift_nonreal`). So the real part of every non-real zero of `A_h`
lies in the *shadow* `{t : |t − Im ρ| ≤ |Re ρ − ½|}` of a zero deeper than `h`. Only the local
radius `√(b² − h²) ≤ b` gives this; the global strip theorem does not.

Selberg's mollifier bounds the measure of the shadows of the zeros at distance `≥ κ/log V` from the
line by `(g(κ/2) + η)(V + 1)/π`, with `g(R) = −log(1 − e^{−2R/15}) → 0`
(`eventually_volume_kappaShadow_le_selberg`). Hence:

* `eventually_volume_cosineShift_nonrealHeight_le_criticalScale`: for all large `V`, the heights
  in `[20, V]` carrying a non-real zero of `A_h` for *some* depth `h ≥ κ/log V` have measure at most
  `(g(κ/2) + η)(V + 1)/π`;
* `exists_criticalScale_cosineShift_lossless_ae`: for every `ε > 0` there is `κ` such that, for
  all large `V`, these heights have measure at most `εV`.

For a single depth the set of such heights is countable; the union over all depths
`h ≥ κ/log V` is the meaningful object.

So the lossless producer `cos(hD)Ξ` continues, at almost every height, down to depths of the
critical order `1/log V`, unconditionally. Below that scale the defect is the Riemann hypothesis.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- A non-real zero of `cos(hD)Ξ` lies in the shadow of a zero of `ξ` deeper than `h`. -/
theorem exists_xiZero_shadow_of_cosineShift_nonreal {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ h < |ρ.re - 1 / 2| ∧ |z.re - ρ.im| ≤ |ρ.re - 1 / 2| := by
  obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hh hz h0
  have hzim : 0 < z.im ^ 2 := by positivity
  refine ⟨1 / 2 + w * I, by rw [← hw, XiC], ?_, ?_⟩
  · have hre : (1 / 2 + w * I).re - 1 / 2 = -w.im := by simp
    rw [hre, abs_neg]
    have h1 : h ^ 2 < w.im ^ 2 := by nlinarith [sq_nonneg (w.re - z.re)]
    have := sq_lt_sq.mp h1
    rwa [abs_of_pos hh] at this
  · have hre : (1 / 2 + w * I).re - 1 / 2 = -w.im := by simp
    have him : (1 / 2 + w * I).im = w.re := by simp
    rw [hre, abs_neg, him]
    have h1 : (z.re - w.re) ^ 2 ≤ w.im ^ 2 := by nlinarith [sq_nonneg h]
    exact sq_le_sq.mp h1

/-- `g(R) = −log(1 − e^{−2R/15}) → 0`. -/
theorem tendsto_selbergTailRate : Tendsto selbergTailRate atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => Real.exp (-(2 * R / 15))) atTop (𝓝 0) := by
    have : Tendsto (fun R : ℝ => -(2 * R / 15)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const
        (by norm_num))
    exact Real.tendsto_exp_atBot.comp this
  have hcont : ContinuousAt (fun x : ℝ => -Real.log (1 - x)) 0 := by
    have : ContinuousAt (fun x : ℝ => 1 - x) 0 := by fun_prop
    exact (Real.continuousAt_log (by norm_num)).comp this |>.neg
  have h2 := hcont.tendsto.comp h1
  have hlim : (-Real.log (1 - 0) : ℝ) = 0 := by simp
  rw [hlim] at h2
  unfold selbergTailRate
  exact h2

/-- **Critical-scale producer.** For all large `V`, the heights in `[20, V]` carrying a non-real
zero of `cos(hD)Ξ` for some `h ≥ κ/log V` have measure at most `(g(κ/2) + η)(V + 1)/π`. -/
theorem eventually_volume_cosineShift_nonrealHeight_le_criticalScale {κ η : ℝ} (hκ : 0 < κ)
    (hη : 0 < η) :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, κ / Real.log V ≤ h ∧
        ∃ z : ℂ, z.re = t ∧ z.im ≠ 0 ∧ (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0}
        ≤ ENNReal.ofReal ((selbergTailRate (κ / 2) + η) * (V + 1) / Real.pi) := by
  filter_upwards [eventually_volume_kappaShadow_le_selberg hκ hη, eventually_gt_atTop (1 : ℝ)]
    with V hV hV1
  have hlog : 0 < Real.log V := Real.log_pos hV1
  refine le_trans (measure_mono ?_) hV
  rintro t ⟨ht, h, hh, z, hzt, hz, h0⟩
  have hhpos : 0 < h := lt_of_lt_of_le (by positivity) hh
  obtain ⟨ρ, hρ, hdeep, hshadow⟩ := exists_xiZero_shadow_of_cosineShift_nonreal hhpos hz h0
  rw [hzt] at hshadow
  exact ⟨ht, ρ, hρ, hh.trans hdeep.le, hshadow⟩

/-- **Lossless at almost every height down to the critical scale.** For every `ε > 0` there is
`κ > 0` such that, for all large `V`, the heights in `[20, V]` carrying a non-real zero of
`cos(hD)Ξ` for some depth `h ≥ κ/log V` have measure at most `εV`. -/
theorem exists_criticalScale_cosineShift_lossless_ae {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, κ / Real.log V ≤ h ∧
        ∃ z : ℂ, z.re = t ∧ z.im ≠ 0 ∧ (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0}
        ≤ ENNReal.ofReal (ε * V) := by
  have hπ := Real.pi_pos
  have hsmall : ∀ᶠ R in atTop, selbergTailRate R < ε * Real.pi / 4 :=
    tendsto_selbergTailRate.eventually (gt_mem_nhds (by positivity))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hsmall
  set κ : ℝ := 2 * max R₀ 1 with hκdef
  have hκ : 0 < κ := by positivity
  have hg : selbergTailRate (κ / 2) < ε * Real.pi / 4 := by
    apply hR₀; rw [hκdef]; simp
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [eventually_volume_cosineShift_nonrealHeight_le_criticalScale hκ
    (by positivity : (0 : ℝ) < ε * Real.pi / 4), eventually_ge_atTop (1 : ℝ)] with V hV hV1
  refine hV.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ hπ]
  have h1 : selbergTailRate (κ / 2) + ε * Real.pi / 4 ≤ ε * Real.pi / 2 := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ V + 1)
  have h3 : ε * Real.pi / 2 * (V + 1) ≤ ε * V * Real.pi := by
    have hk := mul_le_mul_of_nonneg_left (show (V + 1) / 2 ≤ V by linarith)
      (le_of_lt (mul_pos hε hπ))
    calc ε * Real.pi / 2 * (V + 1) = ε * Real.pi * ((V + 1) / 2) := by ring
      _ ≤ ε * Real.pi * V := hk
      _ = ε * V * Real.pi := by ring
  linarith

end

end RHTower
