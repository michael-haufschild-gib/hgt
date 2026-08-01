import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import GaloisForLFunctions.RHTower.SoninCosineRiemannLebesgue

/-!
# Lévy--Khintchine law for the Julia compression profile

This module proves the hyperbolic integral identity for the Julia compression square from the
unconditional `log cosh` Lévy--Khintchine formula.  No probabilistic representation is assumed.
-/

open MeasureTheory

namespace HTGeometry

noncomputable section

theorem neg_log_juliaCompressionSquareProfile (y : ℝ) :
    -Real.log (juliaCompressionSquareProfile y) =
      (1 / 2 : ℝ) * Real.log (Real.cosh (2 * y)) -
        2 * Real.log (Real.cosh (y / 2)) := by
  rw [juliaCompressionSquareProfile_eq_cosh_ratio]
  have hhalf : Real.cosh (y / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have htwo : Real.sqrt (Real.cosh (2 * y)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.cosh_pos _)).ne'
  rw [Real.log_div (pow_ne_zero 2 hhalf) htwo, Real.log_pow,
    Real.log_sqrt (Real.cosh_pos _).le]
  ring

/-- **Exact Julia Lévy--Khintchine identity (JSE2).** -/
theorem neg_log_juliaCompressionSquareProfile_eq_integral (y : ℝ) :
    -Real.log (juliaCompressionSquareProfile y) =
      ∫ t : ℝ in Set.Ioi 0,
        (1 - Real.cos (t * y)) * juliaCompressionLevyDensity t := by
  have h2 := log_cosh_eq_hyperbolicLevyIntegral
    (a := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2) y
  have hh := log_cosh_eq_hyperbolicLevyIntegral
    (a := (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) y
  have hi2 := integrableOn_hyperbolicLevyIntegrand
    (a := (2 : ℝ)) (y := y) (by norm_num : (0 : ℝ) < 2)
  have hih := integrableOn_hyperbolicLevyIntegrand
    (a := (1 / 2 : ℝ)) (y := y) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [neg_log_juliaCompressionSquareProfile, h2,
    show y / 2 = (1 / 2 : ℝ) * y by ring, hh,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub (hi2.const_mul (1 / 2)) (hih.const_mul 2)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hs4 : Real.sinh (Real.pi * t / 4) ≠ 0 :=
    (Real.sinh_pos_iff.mpr
      (div_pos (mul_pos Real.pi_pos ht) (by norm_num))).ne'
  have hs1 : Real.sinh (Real.pi * t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  unfold hyperbolicLevyIntegrand juliaCompressionLevyDensity
  field_simp [ht0, hs4, hs1]
  ring

/-- Algebraic factorization exposing positivity and endpoint behavior of the Julia Lévy density. -/
theorem juliaCompressionLevyDensity_eq_factor {t : ℝ} (ht : 0 < t) :
    juliaCompressionLevyDensity t =
      let v := Real.pi * t / 4
      (Real.cosh v * Real.cosh (2 * v) - 1) /
        (2 * t * Real.sinh v * Real.cosh v * Real.cosh (2 * v)) := by
  let v := Real.pi * t / 4
  have hv : 0 < v := by dsimp [v]; positivity
  have hsv : Real.sinh v ≠ 0 := (Real.sinh_pos_iff.mpr hv).ne'
  have hcv : Real.cosh v ≠ 0 := (Real.cosh_pos v).ne'
  have hc2v : Real.cosh (2 * v) ≠ 0 := (Real.cosh_pos (2 * v)).ne'
  have hpit : Real.pi * t = 4 * v := by dsimp [v]; ring
  have hs4 : Real.sinh (Real.pi * t) =
      4 * Real.sinh v * Real.cosh v * Real.cosh (2 * v) := by
    rw [hpit, show 4 * v = 2 * (2 * v) by ring, Real.sinh_two_mul,
      Real.sinh_two_mul]
    ring
  dsimp only
  rw [juliaCompressionLevyDensity,
    show Real.pi * t / 4 = v by rfl, hs4]
  field_simp [ht.ne', hsv, hcv, hc2v]
  ring

/-- Uniform bound for the removable singularity of the Julia Lévy density at zero. -/
theorem juliaCompressionLevyDensity_le_near_zero {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    juliaCompressionLevyDensity t ≤
      (5 * Real.pi / 16) * Real.cosh 2 ^ 2 := by
  let v := Real.pi * t / 4
  have hv : 0 < v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    nlinarith [Real.pi_lt_four, mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le]
  have h2v : 0 ≤ 2 * v := by positivity
  have h2v2 : 2 * v ≤ 2 := by linarith
  have hAv := HTGeometry.cosh_sub_one_le hv.le
  have hBv := HTGeometry.cosh_sub_one_le h2v
  have hAle : Real.cosh v ≤ Real.cosh 2 := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hv.le,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hBle : Real.cosh (2 * v) ≤ Real.cosh 2 := by
    rw [Real.cosh_le_cosh, abs_of_nonneg h2v,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact h2v2
  have hA0 : 0 ≤ Real.cosh v - 1 := sub_nonneg.mpr (Real.one_le_cosh v)
  have hB0 : 0 ≤ Real.cosh (2 * v) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh (2 * v))
  have hnum : Real.cosh v * Real.cosh (2 * v) - 1 ≤
      (5 / 2 : ℝ) * v ^ 2 * Real.cosh 2 ^ 2 := by
    calc
      Real.cosh v * Real.cosh (2 * v) - 1 =
          (Real.cosh v - 1) * Real.cosh (2 * v) +
            (Real.cosh (2 * v) - 1) := by ring
      _ ≤ (v ^ 2 / 2 * Real.cosh v) * Real.cosh (2 * v) +
            ((2 * v) ^ 2 / 2 * Real.cosh (2 * v)) := by gcongr
      _ ≤ (v ^ 2 / 2 * Real.cosh 2) * Real.cosh 2 +
            ((2 * v) ^ 2 / 2 * Real.cosh 2) := by gcongr
      _ ≤ (5 / 2 : ℝ) * v ^ 2 * Real.cosh 2 ^ 2 := by
        nlinarith [sq_nonneg v,
          mul_nonneg (sq_nonneg v) (Real.cosh_pos 2).le]
  have hnum0 : 0 ≤ Real.cosh v * Real.cosh (2 * v) - 1 := by
    nlinarith [Real.one_le_cosh v, Real.one_le_cosh (2 * v),
      mul_nonneg hA0 (Real.cosh_pos (2 * v)).le]
  have hsv : v ≤ Real.sinh v := Real.self_le_sinh_iff.mpr hv.le
  have hAB : 1 ≤ Real.cosh v * Real.cosh (2 * v) :=
    calc
      1 = 1 * 1 := by ring
      _ ≤ Real.cosh v * Real.cosh (2 * v) :=
        mul_le_mul (Real.one_le_cosh v) (Real.one_le_cosh (2 * v))
          (by norm_num) (Real.cosh_pos v).le
  have hdenLower : 2 * t * v ≤
      2 * t * Real.sinh v * Real.cosh v * Real.cosh (2 * v) := by
    calc
      2 * t * v ≤ 2 * t * Real.sinh v := by gcongr
      _ ≤ 2 * t * Real.sinh v * (Real.cosh v * Real.cosh (2 * v)) := by
        nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * t)
          (Real.sinh_pos_iff.mpr hv).le) (sub_nonneg.mpr hAB)]
      _ = _ := by ring
  have hsimple : 0 < 2 * t * v := by positivity
  rw [juliaCompressionLevyDensity_eq_factor ht]
  dsimp only
  calc
    (Real.cosh v * Real.cosh (2 * v) - 1) /
        (2 * t * Real.sinh v * Real.cosh v * Real.cosh (2 * v)) ≤
      (Real.cosh v * Real.cosh (2 * v) - 1) / (2 * t * v) :=
        div_le_div_of_nonneg_left hnum0 hsimple hdenLower
    _ ≤ ((5 / 2 : ℝ) * v ^ 2 * Real.cosh 2 ^ 2) / (2 * t * v) :=
      div_le_div_of_nonneg_right hnum hsimple.le
    _ = (5 * Real.pi / 16) * Real.cosh 2 ^ 2 := by
      dsimp [v]
      field_simp [ht.ne', Real.pi_ne_zero]
      ring

/-- Inverse-square tail bound for the Julia Lévy density. -/
theorem juliaCompressionLevyDensity_le_tail {t : ℝ} (ht : 0 < t) :
    juliaCompressionLevyDensity t ≤ 2 / (Real.pi * t ^ 2) := by
  have hv : 0 < Real.pi * t / 4 := by positivity
  have hsV : 0 < Real.sinh (Real.pi * t / 4) := Real.sinh_pos_iff.mpr hv
  have hsPi : 0 < Real.sinh (Real.pi * t) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have hfirst : juliaCompressionLevyDensity t ≤
      1 / (2 * t * Real.sinh (Real.pi * t / 4)) := by
    rw [juliaCompressionLevyDensity]
    have : 0 ≤ 2 / (t * Real.sinh (Real.pi * t)) := by positivity
    linarith
  have hself : Real.pi * t / 4 ≤ Real.sinh (Real.pi * t / 4) :=
    Real.self_le_sinh_iff.mpr hv.le
  calc
    juliaCompressionLevyDensity t ≤
        1 / (2 * t * Real.sinh (Real.pi * t / 4)) := hfirst
    _ ≤ 2 / (Real.pi * t ^ 2) := by
      rw [div_le_div_iff₀
        (by positivity : 0 < 2 * t * Real.sinh (Real.pi * t / 4))
        (by positivity : 0 < Real.pi * t ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left hself (by positivity : 0 ≤ 4 * t)]

/-- The Julia Lévy density has finite total mass on the positive half-line. -/
theorem integrableOn_juliaCompressionLevyDensity :
    IntegrableOn juliaCompressionLevyDensity (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable juliaCompressionLevyDensity := by
    unfold juliaCompressionLevyDensity
    measurability
  have hnear : IntegrableOn juliaCompressionLevyDensity (Set.Ioc 0 1) := by
    have hc : IntegrableOn
        (fun _ : ℝ => (5 * Real.pi / 16) * Real.cosh 2 ^ 2) (Set.Ioc 0 1) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine hc.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (juliaCompressionLevyDensity_pos ht.1)]
    exact juliaCompressionLevyDensity_le_near_zero ht.1 ht.2
  have hinv : IntegrableOn (fun t : ℝ => 2 / (Real.pi * t ^ 2)) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := (1 : ℝ))
      (by norm_num) (by norm_num)
    have hr' : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi 1) := hr
    have hpow : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Set.Ioi 1) := by
      refine hr'.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      change t ^ (-2 : ℝ) = 1 / t ^ 2
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simp only [one_div]
    have hconst : IntegrableOn
        (fun t : ℝ => (2 / Real.pi) * (1 / t ^ 2)) (Set.Ioi 1) :=
      hpow.const_mul (2 / Real.pi)
    exact hconst.congr_fun (fun t _ => by ring) measurableSet_Ioi
  have htail : IntegrableOn juliaCompressionLevyDensity (Set.Ioi 1) := by
    refine hinv.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,
      abs_of_pos (juliaCompressionLevyDensity_pos (lt_trans zero_lt_one ht))]
    exact juliaCompressionLevyDensity_le_tail (lt_trans zero_lt_one ht)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hnear.union htail

/-- The Julia compression exponent approaches the exact finite Lévy mass. -/
theorem neg_log_juliaCompressionSquareProfile_tendsto :
    Filter.Tendsto (fun y : ℝ => -Real.log (juliaCompressionSquareProfile y))
      Filter.atTop (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
  have h2 := log_cosh_remainder_tendsto (2 : ℝ) (by norm_num)
  have hh := log_cosh_remainder_tendsto (1 / 2 : ℝ) (by norm_num)
  have hlim := (h2.const_mul (1 / 2 : ℝ)).sub (hh.const_mul 2)
  have hc : Filter.Tendsto (fun _ : ℝ => (3 / 2 : ℝ) * Real.log 2) Filter.atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := tendsto_const_nhds
  have hcombo : Filter.Tendsto (fun y : ℝ =>
      (1 / 2 : ℝ) * Real.log (Real.cosh (2 * y)) -
        2 * Real.log (Real.cosh (y / 2))) Filter.atTop
      (nhds ((3 / 2 : ℝ) * Real.log 2)) := by
    convert hlim.add hc using 1 <;> ring
  refine hcombo.congr' ?_
  filter_upwards with y
  rw [neg_log_juliaCompressionSquareProfile]

/-- Half-line cosine form of Riemann--Lebesgue, reduced to project Fourier infrastructure. -/
theorem tendsto_setIntegral_mul_cos_atTop {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi 0)) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ in Set.Ioi 0, Real.cos (t * y) * g t)
      Filter.atTop (nhds 0) := by
  let G : ℝ → ℝ := Set.indicator (Set.Ioi 0) g
  have hG : Integrable G := hg.integrable_indicator measurableSet_Ioi
  have hRL := RHTower.tendsto_integral_mul_cos_atTop hG
  have hscale : Filter.Tendsto (fun y : ℝ => y / (2 * Real.pi)) Filter.atTop
      Filter.atTop := by
    rw [show (fun y : ℝ => y / (2 * Real.pi)) =
      fun y => (1 / (2 * Real.pi)) * y by funext y; ring]
    exact (Filter.tendsto_const_mul_atTop_of_pos
      (by positivity : 0 < 1 / (2 * Real.pi))).mpr Filter.tendsto_id
  have hcomp := hRL.comp hscale
  refine hcomp.congr' ?_
  filter_upwards with y
  simp only [Function.comp_apply]
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Set.Ioi 0
  · simp only [G, Set.indicator_of_mem ht]
    rw [show 2 * Real.pi * t * (y / (2 * Real.pi)) = t * y by
      field_simp [Real.pi_ne_zero]]
    ring
  · simp [G, ht]

/-- **Exact Julia jump intensity.**  The positive-half-line Lévy density has mass
`(3/2) log 2`, hence the associated compound-Poisson rate is finite and explicit. -/
theorem juliaCompressionLevyDensity_mass :
    ∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t =
      (3 / 2 : ℝ) * Real.log 2 := by
  have hcosInt (y : ℝ) :
      IntegrableOn (fun t : ℝ => Real.cos (t * y) * juliaCompressionLevyDensity t)
        (Set.Ioi 0) := by
    exact integrableOn_juliaCompressionLevyDensity.bdd_mul
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  have hsplit (y : ℝ) :
      (∫ t : ℝ in Set.Ioi 0,
        (1 - Real.cos (t * y)) * juliaCompressionLevyDensity t) =
        (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t) -
          ∫ t : ℝ in Set.Ioi 0,
            Real.cos (t * y) * juliaCompressionLevyDensity t := by
    rw [← MeasureTheory.integral_sub integrableOn_juliaCompressionLevyDensity (hcosInt y)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    ring
  have hcos := tendsto_setIntegral_mul_cos_atTop integrableOn_juliaCompressionLevyDensity
  have hmassLimit : Filter.Tendsto
      (fun y : ℝ => -Real.log (juliaCompressionSquareProfile y)) Filter.atTop
      (nhds (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t)) := by
    have hconst : Filter.Tendsto
        (fun _ : ℝ => ∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t) Filter.atTop
        (nhds (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t)) :=
      tendsto_const_nhds
    have hright := hconst.sub hcos
    have hright' : Filter.Tendsto
        (fun y : ℝ => (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t) -
          ∫ t : ℝ in Set.Ioi 0,
            Real.cos (t * y) * juliaCompressionLevyDensity t) Filter.atTop
        (nhds (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t)) := by
      simpa using hright
    refine hright'.congr' ?_
    filter_upwards with y
    rw [neg_log_juliaCompressionSquareProfile_eq_integral, hsplit]
  exact tendsto_nhds_unique hmassLimit neg_log_juliaCompressionSquareProfile_tendsto

end

end HTGeometry
