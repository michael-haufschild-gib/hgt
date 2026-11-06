import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheCentralInequalityOnAlmostAllHeights
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheSlopeOfXiIsAPoissonSum

/-!
# The half-Gauss transform at the critical scale

Let `Q(v) = ∫_{w>0} G_τ(w − v) ξ(½ + w + iY) dw` and `u = v + 2τβ`, `β = Re a(Y)`. Below the saddle, size bounds for `ζ` lose a power of `log T` in the lower strip and accumulate the slope error on long intervals. Neither is needed if

* the slope error of `ξ` is at most `B` on the window `[u/3, 5u/4]`,
* `|ξ(w)| ≤ |ξ(u/3)|` on the lower strip `[0, u/3]`,
* `|ξ(w)|` grows at most like `exp((β + B)(w² − b²)/2b)` above `b = 5u/4`.

These are exactly what the Poisson sum gives. Then, with `P = |ξ(u)| e^{−τβ²}` and `δ = e^{−uβ/40}`,

`‖Q(v) − Main‖ ≤ P (E(B, τ) + 8δ)`,   `‖Q′(v) − a Q(v)‖ ≤ P (B(1 + E(B, τ)) + 60βδ)`    (`halfGauss_estimates_of_source`),

where `E(B, τ) ≍ B√τ` is the Gaussian model error. So the only conditions are `uβ ≫ 1`, `B√τ ≪ 1` and `B ≪ β`. Since `uβ ≍ τβ²`, the first one is `t log²X ≫ 1`: the critical scale of the zeros.

The exponent is exact on the top: at `w = b + z`, the source and the Gaussian combine to `−τβ² + uB/4 − u²/(64τ) + z(B − u/(8τ)) + z²((β + B)/(2b) − 1/(4τ))`, each bracket negative (`top_exponent_le`).
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The exponents -/

/-- The reciprocal of the time against the slope and the saddle. -/
theorem inv_time_ge {β u v τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hu : 0 < u) (hrel : v + 2 * τ * β = u)
    (hv : 100 * |v| ≤ u) : 200 * β / (101 * u) ≤ 1 / τ := by
  have h1 : -|v| ≤ v := neg_abs_le v
  rw [div_le_div_iff₀ (by positivity) hτ]
  nlinarith only [hrel, hv, h1]

theorem inv_time_le {β u v τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hu : 0 < u) (hrel : v + 2 * τ * β = u)
    (hv : 100 * |v| ≤ u) : 1 / τ ≤ 200 * β / (99 * u) := by
  have h1 : v ≤ |v| := le_abs_self v
  rw [div_le_div_iff₀ hτ (by positivity)]
  nlinarith only [hrel, hv, h1]

/-- **The exponent on the top.** -/
theorem top_exponent_le {β B u v τ w : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hu : 0 < u) (hrel : v + 2 * τ * β = u)
    (hv : 100 * |v| ≤ u) (hB0 : 0 ≤ B) (hB : 100 * B ≤ β) (hw : 5 * u / 4 ≤ w) :
    u / 4 * (β + B) + (β + B) * (w ^ 2 - (5 * u / 4) ^ 2) / (2 * (5 * u / 4)) - (w - v) ^ 2 / (4 * τ) ≤
      -(τ * β ^ 2) - u * β / 40 - β / 5 * (w - 5 * u / 4) := by
  have hinv := inv_time_ge hβ hτ hu hrel hv
  set z := w - 5 * u / 4 with hz
  have hz0 : 0 ≤ z := sub_nonneg.mpr hw
  have hb1 : u * B / 4 - u ^ 2 / (64 * τ) + u * β / 40 ≤ 0 := by
    have h1 : u ^ 2 / (64 * τ) = u ^ 2 / 64 * (1 / τ) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ u ^ 2 / 64)
    have h3 : u ^ 2 / 64 * (200 * β / (101 * u)) = 200 / (64 * 101) * (u * β) := by
      field_simp
    have h4 : u * B ≤ u * (β / 100) := mul_le_mul_of_nonneg_left (by linarith only [hB]) hu.le
    have h5 : 0 < u * β := by positivity
    nlinarith only [h1, h2, h3, h4, h5]
  have hb2 : B - u / (8 * τ) + β / 5 ≤ 0 := by
    have h1 : u / (8 * τ) = u / 8 * (1 / τ) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ u / 8)
    have h3 : u / 8 * (200 * β / (101 * u)) = 200 / (8 * 101) * β := by
      field_simp
    nlinarith only [h1, h2, h3, hB, hβ]
  have hb3 : (β + B) / (2 * (5 * u / 4)) - 1 / (4 * τ) ≤ 0 := by
    have h1 : 1 / (4 * τ) = 1 / 4 * (1 / τ) := by
      field_simp
    have h3 : (β + B) / (2 * (5 * u / 4)) ≤ 101 / 100 * β / (5 / 2 * u) := by
      rw [show 2 * (5 * u / 4) = 5 / 2 * u by ring]
      exact div_le_div_of_nonneg_right (by linarith only [hB]) (by positivity)
    have h4 : 1 / 4 * (200 * β / (101 * u)) - 101 / 100 * β / (5 / 2 * u) = (50 / 101 - 101 / 250) * (β / u) := by
      field_simp
      ring
    have h5 : 0 < β / u := by positivity
    have h2 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h1, h2, h3, h4, h5]
  have hv' : v = u - 2 * τ * β := by linarith only [hrel]
  have hw' : w = z + 5 * u / 4 := by rw [hz]; ring
  have hid : u / 4 * (β + B) + (β + B) * (w ^ 2 - (5 * u / 4) ^ 2) / (2 * (5 * u / 4)) - (w - v) ^ 2 / (4 * τ) -
      (-(τ * β ^ 2) - u * β / 40 - β / 5 * z) =
      (u * B / 4 - u ^ 2 / (64 * τ) + u * β / 40) + z * (B - u / (8 * τ) + β / 5) +
        z ^ 2 * ((β + B) / (2 * (5 * u / 4)) - 1 / (4 * τ)) := by
    rw [hw', hv']
    field_simp
    ring
  have h1 := mul_nonpos_of_nonneg_of_nonpos hz0 hb2
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) hb3
  linarith only [hid, hb1, h1, h2]

/-- The upper Gaussian tail with the exact squared-distance exponent. -/
theorem gaussian_saddle_upper_tail_le {t α y N b : ℝ} (ht : 0 < t) (hN : 0 ≤ N) (hb : y + 2 * t * α ≤ b) :
    N * Real.exp (-((y + 2 * t * α) * α)) * (∫ w in Ioi b, gaussDensity t (w - y) * Real.exp (w * α)) ≤
      N * Real.exp (-(t * α ^ 2)) * Real.exp (-((b - (y + 2 * t * α)) ^ 2 / (4 * t))) := by
  rw [← integral_Ici_eq_integral_Ioi]
  set lam := (b - (y + 2 * t * α)) / (2 * t) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hb) (by positivity)
  have hh := setIntegral_Ici_gaussDensity_sub_mul_rexp_le ht y α b lam hlam0
  calc
    _ ≤ N * Real.exp (-((y + 2 * t * α) * α)) * Real.exp (-(lam * b) + y * (α + lam) + t * (α + lam) ^ 2) := by
      gcongr
    _ = _ := by
      rw [mul_assoc N, ← Real.exp_add, mul_assoc N, ← Real.exp_add]
      congr 2
      rw [hlam]
      field_simp
      ring

theorem exp_add_sub (a b c : ℝ) : Real.exp (a + b - c) = Real.exp a * Real.exp b * Real.exp (-c) := by
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]

theorem exp_neg_sub_sub (a b c : ℝ) : Real.exp (-a - b - c) = Real.exp (-a) * Real.exp (-b) * Real.exp (-c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add]

/-- The exponential on a half-line. -/
theorem integral_exp_decay {c : ℝ} (hc : 0 < c) (b : ℝ) :
    IntegrableOn (fun w => Real.exp (-(c * (w - b)))) (Ioi b) ∧
      ∫ w in Ioi b, Real.exp (-(c * (w - b))) = 1 / c := by
  have h1 : (fun w => Real.exp (-(c * (w - b)))) = fun w => Real.exp (c * b) * Real.exp (-c * w) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1]
  refine ⟨(integrableOn_exp_mul_Ioi (by linarith only [hc]) b).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith only [hc]) b, neg_div_neg_eq]
  have h2 : Real.exp (c * b) * Real.exp (-c * b) = 1 := by
    rw [← Real.exp_add, show c * b + -c * b = 0 by ring, Real.exp_zero]
  rw [← mul_div_assoc, h2]

private theorem integrable_gaussDensity_norm_xiLine' {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) :
    Integrable (fun w => gaussDensity τ (w - y) * ‖xiLine X w‖) := by
  refine (integrable_gaussDensity_sub_mul hτ (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine hτ X) y).norm.congr (Eventually.of_forall fun w => ?_)
  exact norm_gauss_mul τ y w hτ _

/-! ## The estimates -/

/-- **The half-Gauss transform from its source.** -/
theorem halfGauss_estimates_of_source {τ Y v u B : ℝ} (hτ : 0 < τ) (hβ1 : 1 ≤ (horizontalSlope Y).re)
    (hu : 0 < u) (hrel : v + 2 * τ * (horizontalSlope Y).re = u) (hv : 100 * |v| ≤ u) (hB0 : 0 < B)
    (hB : 100 * B ≤ (horizontalSlope Y).re) (hΛ : 400 ≤ u * (horizontalSlope Y).re)
    (hslope : ∀ w ∈ Icc (u / 3) (5 * u / 4),
      ‖xiLineDeriv Y w - horizontalSlope Y * xiLine Y w‖ ≤ B * ‖xiLine Y w‖)
    (hlow : ∀ w ∈ Icc (0 : ℝ) (u / 3), ‖xiLine Y w‖ ≤ ‖xiLine Y (u / 3)‖)
    (htop : ∀ w, 5 * u / 4 ≤ w → ‖xiLine Y w‖ ≤ ‖xiLine Y (5 * u / 4)‖ *
      Real.exp (((horizontalSlope Y).re + B) * (w ^ 2 - (5 * u / 4) ^ 2) / (2 * (5 * u / 4)))) :
    ‖halfGaussTransform τ (xiLine Y) v -
        xiLine Y u * Complex.exp (-(u * horizontalSlope Y)) *
          Complex.exp (v * horizontalSlope Y + τ * horizontalSlope Y ^ 2)‖ ≤
      (‖xiLine Y u‖ * Real.exp (-(τ * (horizontalSlope Y).re ^ 2))) *
        (gaussianSaddleModelError B τ + 8 * Real.exp (-(u * (horizontalSlope Y).re / 40))) ∧
    ‖(∫ w in Ioi (0 : ℝ), (((w - v) / (2 * τ) * gaussDensity τ (w - v) : ℝ) : ℂ) * xiLine Y w) -
        horizontalSlope Y * halfGaussTransform τ (xiLine Y) v‖ ≤
      (‖xiLine Y u‖ * Real.exp (-(τ * (horizontalSlope Y).re ^ 2))) *
        (B * (1 + gaussianSaddleModelError B τ) +
          60 * (horizontalSlope Y).re * Real.exp (-(u * (horizontalSlope Y).re / 40))) := by
  set a := horizontalSlope Y with ha
  set β := a.re with hβdef
  have hβ : 0 < β := by linarith only [hβ1]
  set N := ‖xiLine Y u‖ with hNdef
  have hN : 0 ≤ N := norm_nonneg _
  set P := N * Real.exp (-(τ * β ^ 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  set δ := Real.exp (-(u * β / 40)) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  set c₀ := (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hE0 : 0 ≤ gaussianSaddleModelError B τ := gaussianSaddleModelError_nonneg hB0.le
  set b := 5 * u / 4 with hb
  set a₁ := u / 3 with ha₁
  have hb0 : 0 < b := by positivity
  have ha₁0 : 0 < a₁ := by positivity
  have ha₁b : a₁ ≤ b := by rw [ha₁, hb]; linarith only [hu]
  have hub : u ≤ b := by rw [hb]; linarith only [hu]
  have ha₁u : a₁ ≤ u := by rw [ha₁]; linarith only [hu]
  have hinv := inv_time_ge hβ hτ hu hrel hv
  have hinv2 := inv_time_le hβ hτ hu hrel hv
  have hv1 : -|v| ≤ v := neg_abs_le v
  have hv2 : v ≤ |v| := le_abs_self v
  have hτβ : τ * β = (u - v) / 2 := by linarith only [hrel]
  have huβ : 0 < u * β := by positivity
  -- the squared distances
  have hq : 50 / 101 * (u * β) ≤ u ^ 2 / (4 * τ) := by
    have h1 : u ^ 2 / (4 * τ) = u ^ 2 / 4 * (1 / τ) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ u ^ 2 / 4)
    have h3 : u ^ 2 / 4 * (200 * β / (101 * u)) = 50 / 101 * (u * β) := by
      field_simp
      ring
    linarith only [h1, h2, h3]
  have hc₀β : c₀ ≤ β := by
    rw [hc₀, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by positivity)) hβ]
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : 4 * Real.pi * τ * β ^ 2 = 2 * Real.pi * (u - v) * β := by
      rw [show u - v = 2 * (τ * β) by linarith only [hτβ]]
      ring
    have h2 : 1 ≤ 4 * Real.pi * τ * β ^ 2 := by
      rw [h1]
      have h3 : u - v ≥ u / 2 := by linarith only [hv, hv2, abs_nonneg v]
      have h4 : (u / 2) * β ≤ (u - v) * β := mul_le_mul_of_nonneg_right h3 hβ.le
      have hpi := Real.pi_gt_three
      nlinarith only [h4, hΛ, hpi, mul_nonneg (by positivity : (0 : ℝ) ≤ Real.pi - 3) (by positivity : 0 ≤ (u / 2) * β),
        mul_pos Real.pi_pos huβ]
    have hβ2 : 0 < β ^ 2 := by positivity
    rw [inv_pow, inv_eq_one_div, div_le_iff₀ hβ2]
    exact h2
  -- the source on the window
  have huI : u ∈ Icc a₁ b := ⟨ha₁u, hub⟩
  have hwin (w : ℝ) (hw : w ∈ Icc a₁ b) :
      ‖xiLine Y w‖ ≤ N * Real.exp ((w - u) * β) * Real.exp (B * |w - u|) :=
    norm_xiLine_le_model_of_slope hB0 hslope huI hw
  have hmodel : ∀ w ∈ Icc a₁ b, ‖xiLine Y w - xiLine Y u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
      ‖xiLine Y u‖ * Real.exp ((w - u) * a.re) * (Real.exp (B * |w - u|) - 1) := by
    intro w hw
    have hsub : uIcc u w ⊆ Icc a₁ b := uIcc_subset_Icc huI hw
    exact GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le hB0 (fun s _ => hasDerivAt_xiLine Y s)
      (fun s hs => hslope s (hsub hs))
  -- the value at the lower endpoint
  have hSa : ‖xiLine Y a₁‖ ≤ P * δ := by
    have h1 := hwin a₁ ⟨le_rfl, ha₁b⟩
    rw [abs_of_nonpos (show a₁ - u ≤ 0 by linarith only [ha₁u])] at h1
    rw [hP, hδ, mul_assoc N, ← Real.exp_add]
    refine h1.trans ?_
    rw [mul_assoc N, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN
    have hτ2 : τ * β ^ 2 = (u - v) * β / 2 := by
      rw [show τ * β ^ 2 = τ * β * β by ring, hτβ]
      ring
    rw [hτ2, ha₁]
    have h4 : u * B ≤ u * (β / 100) := mul_le_mul_of_nonneg_left (by linarith only [hB]) hu.le
    have h5 : -v * β ≤ u / 100 * β := mul_le_mul_of_nonneg_right (by linarith only [hv, hv1, abs_nonneg v]) hβ.le
    nlinarith only [h4, h5, huβ]
  -- the mass of the strip
  have hgmass : ∫ w in Ioc 0 a₁, gaussDensity τ (w - v) ≤ 1 := by
    have hint := integrable_gaussDensity_sub_mul_rexp hτ v 0
    have hm := integral_gaussDensity_sub_mul_rexp hτ v 0
    simp only [mul_zero, Real.exp_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at hm hint
    calc ∫ w in Ioc 0 a₁, gaussDensity τ (w - v)
        ≤ ∫ w, gaussDensity τ (w - v) :=
          setIntegral_le_integral hint (Eventually.of_forall fun w => (gaussDensity_pos hτ _).le)
      _ = 1 := hm
  have hstrip : (∫ w in Ioc 0 a₁, gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤ P * δ := by
    have hc : Continuous fun w => gaussDensity τ (w - v) := (continuous_gaussDensity τ).comp (by fun_prop)
    have h1 : (∫ w in Ioc 0 a₁, gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
        ∫ w in Ioc 0 a₁, gaussDensity τ (w - v) * ‖xiLine Y a₁‖ := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun w hw => ?_
      · exact (hc.mul (continuous_xiLine Y).norm).integrableOn_Ioc
      · exact (hc.mul continuous_const).integrableOn_Ioc
      · exact mul_le_mul_of_nonneg_left (hlow w ⟨hw.1.le, hw.2⟩) (gaussDensity_pos hτ _).le
    rw [integral_mul_const] at h1
    refine h1.trans ?_
    calc _ ≤ 1 * ‖xiLine Y a₁‖ := mul_le_mul_of_nonneg_right hgmass (norm_nonneg _)
      _ ≤ P * δ := by rw [one_mul]; exact hSa
  -- the top
  have hbval : ‖xiLine Y b‖ ≤ N * Real.exp (u / 4 * (β + B)) := by
    have h1 := hwin b ⟨ha₁b, le_rfl⟩
    rw [abs_of_nonneg (by linarith only [hub]), mul_assoc N, ← Real.exp_add] at h1
    refine h1.trans (le_of_eq ?_)
    congr 2
    rw [hb]
    ring
  have hgtop (w : ℝ) (hw : b ≤ w) :
      gaussDensity τ (w - v) * ‖xiLine Y w‖ ≤ c₀ * (P * δ) * Real.exp (-(β / 5 * (w - b))) := by
    have h1 := htop w hw
    have h2 := top_exponent_le hβ hτ hu hrel hv hB0.le hB hw
    unfold gaussDensity
    rw [← hc₀]
    calc c₀ * Real.exp (-((w - v) ^ 2 / (4 * τ))) * ‖xiLine Y w‖
        ≤ c₀ * Real.exp (-((w - v) ^ 2 / (4 * τ))) *
            ((N * Real.exp (u / 4 * (β + B))) * Real.exp ((β + B) * (w ^ 2 - b ^ 2) / (2 * b))) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right hbval (Real.exp_pos _).le
      _ = c₀ * N * Real.exp (u / 4 * (β + B) + (β + B) * (w ^ 2 - b ^ 2) / (2 * b) - (w - v) ^ 2 / (4 * τ)) := by
          rw [exp_add_sub]
          ring
      _ ≤ c₀ * N * Real.exp (-(τ * β ^ 2) - u * β / 40 - β / 5 * (w - b)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) (by positivity)
      _ = _ := by
          rw [hP, hδ, exp_neg_sub_sub]
          ring
  have hIg := integrable_gaussDensity_norm_xiLine' hτ Y v
  have hdec1 := integral_exp_decay (show 0 < β / 5 by positivity) b
  have htopmass : (∫ w in Ioi b, gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤ 5 * (P * δ) := by
    have h1 : (∫ w in Ioi b, gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
        ∫ w in Ioi b, c₀ * (P * δ) * Real.exp (-(β / 5 * (w - b))) :=
      setIntegral_mono_on hIg.integrableOn (hdec1.1.const_mul _) measurableSet_Ioi
        fun w hw => hgtop w (le_of_lt hw)
    rw [integral_const_mul, hdec1.2] at h1
    refine h1.trans ?_
    have h2 : 1 / (β / 5) = 5 / β := by
      field_simp
    rw [h2]
    have h3 : c₀ / β ≤ 1 := (div_le_one hβ).mpr hc₀β
    have h4 : 0 ≤ P * δ := by positivity
    calc c₀ * (P * δ) * (5 / β) = (c₀ / β) * (5 * (P * δ)) := by ring
      _ ≤ 1 * (5 * (P * δ)) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := one_mul _
  -- the exponents of the Gaussian tails
  have hδ1 : Real.exp (-((u - a₁) ^ 2 / (4 * τ))) ≤ δ := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : (u - a₁) ^ 2 / (4 * τ) = 4 / 9 * (u ^ 2 / (4 * τ)) := by
      rw [ha₁]
      ring
    rw [h1]
    nlinarith only [hq, huβ]
  have hδ2 : Real.exp (-((b - u) ^ 2 / (4 * τ))) ≤ δ := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : (b - u) ^ 2 / (4 * τ) = 1 / 16 * (u ^ 2 / (4 * τ)) := by
      rw [hb]
      ring
    rw [h1]
    nlinarith only [hq, huβ]
  have hT1 : N * Real.exp (-(u * β)) * (∫ w in Iic a₁, gaussDensity τ (w - v) * Real.exp (w * β)) ≤ P * δ := by
    have h := gaussian_saddle_lower_tail_le (α := β) (y := v) (N := N) (b := a₁) hτ hN (by rw [hrel]; exact ha₁u)
    rw [hrel] at h
    exact h.trans (mul_le_mul_of_nonneg_left hδ1 hP0)
  have hT2 : N * Real.exp (-(u * β)) * (∫ w in Ioi b, gaussDensity τ (w - v) * Real.exp (w * β)) ≤ P * δ := by
    have h := gaussian_saddle_upper_tail_le (α := β) (y := v) (N := N) (b := b) hτ hN (by rw [hrel]; exact hub)
    rw [hrel] at h
    exact h.trans (mul_le_mul_of_nonneg_left hδ2 hP0)
  have hT3 : N * Real.exp (-(u * β)) *
      (∫ w, gaussDensity τ (w - v) * Real.exp (w * β) * (Real.exp (B * |w - u|) - 1)) ≤
      P * gaussianSaddleModelError B τ := by
    have h := gaussian_saddle_model_error_le (α := β) (y := v) hτ hB0.le hN
    rw [hrel] at h
    exact h
  constructor
  · have hQ := norm_halfGaussTransform_sub_main_le hτ (continuous_xiLine Y) (integrable_exp_mul_norm_xiLine hτ Y)
      (y := v) hB0.le ha₁0.le ha₁b hmodel
    refine hQ.trans ?_
    rw [← hNdef, ← hβdef]
    have hexpand : N * Real.exp (-(u * β)) *
        ((∫ w in Iic a₁, gaussDensity τ (w - v) * Real.exp (w * β)) +
          (∫ w in Ioi b, gaussDensity τ (w - v) * Real.exp (w * β)) +
          ∫ w, gaussDensity τ (w - v) * Real.exp (w * β) * (Real.exp (B * |w - u|) - 1)) =
        N * Real.exp (-(u * β)) * (∫ w in Iic a₁, gaussDensity τ (w - v) * Real.exp (w * β)) +
        N * Real.exp (-(u * β)) * (∫ w in Ioi b, gaussDensity τ (w - v) * Real.exp (w * β)) +
        N * Real.exp (-(u * β)) *
          (∫ w, gaussDensity τ (w - v) * Real.exp (w * β) * (Real.exp (B * |w - u|) - 1)) := by ring
    rw [hexpand]
    linarith only [hT1, hT2, hT3, hstrip, htopmass]
  · have hD := norm_slope_sub_mul_le hτ (hasDerivAt_xiLine Y) (continuous_xiLineDeriv Y)
      (integrable_exp_mul_norm_xiLine hτ Y) (y := v) (a := a) ha₁0.le ha₁b hslope
    refine hD.trans ?_
    have hnorma : ‖a‖ ≤ 2 * β := by
      have h := _root_.RHTower.DeBruijn.norm_horizontalSlope_le (X := Y) (by rw [← ha, ← hβdef]; exact hβ.le)
      rw [← ha, ← hβdef] at h
      linarith only [h, hβ1]
    -- the weight on the strip
    have hS1 : (∫ w in Ioc 0 a₁, (|(w - v) / (2 * τ)| + ‖a‖) * gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
        3 * β * (P * δ) := by
      have h1 := gaussian_lower_interval_slope_mass_le (continuous_xiLine Y) (t := τ) (b := a₁) (y := v) hτ a
      refine h1.trans ?_
      have h2 : (a₁ + |v|) / (2 * τ) ≤ β := by
        have h3 : (a₁ + |v|) / (2 * τ) = (a₁ + |v|) / 2 * (1 / τ) := by
          field_simp
        rw [h3]
        have h4 := mul_le_mul_of_nonneg_left hinv2 (by positivity : 0 ≤ (a₁ + |v|) / 2)
        refine h4.trans ?_
        have h5 : (a₁ + |v|) / 2 ≤ u / 4 := by
          rw [ha₁]
          linarith only [hv, hu]
        have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : 0 ≤ 200 * β / (99 * u))
        refine h6.trans ?_
        have h7 : u / 4 * (200 * β / (99 * u)) = 50 / 99 * β := by
          field_simp
          ring
        rw [h7]
        linarith only [hβ]
      have hmass0 : 0 ≤ ∫ w in Ioc 0 a₁, gaussDensity τ (w - v) * ‖xiLine Y w‖ :=
        setIntegral_nonneg measurableSet_Ioc fun w _ => mul_nonneg (gaussDensity_pos hτ _).le (norm_nonneg _)
      exact mul_le_mul (by linarith only [h2, hnorma]) hstrip hmass0 (by positivity)
    -- the weight on the top
    have hdec2 := integral_exp_decay (show 0 < β / 10 by positivity) b
    have hweight (w : ℝ) (hw : b ≤ w) :
        (|(w - v) / (2 * τ)| + ‖a‖) * Real.exp (-(β / 5 * (w - b))) ≤ 5 * β * Real.exp (-(β / 10 * (w - b))) := by
      set z := w - b with hz
      have hz0 : 0 ≤ z := sub_nonneg.mpr hw
      have hwv : 0 ≤ w - v := by
        rw [hb] at hw
        linarith only [hw, hv, hv2, abs_nonneg v, hu]
      have h1 : |(w - v) / (2 * τ)| = (b - v) / (2 * τ) + z / (2 * τ) := by
        rw [abs_of_nonneg (by positivity)]
        rw [hz]
        ring
      have h2 : (b - v) / (2 * τ) ≤ 2 * β := by
        have h3 : (b - v) / (2 * τ) = (b - v) / 2 * (1 / τ) := by
          field_simp
        have hbv : 0 ≤ (b - v) / 2 := by
          rw [hb]
          linarith only [hv, hv2, abs_nonneg v, hu]
        rw [h3]
        have h4 := mul_le_mul_of_nonneg_left hinv2 hbv
        refine h4.trans ?_
        have h5 : (b - v) / 2 ≤ 7 * u / 10 := by
          rw [hb]
          linarith only [hv, hv1, abs_nonneg v, hu]
        have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : 0 ≤ 200 * β / (99 * u))
        refine h6.trans ?_
        have h7 : 7 * u / 10 * (200 * β / (99 * u)) = 140 / 99 * β := by
          field_simp
          ring
        rw [h7]
        linarith only [hβ]
      have hE (c : ℝ) : Real.exp (-(c * z)) = Real.exp (-(c / 2 * z)) * Real.exp (-(c / 2 * z)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hE5 : Real.exp (-(β / 5 * z)) = Real.exp (-(β / 10 * z)) * Real.exp (-(β / 10 * z)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hexp1 : Real.exp (-(β / 10 * z)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ β / 10 * z := by positivity
        linarith only [this])
      have hzdec : z / (2 * τ) * Real.exp (-(β / 10 * z)) ≤ β := by
        have h3 : β / 10 * z ≤ Real.exp (β / 10 * z) := by
          have := Real.add_one_le_exp (β / 10 * z)
          linarith only [this]
        have h4 : z * Real.exp (-(β / 10 * z)) ≤ 10 / β := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hβ]
          nlinarith only [h3]
        have h5 : 1 / (2 * τ) ≤ 100 * β / (99 * u) := by
          have h6 : 1 / (2 * τ) = 1 / 2 * (1 / τ) := by
            field_simp
          rw [h6]
          have h7 := mul_le_mul_of_nonneg_left hinv2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
          refine h7.trans (le_of_eq ?_)
          field_simp
          ring
        have h6 : z / (2 * τ) * Real.exp (-(β / 10 * z)) = (z * Real.exp (-(β / 10 * z))) * (1 / (2 * τ)) := by
          field_simp
        rw [h6]
        have h7 : 0 ≤ z * Real.exp (-(β / 10 * z)) := by positivity
        have h8 := mul_le_mul h4 h5 (by positivity) (by positivity)
        refine h8.trans ?_
        have h9 : 10 / β * (100 * β / (99 * u)) = 1000 / 99 * (1 / u) := by
          field_simp
          norm_num
        rw [h9]
        have h10 : 1 / u ≤ β / 400 := by
          rw [div_le_div_iff₀ hu (by norm_num)]
          linarith only [hΛ]
        linarith only [h10, hβ]
      rw [hE5, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [h1]
      have hexp0 := Real.exp_pos (-(β / 10 * z))
      have h3 : (b - v) / (2 * τ) * Real.exp (-(β / 10 * z)) ≤ 2 * β :=
        (mul_le_mul_of_nonneg_left hexp1 (by
          rw [hb]
          have : 0 ≤ 5 * u / 4 - v := by linarith only [hv, hv2, abs_nonneg v, hu]
          positivity)).trans (by linarith only [h2])
      have h4 : ‖a‖ * Real.exp (-(β / 10 * z)) ≤ 2 * β :=
        (mul_le_mul_of_nonneg_left hexp1 (norm_nonneg _)).trans (by linarith only [hnorma])
      nlinarith only [h3, h4, hzdec]
    have hS2 : (∫ w in Ioi b, (|(w - v) / (2 * τ)| + ‖a‖) * gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
        50 * β * (P * δ) := by
      have h1 : (∫ w in Ioi b, (|(w - v) / (2 * τ)| + ‖a‖) * gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
          ∫ w in Ioi b, c₀ * (P * δ) * (5 * β * Real.exp (-(β / 10 * (w - b)))) := by
        refine setIntegral_mono_on ?_ ((hdec2.1.const_mul _).const_mul _) measurableSet_Ioi fun w hw => ?_
        · have hslopeInt := integrable_slope_mul hτ (continuous_xiLine Y) (integrable_exp_mul_norm_xiLine hτ Y) v
          have hA := (hslopeInt.norm.add (hIg.const_mul ‖a‖)).integrableOn (s := Ioi b)
          refine hA.congr (Eventually.of_forall fun w => ?_)
          simp only [Pi.add_apply]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussDensity_pos hτ _)]
          ring
        · have hw' : b ≤ w := le_of_lt hw
          have h2 := hgtop w hw'
          have h3 := hweight w hw'
          have hweight0 : 0 ≤ |(w - v) / (2 * τ)| + ‖a‖ := by positivity
          calc (|(w - v) / (2 * τ)| + ‖a‖) * gaussDensity τ (w - v) * ‖xiLine Y w‖
              = (|(w - v) / (2 * τ)| + ‖a‖) * (gaussDensity τ (w - v) * ‖xiLine Y w‖) := by ring
            _ ≤ (|(w - v) / (2 * τ)| + ‖a‖) * (c₀ * (P * δ) * Real.exp (-(β / 5 * (w - b)))) :=
                mul_le_mul_of_nonneg_left h2 hweight0
            _ = c₀ * (P * δ) * ((|(w - v) / (2 * τ)| + ‖a‖) * Real.exp (-(β / 5 * (w - b)))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [integral_const_mul, integral_const_mul, hdec2.2] at h1
      refine h1.trans ?_
      have h2 : 5 * β * (1 / (β / 10)) = 50 := by
        field_simp
        norm_num
      rw [h2]
      have h4 : 0 ≤ P * δ := by positivity
      calc c₀ * (P * δ) * 50 ≤ β * (P * δ) * 50 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₀β h4) (by norm_num)
        _ = _ := by ring
    have hgauss_le (x : ℝ) : gaussDensity τ x ≤ c₀ := by
      unfold gaussDensity
      rw [← hc₀]
      have h1 : Real.exp (-(x ^ 2 / (4 * τ))) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ x ^ 2 / (4 * τ) := by positivity
        linarith only [this])
      calc c₀ * Real.exp (-(x ^ 2 / (4 * τ))) ≤ c₀ * 1 := mul_le_mul_of_nonneg_left h1 hc₀pos.le
        _ = c₀ := mul_one _
    have hS3 : gaussDensity τ (a₁ - v) * ‖xiLine Y a₁‖ ≤ β * (P * δ) :=
      mul_le_mul ((hgauss_le _).trans hc₀β) hSa (norm_nonneg _) hβ.le
    have hS4 : gaussDensity τ (b - v) * ‖xiLine Y b‖ ≤ β * (P * δ) := by
      have h1 := hgtop b le_rfl
      rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hc₀β (by positivity))
    have hS5 : (∫ w in Ioc a₁ b, gaussDensity τ (w - v) * ‖xiLine Y w‖) ≤
        P * (1 + gaussianSaddleModelError B τ) := by
      refine gaussian_saddle_window_mass_le (continuous_xiLine Y) (α := β) (y := v) (N := N) hτ hB0.le hN ?_
      rw [hrel]
      exact fun w hw => hwin w ⟨hw.1.le, hw.2⟩
    have hS5' := mul_le_mul_of_nonneg_left hS5 hB0.le
    have hP0δ : 0 ≤ β * (P * δ) := by positivity
    have hfinal : P * (B * (1 + gaussianSaddleModelError B τ) + 60 * β * δ) =
        B * (P * (1 + gaussianSaddleModelError B τ)) + 60 * (β * (P * δ)) := by ring
    rw [hfinal]
    linarith only [hS1, hS2, hS3, hS4, hS5', hP0δ]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
