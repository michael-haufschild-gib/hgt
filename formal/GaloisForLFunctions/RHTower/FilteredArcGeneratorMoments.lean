import GaloisForLFunctions.RHTower.FilteredArcGeneratorDecay

/-!
# Sine moments of the filtered arc generators

For `c > 0` and an arc point `u + iy`, the Basset integral gives the sine moment of `ψ_u'`:

`J_u(c) = ∫ ψ_u'(x) sin(cx) dx = −4c √y K₀(cy) cos(cu)`  (`integral_arcPairDeriv_mul_sin`).

At `c = 2π(n+1)` this is `−4c √y` times the arc Whittaker mode `K₀(cy) cos(cu)` of the
annihilation problem on the modular arc.

**Moments of the filtered generator** (`integral_filteredArcDeriv_mul_sin`). For `h = h_{K,u}`,

`∫ h'(x) sin(cx) dx = J_u(c) − ∫ ǧ_K(w) e^{−w/2} J_u(c e^w) dw`.

Proof: Fubini for the integrable kernel `ǧ_K(w) e^{−3w/2} ψ_u'(x e^{−w}) sin(cx)`, then the substitution
`x = e^w t` in the inner integral.

**Uniform error** (`abs_integral_filteredArcDeriv_mul_sin_sub_le`). `√r K₀(r) ≤ √(π/2)` for `r > 0`
(`sqrt_mul_kMoment_zero_le`, from `cosh t ≥ 1 + t²/2`), so `|e^{−w/2} J_u(c e^w)| ≤ 4√(π/2) √c`
for every `w` and every arc point. Hence

`|∫ h_{K,u}' sin(c·) − J_u(c)| ≤ 4√(π/2) √c (2e^{−K/4} + e^{−K/2})`,

uniformly in `u`, which tends to `0` as `K → ∞`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The sine moment `J_u(c) = −4c √y K₀(cy) cos(cu)` of `ψ_u'`. -/
def arcPairSineMoment (u : ArcParam) (c : ℝ) : ℝ :=
  -(4 * c * Real.sqrt (modularArcHeight u) * kMoment 0 (c * modularArcHeight u) *
    Real.cos (c * u))

theorem integrable_arcLineKernel_mul_sin (u : ArcParam) (c : ℝ) :
    Integrable fun x => arcLineKernel x u * Real.sin (c * x) := by
  refine (integrable_inv_one_add_sq.const_mul 32).mono'
    ((continuous_arcLineKernel.comp (continuous_id.prodMk continuous_const)).mul
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |arcLineKernel x u| * |Real.sin (c * x)| ≤ 32 * (1 + x ^ 2)⁻¹ * 1 :=
        mul_le_mul (abs_arcLineDeriv_kernel_le u x) (Real.abs_sin_le_one _) (abs_nonneg _)
          (by positivity)
    _ = 32 * (1 + x ^ 2)⁻¹ := mul_one _

theorem integral_arcLineKernel_mul_sin (u : ArcParam) {c : ℝ} (hc : 0 < c) :
    ∫ x, arcLineKernel x u * Real.sin (c * x) =
      2 * c * Real.sqrt (modularArcHeight u) * kMoment 0 (c * modularArcHeight u) *
        Real.cos (c * u) := by
  have hy := modularArcHeight_pos u.2
  have e : (fun x => arcLineKernel x u * Real.sin (c * x)) = fun x =>
      Real.sqrt (modularArcHeight u) * ((x - u) * ((x - u) ^ 2 + modularArcHeight u ^ 2) ^
        (-(3 / 2) : ℝ) * Real.sin (c * x)) := by
    funext x; simp only [arcLineKernel]; ring
  rw [e, integral_const_mul, integral_shift_mul_rpow_sin hy hc]
  ring

/-- **The Basset sine moment of `ψ_u'`.** -/
theorem integral_arcPairDeriv_mul_sin (u : ArcParam) {c : ℝ} (hc : 0 < c) :
    ∫ x, arcPairDeriv u x * Real.sin (c * x) = arcPairSineMoment u c := by
  have e : (fun x => arcPairDeriv u x * Real.sin (c * x)) = fun x =>
      -(arcLineKernel x u * Real.sin (c * x) + arcLineKernel x (arcNeg u) * Real.sin (c * x)) := by
    funext x; simp only [arcPairDeriv]; ring
  rw [e, integral_neg, integral_add (integrable_arcLineKernel_mul_sin u c)
    (integrable_arcLineKernel_mul_sin _ c), integral_arcLineKernel_mul_sin u hc,
    integral_arcLineKernel_mul_sin _ hc]
  simp only [arcNeg, modularArcHeight_neg, arcPairSineMoment]
  rw [show c * -(u : ℝ) = -(c * u) by ring, Real.cos_neg]
  ring

/-- **The filtered sine moments.** -/
theorem integral_filteredArcDeriv_mul_sin {K : ℝ} (hK : 0 < K) (u : ArcParam) {c : ℝ}
    (hc : 0 < c) :
    ∫ x, filteredArcDeriv K u x * Real.sin (c * x) = arcPairSineMoment u c -
      ∫ w, poleFilter K w * (Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)) := by
  have hker := integrable_filteredArcDerivKernel hK u
  have hprod : Integrable (fun p : ℝ × ℝ => filteredArcDerivKernel K u p.1 p.2 *
      Real.sin (c * p.1)) (volume.prod volume) :=
    hker.mul_bdd (by fun_prop) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hswap := integral_integral_swap (f := fun x w =>
    filteredArcDerivKernel K u x w * Real.sin (c * x)) hprod
  have h1 : Integrable fun x => arcPairDeriv u x * Real.sin (c * x) := by
    refine (integrable_inv_one_add_sq.const_mul 64).mono'
      ((continuous_arcPairDeriv u).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |arcPairDeriv u x| * |Real.sin (c * x)| ≤ 64 * (1 + x ^ 2)⁻¹ * 1 :=
          mul_le_mul (abs_arcPairDeriv_le u x) (Real.abs_sin_le_one _) (abs_nonneg _)
            (by positivity)
      _ = 64 * (1 + x ^ 2)⁻¹ := mul_one _
  have h2 : Integrable fun x => (∫ w, filteredArcDerivKernel K u x w) * Real.sin (c * x) := by
    refine hprod.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const]
  have e : (fun x => filteredArcDeriv K u x * Real.sin (c * x)) = fun x =>
      arcPairDeriv u x * Real.sin (c * x) -
        (∫ w, filteredArcDerivKernel K u x w) * Real.sin (c * x) := by
    funext x; simp only [filteredArcDeriv, filteredArcDerivKernel]; ring
  rw [e, integral_sub h1 h2, integral_arcPairDeriv_mul_sin u hc]
  congr 1
  have h3 : ∫ x, (∫ w, filteredArcDerivKernel K u x w) * Real.sin (c * x) =
      ∫ x, ∫ w, filteredArcDerivKernel K u x w * Real.sin (c * x) :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only; rw [integral_mul_const])
  rw [h3, hswap]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [filteredArcDerivKernel]
  have hew : 0 < Real.exp w := Real.exp_pos w
  have hsub : ∫ x, poleFilter K w * (Real.exp (-(3 * w / 2)) * arcPairDeriv u (x * Real.exp (-w))) *
      Real.sin (c * x) = poleFilter K w * Real.exp (-(3 * w / 2)) *
        ∫ x, arcPairDeriv u (x * Real.exp (-w)) * Real.sin (c * Real.exp w * (x * Real.exp (-w))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    have : c * Real.exp w * (x * Real.exp (-w)) = c * x := by
      rw [Real.exp_neg]; field_simp
    rw [this]; ring
  rw [hsub]
  have hcv := Measure.integral_comp_mul_right
    (fun t : ℝ => arcPairDeriv u t * Real.sin (c * Real.exp w * t)) (Real.exp (-w))
  rw [hcv, integral_arcPairDeriv_mul_sin u (by positivity), abs_of_pos (inv_pos.mpr
    (Real.exp_pos _)), smul_eq_mul, ← Real.exp_neg, neg_neg]
  have : Real.exp (-(3 * w / 2)) * Real.exp w = Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

/-- `cosh t ≥ 1 + t²/2`. -/
theorem cosh_ge_one_add_sq_half {t : ℝ} (ht : 0 ≤ t) : 1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h1 : Real.cosh t = 1 + 2 * Real.sinh (t / 2) ^ 2 := by
    have := Real.cosh_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring, Real.cosh_sq] at this
    rw [this]; ring
  have h2 : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  rw [h1]
  nlinarith

/-- **`√r K₀(r) ≤ √(π/2)`.** -/
theorem sqrt_mul_kMoment_zero_le {r : ℝ} (hr : 0 < r) :
    Real.sqrt r * kMoment 0 r ≤ Real.sqrt (Real.pi / 2) := by
  have hb : 0 < r / 2 := by positivity
  have hK : kMoment 0 r ≤ Real.sqrt (Real.pi / (r / 2)) / 2 := by
    rw [kMoment_eq, ← integral_gaussian_Ioi]
    refine setIntegral_mono_on (integrableOn_kIntegrand 0 hr)
      (integrable_exp_neg_mul_sq hb).integrableOn measurableSet_Ioi fun t ht => ?_
    unfold kIntegrand
    rw [pow_zero, one_mul, Real.exp_le_exp]
    have := cosh_ge_one_add_sq_half (le_of_lt ht)
    nlinarith
  have hs : Real.sqrt r * (Real.sqrt (Real.pi / (r / 2)) / 2) = Real.sqrt (Real.pi / 2) := by
    rw [mul_div_assoc', ← Real.sqrt_mul hr.le]
    rw [show r * (Real.pi / (r / 2)) = 2 * Real.pi by field_simp]
    rw [show Real.pi / 2 = 2 * Real.pi / 4 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← hs]
  exact mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _)

/-- `|e^{−w/2} J_u(c e^w)| ≤ 4√(π/2) √c`. -/
theorem abs_exp_mul_arcPairSineMoment_le (u : ArcParam) {c : ℝ} (hc : 0 < c) (w : ℝ) :
    |Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)| ≤
      4 * Real.sqrt (Real.pi / 2) * Real.sqrt c := by
  have hy := modularArcHeight_pos u.2
  set y := modularArcHeight u
  set k := c * Real.exp w with hk
  have hk0 : 0 < k := by positivity
  have hK := sqrt_mul_kMoment_zero_le (show 0 < k * y by positivity)
  have hK0 := kMoment_nonneg 0 (k * y)
  have hsk : Real.sqrt k = Real.sqrt c * Real.exp (w / 2) := by
    rw [hk, Real.sqrt_mul hc.le, Real.exp_half]
  unfold arcPairSineMoment
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ 4 * k * Real.sqrt y * kMoment 0 (k * y))]
  have hcos := Real.abs_cos_le_one (k * u)
  have e1 : 4 * k * Real.sqrt y * kMoment 0 (k * y) =
      4 * Real.sqrt k * (Real.sqrt (k * y) * kMoment 0 (k * y)) := by
    rw [Real.sqrt_mul hk0.le]
    have : k = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hk0.le).symm
    nth_rewrite 1 [this]; ring
  rw [e1, hsk]
  have he : Real.exp (-(w / 2)) * Real.exp (w / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(w / 2)) * (4 * (Real.sqrt c * Real.exp (w / 2)) *
        (Real.sqrt (k * y) * kMoment 0 (k * y)) * |Real.cos (k * u)|)
      = 4 * Real.sqrt c * (Real.sqrt (k * y) * kMoment 0 (k * y)) * |Real.cos (k * u)| *
          (Real.exp (-(w / 2)) * Real.exp (w / 2)) := by ring
    _ ≤ 4 * Real.sqrt c * Real.sqrt (Real.pi / 2) * 1 * 1 := by
        rw [he]
        gcongr
    _ = 4 * Real.sqrt (Real.pi / 2) * Real.sqrt c := by ring

/-- **Uniform error of the filtered moments.** -/
theorem abs_integral_filteredArcDeriv_mul_sin_sub_le {K : ℝ} (hK : 0 < K) (u : ArcParam)
    {c : ℝ} (hc : 0 < c) :
    |(∫ x, filteredArcDeriv K u x * Real.sin (c * x)) - arcPairSineMoment u c| ≤
      4 * Real.sqrt (Real.pi / 2) * Real.sqrt c * (2 * Real.exp (-(K / 4)) + Real.exp (-(K / 2))) := by
  rw [integral_filteredArcDeriv_mul_sin hK u hc, sub_sub_cancel_left, abs_neg]
  set B := 4 * Real.sqrt (Real.pi / 2) * Real.sqrt c
  have hB : 0 ≤ B := by positivity
  have hint : Integrable fun w =>
      poleFilter K w * (Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)) := by
    refine ((integrable_poleFilter hK).abs.const_mul B).mono' ?_ (Eventually.of_forall fun w => ?_)
    · refine ((continuous_poleFilter K).mul ((by fun_prop : Continuous fun w : ℝ =>
        Real.exp (-(w / 2))).mul ?_)).aestronglyMeasurable
      unfold arcPairSineMoment
      have hc' : Continuous fun w : ℝ => kMoment 0 (c * Real.exp w * modularArcHeight u) :=
        (continuousOn_kMoment 0).comp_continuous (by fun_prop) fun w =>
          mul_pos (by positivity) (modularArcHeight_pos u.2)
      exact ((by fun_prop : Continuous fun w : ℝ => 4 * (c * Real.exp w) *
        Real.sqrt (modularArcHeight u)).mul hc').mul (by fun_prop) |>.neg
    · rw [Real.norm_eq_abs, abs_mul]
      calc |poleFilter K w| * |Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)|
          ≤ |poleFilter K w| * B :=
            mul_le_mul_of_nonneg_left (abs_exp_mul_arcPairSineMoment_le u hc w) (abs_nonneg _)
        _ = B * |poleFilter K w| := mul_comm _ _
  calc |∫ w, poleFilter K w * (Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w))|
      ≤ ∫ w, |poleFilter K w * (Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, B * |poleFilter K w| :=
        integral_mono hint.abs ((integrable_poleFilter hK).abs.const_mul B) fun w => by
          simp only
          rw [abs_mul]
          calc |poleFilter K w| * |Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)|
              ≤ |poleFilter K w| * B :=
                mul_le_mul_of_nonneg_left (abs_exp_mul_arcPairSineMoment_le u hc w)
                  (abs_nonneg _)
            _ = B * |poleFilter K w| := mul_comm _ _
    _ = B * ∫ w, |poleFilter K w| := integral_const_mul _ _
    _ ≤ B * (2 * Real.exp (-(K / 4)) + Real.exp (-(K / 2))) :=
        mul_le_mul_of_nonneg_left (integral_abs_poleFilter_le hK) hB

end

end RHTower
