import GaloisForLFunctions.HTGeometry.ComplexRateGammaIntegral
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import Mathlib.Analysis.Calculus.DSlope

/-!
# The sinc separator and its Mellin transform

Fix `λ > 0` and put `κ₊ = λ - iπ`, `κ₋ = λ + iπ`, so that `sin(πy) e^{-λy} = (e^{-κ₊y} - e^{-κ₋y})/(2i)`.
For `ρ ∈ ℂ` and `c ∈ ℂ` the separator kernel is

`ψ(y) = -(1/π) y^{-ρ-1} sin(πy) e^{-λy} + c sin(πy) e^{-λy}`.

It vanishes at every positive integer.  Its Mellin transform continues to the meromorphic function

`Ψ(s) = H(s)/(s - ρ) + c Γ(s) B(s)`,   `H(s) = -(1/π) Γ(s - ρ + 1) Q(s - ρ - 1)`,

with `B(w) = (κ₊^{-w} - κ₋^{-w})/(2i)` and `Q = dslope B 0`, i.e. `Q(w) = B(w)/w`.

* `mellin_sepKernel`: `𝓜ψ = Ψ` on `Re s > Re ρ + 1` (complex-rate Gamma integral).
* `tendsto_sub_mul_sepMellin`: `(s - ρ) Ψ(s) → -1` at `ρ`, because `B(-1) = -π`.
* `norm_sinPair_le`: `|B(w)| ≤ |κ|^{-Re w} e^{(π²/2λ)|Im w|}`, from `|arg κ±| ≤ π²/(2λ)`.  Hence `Ψ`
  decays like `e^{-(π/2 - π²/(2λ))|t|}`; the rate tends to `π/2` as `λ → ∞`.
-/

open MeasureTheory Set Filter Complex
open scoped Topology

noncomputable section

namespace RHTower.SincSeparator

open GaloisForLFunctions.HTGeometry
open HTGeometry

/-- `κ₊ = λ - iπ`. -/
def kp (lam : ℝ) : ℂ := (lam : ℂ) - (Real.pi : ℂ) * I

/-- `κ₋ = λ + iπ`. -/
def km (lam : ℝ) : ℂ := (lam : ℂ) + (Real.pi : ℂ) * I

/-- `B(w) = (κ₊^{-w} - κ₋^{-w})/(2i)`. -/
def sinPair (lam : ℝ) (w : ℂ) : ℂ := (kp lam ^ (-w) - km lam ^ (-w)) / (2 * I)

/-- `Γ(w) B(w) = ∫_0^∞ y^{w-1} sin(πy) e^{-λy} dy` (`Re w > 0`). -/
def sinMellin (lam : ℝ) (w : ℂ) : ℂ := Complex.Gamma w * sinPair lam w

/-- `sin(πy) e^{-λy}`. -/
def sinExp (lam y : ℝ) : ℝ := Real.sin (Real.pi * y) * Real.exp (-(lam * y))

/-- `H(s) = -(1/π) Γ(s - ρ + 1) Q(s - ρ - 1)`. -/
def polarNum (lam : ℝ) (ρ s : ℂ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * Complex.Gamma (s - ρ + 1) * dslope (sinPair lam) 0 (s - ρ - 1)

/-- The separator Mellin function `Ψ(s) = H(s)/(s - ρ) + c Γ(s) B(s)`. -/
def sepMellin (lam : ℝ) (ρ c s : ℂ) : ℂ := polarNum lam ρ s / (s - ρ) + c * sinMellin lam s

/-- The separator kernel `ψ(y) = -(1/π) y^{-ρ-1} sin(πy)e^{-λy} + c sin(πy)e^{-λy}`. -/
def sepKernel (lam : ℝ) (ρ c : ℂ) (y : ℝ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * ((y : ℂ) ^ (-ρ - 1) * (sinExp lam y : ℂ)) + c * (sinExp lam y : ℂ)

variable {lam : ℝ}

theorem kp_re : (kp lam).re = lam := by simp [kp]
theorem km_re : (km lam).re = lam := by simp [km]
theorem kp_im : (kp lam).im = -Real.pi := by simp [kp]
theorem km_im : (km lam).im = Real.pi := by simp [km]

theorem kp_ne_zero (hlam : 0 < lam) : kp lam ≠ 0 := by
  intro h; have := congrArg Complex.re h; rw [kp_re] at this; simp at this; linarith

theorem km_ne_zero (hlam : 0 < lam) : km lam ≠ 0 := by
  intro h; have := congrArg Complex.re h; rw [km_re] at this; simp at this; linarith

theorem norm_km_eq_norm_kp : ‖km lam‖ = ‖kp lam‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  simp [kp, km, Complex.normSq_apply]

theorem lam_le_norm_kp (hlam : 0 < lam) : lam ≤ ‖kp lam‖ := by
  have h := Complex.abs_re_le_norm (kp lam)
  rwa [kp_re, abs_of_pos hlam] at h

/-- `arcsin y ≤ (π/2) y` on `[0,1]`. -/
theorem arcsin_le_pi_div_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.arcsin y ≤ Real.pi / 2 * y := by
  have hx0 : 0 ≤ Real.pi / 2 * y := by positivity
  have hx1 : Real.pi / 2 * y ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin : y ≤ Real.sin (Real.pi / 2 * y) := by
    have := Real.mul_le_sin hx0 hx1
    rwa [show 2 / Real.pi * (Real.pi / 2 * y) = y by field_simp] at this
  calc Real.arcsin y ≤ Real.arcsin (Real.sin (Real.pi / 2 * y)) := Real.arcsin_le_arcsin hsin
    _ = Real.pi / 2 * y := Real.arcsin_sin (by linarith [Real.pi_pos]) hx1

theorem abs_arcsin_eq (x : ℝ) : |Real.arcsin x| = Real.arcsin |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.arcsin_nonneg.mpr hx)]
  · rw [abs_of_nonpos hx, abs_of_nonpos (Real.arcsin_nonpos.mpr hx), Real.arcsin_neg]

/-- For `Re κ = λ > 0` and `|Im κ| = π`: `|arg κ| ≤ π²/(2λ)`. -/
theorem abs_arg_le_of_re {κ : ℂ} (hlam : 0 < lam) (hre : κ.re = lam) (him : |κ.im| = Real.pi) :
    |Complex.arg κ| ≤ Real.pi ^ 2 / (2 * lam) := by
  have hκ0 : κ ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
  have hn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ0
  have hlamn : lam ≤ ‖κ‖ := by have := Complex.abs_re_le_norm κ; rwa [hre, abs_of_pos hlam] at this
  rw [Complex.arg_of_re_nonneg (by rw [hre]; exact hlam.le)]
  have hq : |κ.im / ‖κ‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hn, div_le_one hn]; exact Complex.abs_im_le_norm κ
  rw [abs_arcsin_eq]
  refine (arcsin_le_pi_div_two_mul (abs_nonneg _) hq).trans ?_
  rw [abs_div, abs_of_pos hn, him]
  rw [show Real.pi / 2 * (Real.pi / ‖κ‖) = Real.pi ^ 2 / (2 * ‖κ‖) by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

theorem abs_arg_kp_le (hlam : 0 < lam) : |Complex.arg (kp lam)| ≤ Real.pi ^ 2 / (2 * lam) :=
  abs_arg_le_of_re hlam kp_re (by rw [kp_im, abs_neg, abs_of_pos Real.pi_pos])

theorem abs_arg_km_le (hlam : 0 < lam) : |Complex.arg (km lam)| ≤ Real.pi ^ 2 / (2 * lam) :=
  abs_arg_le_of_re hlam km_re (by rw [km_im, abs_of_pos Real.pi_pos])

theorem norm_cpow_neg_le {κ : ℂ} (hκ : κ ≠ 0) (w : ℂ) :
    ‖κ ^ (-w)‖ ≤ ‖κ‖ ^ (-w.re) * Real.exp (|Complex.arg κ| * |w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hκ, div_eq_mul_inv, ← Real.exp_neg, Complex.neg_re,
    Complex.neg_im]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [mul_neg, neg_neg]
  exact (le_abs_self _).trans (by rw [abs_mul])

/-- `|B(w)| ≤ |κ|^{-Re w} e^{(π²/2λ)|Im w|}`. -/
theorem norm_sinPair_le (hlam : 0 < lam) (w : ℂ) :
    ‖sinPair lam w‖ ≤ ‖kp lam‖ ^ (-w.re) * Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|) := by
  have h1 := norm_cpow_neg_le (kp_ne_zero hlam) w
  have h2 := norm_cpow_neg_le (km_ne_zero hlam) w
  rw [norm_km_eq_norm_kp] at h2
  have e1 : Real.exp (|Complex.arg (kp lam)| * |w.im|) ≤
      Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_arg_kp_le hlam) (abs_nonneg _))
  have e2 : Real.exp (|Complex.arg (km lam)| * |w.im|) ≤
      Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_arg_km_le hlam) (abs_nonneg _))
  have hP : 0 ≤ ‖kp lam‖ ^ (-w.re) := by positivity
  unfold sinPair
  rw [norm_div, show ‖(2 : ℂ) * I‖ = 2 by simp]
  calc ‖kp lam ^ (-w) - km lam ^ (-w)‖ / 2 ≤ (‖kp lam ^ (-w)‖ + ‖km lam ^ (-w)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (‖kp lam‖ ^ (-w.re) * Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|) +
          ‖kp lam‖ ^ (-w.re) * Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|)) / 2 := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left e1 hP)
        · exact h2.trans (mul_le_mul_of_nonneg_left e2 hP)
    _ = _ := by ring

theorem sinPair_zero : sinPair lam 0 = 0 := by simp [sinPair]

theorem sinPair_neg_one : sinPair lam (-1) = -Real.pi := by
  unfold sinPair
  rw [neg_neg, Complex.cpow_one, Complex.cpow_one, kp, km]
  field_simp
  ring

theorem differentiable_sinPair (hlam : 0 < lam) : Differentiable ℂ (sinPair lam) := by
  unfold sinPair
  refine Differentiable.div_const (Differentiable.sub ?_ ?_) _
  · exact Differentiable.const_cpow differentiable_neg (Or.inl (kp_ne_zero hlam))
  · exact Differentiable.const_cpow differentiable_neg (Or.inl (km_ne_zero hlam))

theorem differentiable_dslope_sinPair (hlam : 0 < lam) :
    Differentiable ℂ (dslope (sinPair lam) 0) := by
  have h := (differentiableOn_dslope (f := sinPair lam) (s := univ) (c := 0) Filter.univ_mem).mpr
    (differentiable_sinPair hlam).differentiableOn
  exact fun w => h.differentiableAt Filter.univ_mem

theorem dslope_sinPair_eq (w : ℂ) (hw : w ≠ 0) : dslope (sinPair lam) 0 w = sinPair lam w / w := by
  rw [dslope_of_ne _ hw, slope_def_field, sinPair_zero, sub_zero, sub_zero]

theorem norm_dslope_sinPair_le (hlam : 0 < lam) {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖dslope (sinPair lam) 0 w‖ ≤
      ‖kp lam‖ ^ (-w.re) * Real.exp (Real.pi ^ 2 / (2 * lam) * |w.im|) := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
  rw [dslope_sinPair_eq w hw0, norm_div]
  exact (div_le_self (norm_nonneg _) hw).trans (norm_sinPair_le hlam w)

/-! ## The Mellin transform of `sin(πy) e^{-λy}` -/

theorem sinExp_eq (y : ℝ) :
    ((sinExp lam y : ℝ) : ℂ) =
      (cexp (-(kp lam * y)) - cexp (-(km lam * y))) / (2 * I) := by
  have hp : cexp (-(kp lam * y)) =
      cexp (-((lam * y : ℝ) : ℂ)) * cexp (((Real.pi * y : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; simp only [kp]; push_cast; ring
  have hm : cexp (-(km lam * y)) =
      cexp (-((lam * y : ℝ) : ℂ)) * cexp (-(((Real.pi * y : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; simp only [km]; push_cast; ring
  have hsin : Complex.sin ((Real.pi * y : ℝ) : ℂ) =
      (cexp (((Real.pi * y : ℝ) : ℂ) * I) - cexp (-(((Real.pi * y : ℝ) : ℂ) * I))) / (2 * I) := by
    rw [Complex.sin, div_eq_div_iff (by norm_num) (by simp [Complex.I_ne_zero])]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hp, hm, sinExp, Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_exp, hsin,
    ← mul_sub, mul_div_assoc]
  push_cast
  ring

theorem integral_sinExp_cpow (hlam : 0 < lam) {w : ℂ} (hw : 0 < w.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * ((sinExp lam y : ℝ) : ℂ) = sinMellin lam w := by
  have hp := integral_cpow_mul_cexp_neg_mul_complex hw (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
  have hm := integral_cpow_mul_cexp_neg_mul_complex hw (show 0 < (km lam).re by rw [km_re]; exact hlam)
  have ip := integrableOn_complexRateGammaIntegrand hw (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
  have im := integrableOn_complexRateGammaIntegrand hw (show 0 < (km lam).re by rw [km_re]; exact hlam)
  have hcongr : (fun y : ℝ => (y : ℂ) ^ (w - 1) * ((sinExp lam y : ℝ) : ℂ)) =
      fun y => (complexRateGammaIntegrand w (kp lam) y - complexRateGammaIntegrand w (km lam) y) /
        (2 * I) := by
    funext y
    rw [sinExp_eq, complexRateGammaIntegrand, complexRateGammaIntegrand]
    ring
  rw [hcongr, integral_div, integral_sub ip im]
  unfold complexRateGammaIntegrand
  rw [hp, hm, sinMellin, sinPair]
  ring

theorem sinMellin_one : sinMellin lam 1 = (Real.pi : ℂ) / ((lam : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2) := by
  have hden : (lam : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < lam ^ 2 + Real.pi ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hkp : kp lam ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [kp_im] at this; simp at this
  have hkm : km lam ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [km_im] at this; simp at this
  have hprod : kp lam * km lam = (lam : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 := by
    simp only [kp, km]; ring_nf; rw [Complex.I_sq]; ring
  unfold sinMellin sinPair
  rw [Complex.Gamma_one, one_mul, Complex.cpow_neg_one, Complex.cpow_neg_one, ← hprod]
  field_simp
  simp only [kp, km]
  ring_nf

theorem sinMellin_one_ne_zero (hlam : 0 < lam) : sinMellin lam 1 ≠ 0 := by
  rw [sinMellin_one]
  have hden : (0 : ℝ) < lam ^ 2 + Real.pi ^ 2 := by positivity
  exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hden.ne')

/-! ## The separator Mellin function -/

theorem differentiableAt_polarNum (hlam : 0 < lam) {ρ s : ℂ} (hs : ρ.re - 1 < s.re) :
    DifferentiableAt ℂ (polarNum lam ρ) s := by
  unfold polarNum
  have hG : DifferentiableAt ℂ (fun z => Complex.Gamma (z - ρ + 1)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s
      ((differentiableAt_id.sub_const ρ).add_const 1)
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact ((differentiableAt_const _).mul hG).mul
    ((differentiable_dslope_sinPair hlam).differentiableAt.comp s
      ((differentiableAt_id.sub_const ρ).sub_const 1))

theorem differentiableAt_sinMellin (hlam : 0 < lam) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (sinMellin lam) s := by
  unfold sinMellin
  refine (Complex.differentiableAt_Gamma _ fun m h => ?_).mul
    ((differentiable_sinPair hlam).differentiableAt)
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem differentiableAt_sepMellin (hlam : 0 < lam) {ρ c s : ℂ} (hs0 : 0 < s.re)
    (hs : ρ.re - 1 < s.re) (hsρ : s ≠ ρ) : DifferentiableAt ℂ (sepMellin lam ρ c) s := by
  unfold sepMellin
  exact ((differentiableAt_polarNum hlam hs).div (differentiableAt_id.sub_const ρ)
    (sub_ne_zero.mpr hsρ)).add ((differentiableAt_const c).mul (differentiableAt_sinMellin hlam hs0))

theorem polarNum_self (ρ : ℂ) : polarNum lam ρ ρ = -1 := by
  unfold polarNum
  rw [sub_self, zero_add, Complex.Gamma_one, show (0 : ℂ) - 1 = -1 by ring,
    dslope_sinPair_eq (-1) (by norm_num), sinPair_neg_one]
  field_simp

/-- **The residue at `ρ`:** `(s - ρ) Ψ(s) → -1`. -/
theorem tendsto_sub_mul_sepMellin (hlam : 0 < lam) {ρ c : ℂ} (hρ : 0 < ρ.re) :
    Tendsto (fun s => (s - ρ) * sepMellin lam ρ c s) (𝓝[≠] ρ) (𝓝 (-1)) := by
  have hH : ContinuousAt (polarNum lam ρ) ρ :=
    (differentiableAt_polarNum hlam (by linarith)).continuousAt
  have hS : ContinuousAt (fun s => (s - ρ) * (c * sinMellin lam s)) ρ :=
    ((continuousAt_id.sub continuousAt_const).mul
      (continuousAt_const.mul (differentiableAt_sinMellin hlam hρ).continuousAt))
  have hlim : Tendsto (fun s => polarNum lam ρ s + (s - ρ) * (c * sinMellin lam s)) (𝓝 ρ)
      (𝓝 (-1)) := by
    have := (hH.add hS).tendsto
    simp only [Pi.add_apply, polarNum_self, sub_self, zero_mul, add_zero] at this
    exact this
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  unfold sepMellin
  field_simp

/-! ## The separator kernel and its Mellin transform -/

theorem sinExp_natCast (n : ℕ) : sinExp lam n = 0 := by
  simp [sinExp, Real.sin_nat_mul_pi, mul_comm Real.pi]

theorem sepKernel_natCast (ρ c : ℂ) (n : ℕ) : sepKernel lam ρ c n = 0 := by
  simp [sepKernel, sinExp_natCast]

theorem continuousAt_sepKernel (ρ c : ℂ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (sepKernel lam ρ c) y := by
  have hse : Continuous fun y : ℝ => ((sinExp lam y : ℝ) : ℂ) := by
    unfold sinExp; fun_prop
  unfold sepKernel
  refine ((continuousAt_const.mul ((continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')).mul
    hse.continuousAt))).add (continuousAt_const.mul hse.continuousAt)

theorem mellin_sinExp (hlam : 0 < lam) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun y => ((sinExp lam y : ℝ) : ℂ)) s = sinMellin lam s := by
  rw [mellin, ← integral_sinExp_cpow hlam hs]
  rfl

/-- `𝓜ψ = Ψ` on `Re s > Re ρ + 1`. -/
theorem mellin_sepKernel (hlam : 0 < lam) {ρ c s : ℂ} (hρ : 0 < ρ.re) (hs : ρ.re + 1 < s.re) :
    mellin (sepKernel lam ρ c) s = sepMellin lam ρ c s := by
  set w : ℂ := s - ρ - 1 with hw
  have hw0 : 0 < w.re := by simp [hw]; linarith
  have hs0 : 0 < s.re := by linarith
  have hI1 := integral_sinExp_cpow hlam hw0
  have hI2 := integral_sinExp_cpow hlam hs0
  have hint1 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (w - 1) * ((sinExp lam y : ℝ) : ℂ)) (Ioi 0) := by
    have hp := integrableOn_complexRateGammaIntegrand hw0 (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
    have hm := integrableOn_complexRateGammaIntegrand hw0 (show 0 < (km lam).re by rw [km_re]; exact hlam)
    refine IntegrableOn.congr_fun ((hp.sub hm).div_const (2 * I)) (fun y _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply, complexRateGammaIntegrand, complexRateGammaIntegrand, sinExp_eq]; ring
  have hint2 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * ((sinExp lam y : ℝ) : ℂ)) (Ioi 0) := by
    have hp := integrableOn_complexRateGammaIntegrand hs0 (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
    have hm := integrableOn_complexRateGammaIntegrand hs0 (show 0 < (km lam).re by rw [km_re]; exact hlam)
    refine IntegrableOn.congr_fun ((hp.sub hm).div_const (2 * I)) (fun y _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply, complexRateGammaIntegrand, complexRateGammaIntegrand, sinExp_eq]; ring
  have hsplit : ∀ y ∈ Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) • sepKernel lam ρ c y =
      -(1 / (Real.pi : ℂ)) * ((y : ℂ) ^ (w - 1) * ((sinExp lam y : ℝ) : ℂ)) +
        c * ((y : ℂ) ^ (s - 1) * ((sinExp lam y : ℝ) : ℂ)) := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
    have hpow : (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-ρ - 1) = (y : ℂ) ^ (w - 1) := by
      rw [← Complex.cpow_add _ _ hy0, hw]; ring_nf
    rw [smul_eq_mul, sepKernel]
    linear_combination (-(1 / (Real.pi : ℂ)) * ((sinExp lam y : ℝ) : ℂ)) * hpow
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add ((hint1.const_mul _))
    (hint2.const_mul _), integral_const_mul, integral_const_mul, hI1, hI2]
  -- `H(s)/(s-ρ) = -(1/π) Γ(w) B(w)`
  have hw1 : w + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hw00 : w ≠ 0 := by intro h; rw [h] at hw0; simp at hw0
  have hsρ : s - ρ = w + 1 := by rw [hw]; ring
  have hG : Complex.Gamma (s - ρ + 1) = (w + 1) * (w * Complex.Gamma w) := by
    rw [show s - ρ + 1 = (w + 1) + 1 by rw [hw]; ring, Complex.Gamma_add_one _ hw1,
      Complex.Gamma_add_one _ hw00]
  unfold sepMellin polarNum sinMellin
  rw [show s - ρ - 1 = w from rfl, dslope_sinPair_eq w hw00, hG, hsρ]
  field_simp

/-! ## Vertical decay -/

theorem rpow_le_add_of_mem {b x x₁ x₂ : ℝ} (hb : 0 < b) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) :
    b ^ x ≤ b ^ x₁ + b ^ x₂ := by
  rcases le_total 1 b with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h hx₂).trans (le_add_of_nonneg_left (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_ge hb h hx₁).trans (le_add_of_nonneg_right (by positivity))

/-- `|t|^N e^{-δ|t|} ≤ M (1 + t²)⁻¹` for `|t| ≥ 1`. -/
theorem exists_pow_mul_exp_neg_le {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ M : ℝ, ∀ t : ℝ, 1 ≤ |t| → |t| ^ N * Real.exp (-(δ * |t|)) ≤ M * (1 + t ^ 2)⁻¹ := by
  refine ⟨2 * (N + 2).factorial / δ ^ (N + 2), fun t ht => ?_⟩
  have hexp := Real.pow_div_factorial_le_exp (δ * |t|) (by positivity) (N + 2)
  have hf : (0 : ℝ) < (N + 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have hsq : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by rw [sq_abs]; nlinarith [sq_abs t]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [mul_pow, div_le_iff₀ hf] at hexp
  have hkey : |t| ^ (N + 2) * Real.exp (-(δ * |t|)) ≤ (N + 2).factorial / δ ^ (N + 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc |t| ^ (N + 2) * Real.exp (-(δ * |t|)) * δ ^ (N + 2)
        = (δ ^ (N + 2) * |t| ^ (N + 2)) * Real.exp (-(δ * |t|)) := by ring
      _ ≤ (Real.exp (δ * |t|) * (N + 2).factorial) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = (N + 2).factorial := by
          rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; simp
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc |t| ^ N * Real.exp (-(δ * |t|)) * (1 + t ^ 2)
      ≤ |t| ^ N * Real.exp (-(δ * |t|)) * (2 * |t| ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * (|t| ^ (N + 2) * Real.exp (-(δ * |t|))) := by ring
    _ ≤ 2 * ((N + 2).factorial / δ ^ (N + 2)) := by gcongr
    _ = 2 * (N + 2).factorial / δ ^ (N + 2) := by ring

/-- **Vertical decay of the separator.**  On a vertical strip `σ₁ ≤ Re s ≤ σ₂`,
`|Ψ(s)| ≤ K |t|^N e^{-(π/2 - π²/(2λ))|t|}` for `|t| ≥ |Im ρ| + 2`. -/
theorem exists_norm_sepMellin_le (hlam : 0 < lam) (ρ c : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |ρ.im| + 2 ≤ |s.im| →
      ‖sepMellin lam ρ c s‖ ≤
        K * |s.im| ^ N * Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * lam)) * |s.im|)) := by
  set θ : ℝ := Real.pi ^ 2 / (2 * lam) with hθ
  set δ : ℝ := Real.pi / 2 - θ with hδ
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ := exists_sharp_bound_norm_Gamma_strip (σ₁ - ρ.re + 1) (σ₂ - ρ.re + 1)
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ := exists_sharp_bound_norm_Gamma_strip σ₁ σ₂
  set b : ℝ := ‖kp lam‖ with hb
  have hb0 : 0 < b := norm_pos_iff.mpr (kp_ne_zero hlam)
  set P₁ : ℝ := b ^ (ρ.re + 1 - σ₂) + b ^ (ρ.re + 1 - σ₁) with hP₁
  set P₂ : ℝ := b ^ (-σ₂) + b ^ (-σ₁) with hP₂
  have hP₁0 : 0 ≤ P₁ := by positivity
  have hP₂0 : 0 ≤ P₂ := by positivity
  set γ : ℝ := ρ.im with hγ
  refine ⟨(1 / Real.pi) * C₁ * P₁ * 2 ^ N₁ * Real.exp (|δ| * |γ|) + ‖c‖ * C₂ * P₂, N₁ + N₂,
    fun s hs1 hs2 ht => ?_⟩
  set t : ℝ := s.im with ht_def
  have htγ : 1 ≤ |t - γ| := by
    have := abs_sub_abs_le_abs_sub t γ; linarith
  have ht1 : 1 ≤ |t| := by linarith [abs_nonneg γ]
  have htγ2 : |t - γ| ≤ 2 * |t| := by
    have := abs_sub t γ; linarith [abs_nonneg γ]
  -- the polar part
  set z : ℂ := s - ρ + 1 with hz
  set w : ℂ := s - ρ - 1 with hw
  have hzre1 : σ₁ - ρ.re + 1 ≤ z.re := by simp [hz]; linarith
  have hzre2 : z.re ≤ σ₂ - ρ.re + 1 := by simp [hz]; linarith
  have hzim : z.im = t - γ := by simp [hz, ht_def, hγ]
  have hwim : w.im = t - γ := by simp [hw, ht_def, hγ]
  have hwre : -w.re = ρ.re + 1 - s.re := by simp [hw]; ring
  have hG1 : ‖Complex.Gamma z‖ ≤ C₁ * |t - γ| ^ N₁ * Real.exp (-(Real.pi * |t - γ| / 2)) := by
    have := hΓ₁ z hzre1 hzre2 (by rw [hzim]; exact htγ)
    rwa [hzim] at this
  have hwn : 1 ≤ ‖w‖ := le_trans (by rw [hwim]; exact htγ) (Complex.abs_im_le_norm w)
  have hQ : ‖dslope (sinPair lam) 0 w‖ ≤ P₁ * Real.exp (θ * |t - γ|) := by
    have h := norm_dslope_sinPair_le hlam hwn
    rw [hwim, hwre] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact rpow_le_add_of_mem hb0 (by linarith) (by linarith)
  have hsρ : 1 ≤ ‖s - ρ‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm (s - ρ))
    simpa [ht_def, hγ] using htγ
  have hpolar : ‖polarNum lam ρ s / (s - ρ)‖ ≤
      (1 / Real.pi) * C₁ * P₁ * |t - γ| ^ N₁ * Real.exp (-(δ * |t - γ|)) := by
    rw [norm_div]
    refine (div_le_self (norm_nonneg _) hsρ).trans ?_
    unfold polarNum
    rw [show s - ρ - 1 = w from rfl, show s - ρ + 1 = z from rfl, norm_mul, norm_mul, norm_neg,
      norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc 1 / Real.pi * ‖Complex.Gamma z‖ * ‖dslope (sinPair lam) 0 w‖
        ≤ 1 / Real.pi * (C₁ * |t - γ| ^ N₁ * Real.exp (-(Real.pi * |t - γ| / 2))) *
            (P₁ * Real.exp (θ * |t - γ|)) := by gcongr
      _ = (1 / Real.pi) * C₁ * P₁ * |t - γ| ^ N₁ *
            (Real.exp (-(Real.pi * |t - γ| / 2)) * Real.exp (θ * |t - γ|)) := by ring
      _ = (1 / Real.pi) * C₁ * P₁ * |t - γ| ^ N₁ * Real.exp (-(δ * |t - γ|)) := by
          rw [← Real.exp_add, hδ]; ring_nf
  have hshift : |t - γ| ^ N₁ * Real.exp (-(δ * |t - γ|)) ≤
      2 ^ N₁ * Real.exp (|δ| * |γ|) * (|t| ^ N₁ * Real.exp (-(δ * |t|))) := by
    have hpow : |t - γ| ^ N₁ ≤ 2 ^ N₁ * |t| ^ N₁ := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) htγ2 N₁
    have hex : Real.exp (-(δ * |t - γ|)) ≤ Real.exp (|δ| * |γ|) * Real.exp (-(δ * |t|)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h3 : abs (|t - γ| - |t|) ≤ |γ| := by
        have := abs_abs_sub_abs_le_abs_sub (t - γ) t
        simpa [abs_neg] using this
      have h4 : -(δ * |t - γ|) + δ * |t| ≤ |δ| * |γ| := by
        have : -(δ * |t - γ|) + δ * |t| = -(δ * (|t - γ| - |t|)) := by ring
        rw [this]
        calc -(δ * (|t - γ| - |t|)) ≤ |δ * (|t - γ| - |t|)| := neg_le_abs _
          _ = |δ| * abs (|t - γ| - |t|) := abs_mul _ _
          _ ≤ |δ| * |γ| := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      linarith
    calc |t - γ| ^ N₁ * Real.exp (-(δ * |t - γ|))
        ≤ (2 ^ N₁ * |t| ^ N₁) * (Real.exp (|δ| * |γ|) * Real.exp (-(δ * |t|))) :=
          mul_le_mul hpow hex (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  -- the regular part
  have hsre1 : σ₁ ≤ s.re := hs1
  have hG2 : ‖Complex.Gamma s‖ ≤ C₂ * |t| ^ N₂ * Real.exp (-(Real.pi * |t| / 2)) :=
    hΓ₂ s hs1 hs2 ht1
  have hB : ‖sinPair lam s‖ ≤ P₂ * Real.exp (θ * |t|) := by
    refine (norm_sinPair_le hlam s).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact rpow_le_add_of_mem hb0 (by linarith) (by linarith)
  have hreg : ‖c * sinMellin lam s‖ ≤ ‖c‖ * C₂ * P₂ * (|t| ^ N₂ * Real.exp (-(δ * |t|))) := by
    unfold sinMellin
    rw [norm_mul, norm_mul]
    calc ‖c‖ * (‖Complex.Gamma s‖ * ‖sinPair lam s‖)
        ≤ ‖c‖ * ((C₂ * |t| ^ N₂ * Real.exp (-(Real.pi * |t| / 2))) * (P₂ * Real.exp (θ * |t|))) := by
          gcongr
      _ = ‖c‖ * C₂ * P₂ * (|t| ^ N₂ * (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (θ * |t|))) := by
          ring
      _ = _ := by rw [← Real.exp_add, hδ]; ring_nf
  have hN1 : |t| ^ N₁ ≤ |t| ^ (N₁ + N₂) := pow_le_pow_right₀ ht1 (by omega)
  have hN2 : |t| ^ N₂ ≤ |t| ^ (N₁ + N₂) := pow_le_pow_right₀ ht1 (by omega)
  have hE : 0 ≤ Real.exp (-(δ * |t|)) := (Real.exp_pos _).le
  have hc0 : 0 ≤ ‖c‖ * C₂ * P₂ := by positivity
  have hA0 : 0 ≤ (1 / Real.pi) * C₁ * P₁ := by positivity
  unfold sepMellin
  calc ‖polarNum lam ρ s / (s - ρ) + c * sinMellin lam s‖
      ≤ ‖polarNum lam ρ s / (s - ρ)‖ + ‖c * sinMellin lam s‖ := norm_add_le _ _
    _ ≤ (1 / Real.pi) * C₁ * P₁ * (2 ^ N₁ * Real.exp (|δ| * |γ|) * (|t| ^ N₁ * Real.exp (-(δ * |t|))))
        + ‖c‖ * C₂ * P₂ * (|t| ^ N₂ * Real.exp (-(δ * |t|))) := by
        refine add_le_add (hpolar.trans ?_) hreg
        rw [mul_assoc ((1 / Real.pi) * C₁ * P₁)]
        exact mul_le_mul_of_nonneg_left hshift hA0
    _ ≤ (1 / Real.pi) * C₁ * P₁ * (2 ^ N₁ * Real.exp (|δ| * |γ|) *
          (|t| ^ (N₁ + N₂) * Real.exp (-(δ * |t|))))
        + ‖c‖ * C₂ * P₂ * (|t| ^ (N₁ + N₂) * Real.exp (-(δ * |t|))) := by
        gcongr
    _ = _ := by ring

end RHTower.SincSeparator
