import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualExpansion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# High-block law: the Gaussian cutoff is real, decreasing, with values in `[0, 1]`

`V(x) = (1/2π) ∫ x^{−(1+it)} e^{(1+it)²}/(1+it) dt` has derivative
`V'(x) = −e^{−(log x)²/4} / (2√π x)` for `x > 0` (differentiation under the integral sign and the
Gaussian integral). Hence `Im V ≡ 0` on `(0,∞)` (constant, and `V → 0` at `∞`), `Re V` is antitone,
and `0 ≤ V ≤ 1` (`V → 1` at `0⁺`, `V → 0` at `∞`). These are the inputs of the total-variation bound
that reduces smooth mollified energies to sharp-cutoff ones.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- `d/dy (y:ℂ)^{−w} = −w y^{−w−1}` for real `y > 0`. -/
theorem hasDerivAt_ofReal_cpow_neg_highBlockCutoffMonotone {w : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-w - 1)) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have h1 : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    hlog.ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => -w * ((Real.log y : ℝ) : ℂ)) (-w * ((x⁻¹ : ℝ) : ℂ)) x :=
    h1.const_mul (-w)
  have h3 := h2.cexp
  have hfun : (fun y : ℝ => (y : ℂ) ^ (-w)) =ᶠ[𝓝 x]
      fun y : ℝ => Complex.exp (-w * ((Real.log y : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hy)),
      ← Complex.ofReal_log hy.le, mul_comm]
  refine (h3.congr_of_eventuallyEq hfun).congr_deriv ?_
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.cpow_def_of_ne_zero hx0,
    ← Complex.ofReal_log hx.le]
  push_cast
  ring

/-- The `x`-derivative of the Mellin integrand at `Re w = 1`. -/
def cutoffDerivIntegrand (x t : ℝ) : ℂ :=
  -(((1 : ℝ) : ℂ) + (t : ℂ) * I) * (x : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℂ) * I) - 1) *
    smoothAFEGaussianKernel (((1 : ℝ) : ℂ) + (t : ℂ) * I)

theorem hasDerivAt_smoothAFEMellinIntegrand_line_one {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun y : ℝ => smoothAFEMellinIntegrand y (((1 : ℝ) : ℂ) + (t : ℂ) * I))
      (cutoffDerivIntegrand x t) x := by
  unfold smoothAFEMellinIntegrand cutoffDerivIntegrand
  exact (hasDerivAt_ofReal_cpow_neg_highBlockCutoffMonotone hx).mul_const _

theorem norm_cutoffDerivIntegrand_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖cutoffDerivIntegrand x t‖ ≤ (Real.exp 1 * x ^ (-2 : ℝ)) * ((1 + |t|) * Real.exp (-(t ^ 2))) := by
  unfold cutoffDerivIntegrand
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-(((1 : ℝ) : ℂ) + (t : ℂ) * I) - 1).re = -2 := by simp; norm_num
  rw [hre]
  have hw : ‖((1 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ 1 + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_one]
  have hk := norm_smoothAFEGaussianKernel_vertical_le (σ := (1 : ℝ)) one_pos t
  rw [one_pow, div_one] at hk
  calc ‖((1 : ℝ) : ℂ) + (t : ℂ) * I‖ * x ^ (-2 : ℝ) *
        ‖smoothAFEGaussianKernel (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (1 + |t|) * x ^ (-2 : ℝ) * (Real.exp 1 * Real.exp (-(t ^ 2))) := by
        gcongr
    _ = (Real.exp 1 * x ^ (-2 : ℝ)) * ((1 + |t|) * Real.exp (-(t ^ 2))) := by ring

theorem continuous_cutoffDerivIntegrand {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => cutoffDerivIntegrand x t) := by
  unfold cutoffDerivIntegrand smoothAFEGaussianKernel
  have hw : Continuous (fun t : ℝ => ((1 : ℝ) : ℂ) + (t : ℂ) * I) := by fun_prop
  have hw0 : ∀ t : ℝ, ((1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hc : Continuous (fun t : ℝ => (x : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℂ) * I) - 1)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hx0)
  have hk : Continuous (fun t : ℝ => Complex.exp ((((1 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2) /
      (((1 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    (Complex.continuous_exp.comp (hw.pow 2)).div hw hw0
  exact (hw.neg.mul hc).mul hk

/-- **Derivative of the cutoff, integral form.** -/
theorem hasDerivAt_smoothAFECutoff_integral {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => smoothAFECutoff y)
      ((1 / (2 * Real.pi)) • ∫ t : ℝ, cutoffDerivIntegrand x t) x := by
  have hfun : (fun y : ℝ => smoothAFECutoff y) = fun y : ℝ =>
      (1 / (2 * Real.pi)) • ∫ t : ℝ, smoothAFEMellinIntegrand y (((1 : ℝ) : ℂ) + (t : ℂ) * I) := by
    funext y
    rw [smoothAFECutoff, smoothAFECutoffAt_eq_integral]
  rw [hfun]
  refine HasDerivAt.const_smul (1 / (2 * Real.pi) : ℝ) ?_
  have hε : 0 < x / 2 := by linarith
  have hbound_int : Integrable (fun t : ℝ =>
      (Real.exp 1 * (x / 2) ^ (-2 : ℝ)) * ((1 + |t|) * Real.exp (-(t ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun t => (Real.exp 1 * (x / 2) ^ (-2 : ℝ)) * ((1 + |t|) * Real.exp (-(t ^ 2))))
    (F := fun y t => smoothAFEMellinIntegrand y (((1 : ℝ) : ℂ) + (t : ℂ) * I))
    (F' := fun y t => cutoffDerivIntegrand y t) (s := ball x (x / 2))
    (ball_mem_nhds x hε) ?_ ?_ ?_ ?_ hbound_int ?_).2
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    have h := smoothAFEMellinIntegrand_verticalIntegrable (x := y) (σ := 1) hy one_pos
    rw [Complex.VerticalIntegrable] at h
    exact h.aestronglyMeasurable
  · have h := smoothAFEMellinIntegrand_verticalIntegrable (x := x) (σ := 1) hx one_pos
    rw [Complex.VerticalIntegrable] at h
    exact h
  · exact (continuous_cutoffDerivIntegrand hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t y hy => ?_
    have hy0 : x / 2 < y := by
      rw [mem_ball, Real.dist_eq, abs_lt] at hy
      linarith [hy.1]
    have hypos : 0 < y := by linarith
    refine (norm_cutoffDerivIntegrand_le hypos t).trans ?_
    have hy0le : x / 2 ≤ y := hy0.le
    have hmono : y ^ (-2 : ℝ) ≤ (x / 2) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hypos.le, Real.rpow_neg hε.le, Real.rpow_two, Real.rpow_two]
      gcongr
    gcongr
  · refine Filter.Eventually.of_forall fun t y hy => ?_
    have hy0 : x / 2 < y := by
      rw [mem_ball, Real.dist_eq, abs_lt] at hy
      linarith [hy.1]
    exact hasDerivAt_smoothAFEMellinIntegrand_line_one (by linarith) t

/-- The derivative integrand as a Gaussian. -/
theorem cutoffDerivIntegrand_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    cutoffDerivIntegrand x t =
      -((x : ℂ) ^ (-(2 : ℂ))) *
        Complex.exp ((-1 : ℂ) * (t : ℂ) ^ 2 + (I * (2 - (Real.log x : ℂ))) * (t : ℂ) + 1) := by
  unfold cutoffDerivIntegrand smoothAFEGaussianKernel
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hw0 : ((1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
  field_simp
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The closed form of the derivative:** `V'(x) = −e^{−(log x)²/4}/(2√π x)`. -/
theorem hasDerivAt_smoothAFECutoff {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => smoothAFECutoff y)
      (((-(Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi * x)) : ℝ) : ℂ)) x := by
  refine (hasDerivAt_smoothAFECutoff_integral hx).congr_deriv ?_
  have hint : (∫ t : ℝ, cutoffDerivIntegrand x t) =
      -((x : ℂ) ^ (-(2 : ℂ))) *
        ∫ t : ℝ, Complex.exp ((-1 : ℂ) * (t : ℂ) ^ 2 + (I * (2 - (Real.log x : ℂ))) * (t : ℂ) + 1) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => cutoffDerivIntegrand_eq hx t)
  rw [hint, integral_cexp_quadratic (by norm_num) _ _]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hL : Complex.exp ((Real.log x : ℂ)) = (x : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hx]
  have hsq : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ ((1 : ℂ) / 2) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    try rfl
  have hexp : Complex.exp ((1 : ℂ) - (I * (2 - (Real.log x : ℂ))) ^ 2 / (4 * (-1 : ℂ))) =
      (x : ℂ) * Complex.exp (((-(Real.log x) ^ 2 / 4 : ℝ) : ℂ)) := by
    rw [← hL, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hsq, hexp]
  have hpow : (x : ℂ) ^ (-(2 : ℂ)) = ((x ^ (-2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le]
    push_cast
    rfl
  rw [hpow, Complex.real_smul]
  have hx2 : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.rpow_neg hx.le, one_div]
    norm_cast
  rw [hx2]
  have hsqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsπC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsπ.ne'
  have hπC : (Real.pi : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsqrt]
  push_cast
  rw [hπC]
  field_simp
  try ring

/-- The cutoff's derivative, in real form. -/
def smoothAFECutoffDeriv (x : ℝ) : ℝ :=
  -(Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi * x))

theorem smoothAFECutoffDeriv_nonpos {x : ℝ} (hx : 0 < x) : smoothAFECutoffDeriv x ≤ 0 := by
  unfold smoothAFECutoffDeriv
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have : 0 ≤ Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi * x) := by positivity
  linarith

theorem hasDerivAt_smoothAFECutoff_re {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (smoothAFECutoff y).re) (smoothAFECutoffDeriv x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_smoothAFECutoff hx)
  rw [Complex.reCLM_apply, Complex.ofReal_re] at h
  exact h

theorem hasDerivAt_smoothAFECutoff_im {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (smoothAFECutoff y).im) 0 x := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_smoothAFECutoff hx)
  rw [Complex.imCLM_apply, Complex.ofReal_im] at h
  exact h

/-- The imaginary part is constant on `(0, ∞)`. -/
theorem smoothAFECutoff_im_eq_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (smoothAFECutoff a).im = (smoothAFECutoff b).im := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha (not_le.mp hab).le).symm
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => (smoothAFECutoff y).im) (f' := fun _ => (0 : ℝ)) (a := a) (b := b)
    (fun y hy => hasDerivAt_smoothAFECutoff_im (by
      rw [Set.uIcc_of_le hab] at hy
      linarith [hy.1]))
    (by simp)
  rw [intervalIntegral.integral_zero] at h
  linarith

/-- **The cutoff is real on `(0, ∞)`.** -/
theorem smoothAFECutoff_im_eq_zero {x : ℝ} (hx : 0 < x) : (smoothAFECutoff x).im = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  have hbound : ∀ y : ℝ, 0 < y → |(smoothAFECutoff x).im| ≤ K / y := by
    intro y hy
    rw [smoothAFECutoff_im_eq_of_pos hx hy]
    calc |(smoothAFECutoff y).im| ≤ ‖smoothAFECutoff y‖ := Complex.abs_im_le_norm _
      _ ≤ K * y ^ (-(1 : ℝ)) := hK hy
      _ = K / y := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hle : |(smoothAFECutoff x).im| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    have hy : 0 < max 1 (K / ε) := lt_max_of_lt_left one_pos
    refine (hbound _ hy).trans ?_
    rw [div_le_iff₀ hy]
    calc K = ε * (K / ε) := by field_simp
      _ ≤ ε * max 1 (K / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
  exact abs_nonpos_iff.mp hle

/-- **The real part is antitone on `(0, ∞)`.** -/
theorem smoothAFECutoff_re_antitoneOn :
    AntitoneOn (fun y : ℝ => (smoothAFECutoff y).re) (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro y hy
    exact (hasDerivAt_smoothAFECutoff_re hy).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro y hy
    exact (hasDerivAt_smoothAFECutoff_re hy).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro y hy
    rw [(hasDerivAt_smoothAFECutoff_re hy).deriv]
    exact smoothAFECutoffDeriv_nonpos hy

/-- `0 ≤ Re V` on `(0, ∞)`. -/
theorem smoothAFECutoff_re_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ (smoothAFECutoff x).re := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  have hbound : ∀ y : ℝ, x ≤ y → -(K / y) ≤ (smoothAFECutoff x).re := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hx hy
    have hmono := smoothAFECutoff_re_antitoneOn hx hy0 hy
    have h1 : -(K / y) ≤ (smoothAFECutoff y).re := by
      have := Complex.abs_re_le_norm (smoothAFECutoff y)
      have h2 : ‖smoothAFECutoff y‖ ≤ K / y := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        exact hK hy0
      linarith [neg_abs_le (smoothAFECutoff y).re]
    exact h1.trans hmono
  have hle : -(smoothAFECutoff x).re ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    have hy : x ≤ max x (K / ε) := le_max_left _ _
    have hy0 : 0 < max x (K / ε) := lt_of_lt_of_le hx hy
    have h := hbound _ hy
    have hKε : K / max x (K / ε) ≤ ε := by
      rw [div_le_iff₀ hy0]
      calc K = ε * (K / ε) := by field_simp
        _ ≤ ε * max x (K / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
    linarith
  linarith

/-- `Re V ≤ 1` on `(0, ∞)`. -/
theorem smoothAFECutoff_re_le_one {x : ℝ} (hx : 0 < x) : (smoothAFECutoff x).re ≤ 1 := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
  have hbound : ∀ y : ℝ, 0 < y → y ≤ x → (smoothAFECutoff x).re ≤ 1 + K * y := by
    intro y hy0 hy
    have hmono := smoothAFECutoff_re_antitoneOn hy0 hx hy
    have h1 : (smoothAFECutoff y).re ≤ 1 + K * y := by
      have := Complex.abs_re_le_norm (smoothAFECutoff y - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have h2 : ‖smoothAFECutoff y - 1‖ ≤ K * y := by
        have := hK hy0
        rwa [Real.rpow_one] at this
      linarith [le_abs_self ((smoothAFECutoff y).re - 1)]
    exact hmono.trans h1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hy0 : 0 < min x (ε / (K + 1)) := lt_min hx (by positivity)
  have hy : min x (ε / (K + 1)) ≤ x := min_le_left _ _
  have h := hbound _ hy0 hy
  have hKy : K * min x (ε / (K + 1)) ≤ ε := by
    calc K * min x (ε / (K + 1)) ≤ K * (ε / (K + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
      _ ≤ (K + 1) * (ε / (K + 1)) := by gcongr; linarith
      _ = ε := by field_simp
  linarith

end

end RHTower
