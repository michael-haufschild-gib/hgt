import GaloisForLFunctions.RHTower.ThetaGroupFormCuspBounds

/-!
# Exact theta-group modularity does not force real zeros

The forms `θ₃(1 + t₁h + t₂h²)` (`h` the `Γ_θ` Hauptmodul) are two-periodic, satisfy the exact theta
inversion law, and have even theta sources built from the same Gaussian atoms with integer
frequencies.  Their transforms are `Ξ₀ + t₁Ξ₁ + t₂Ξ₂`.  This module proves:

* Fourier injectivity for continuous integrable functions (`eq_zero_of_fourier_eq_zero`);
* a vanishing source forces the form to vanish on the imaginary axis (ODE recovery);
* `Ξ₁` and `Ξ₂` are `ℝ`-linearly independent entire functions;
* by the open mapping and identity theorems they are pointwise `ℝ`-independent somewhere in
  `0 < im z < 1/2`, and Cramer's rule then gives real `t₁, t₂` with an off-line zero there
  (`thetaGroup_offLine_strip_zero`).
-/

open Complex MeasureTheory Filter Topology
open scoped Real ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Fourier injectivity for continuous integrable functions -/

/-- A continuous integrable real function with vanishing Fourier transform is zero. -/
theorem eq_zero_of_real_fourier_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f)
    (h : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (t * x * I) * (f x : ℂ) = 0) : f = 0 := by
  set fp : ℝ → NNReal := fun x => Real.toNNReal (f x) with hfp
  set fn : ℝ → NNReal := fun x => Real.toNNReal (-f x) with hfn
  have hfpm : Measurable fp := (hf.measurable).real_toNNReal
  have hfnm : Measurable fn := (hf.measurable.neg).real_toNNReal
  haveI : IsFiniteMeasure (volume.withDensity fun x => (fp x : ENNReal)) :=
    isFiniteMeasure_withDensity_ofReal hfi.hasFiniteIntegral
  haveI : IsFiniteMeasure (volume.withDensity fun x => (fn x : ENNReal)) :=
    isFiniteMeasure_withDensity_ofReal hfi.neg.hasFiniteIntegral
  have hpInt : Integrable (fun x => ((fp x : ℝ) : ℂ)) := by
    refine (hfi.norm.ofReal).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, hfp]
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    simp only [Real.coe_toNNReal']
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnInt : Integrable (fun x => ((fn x : ℝ) : ℂ)) := by
    refine (hfi.norm.ofReal).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, hfn]
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    simp only [Real.coe_toNNReal']
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hsplit : ∀ x, (f x : ℂ) = ((fp x : ℝ) : ℂ) - ((fn x : ℝ) : ℂ) := by
    intro x
    simp only [hfp, hfn, Real.coe_toNNReal']
    rcases le_total 0 (f x) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; simp
    · rw [max_eq_right h0, max_eq_left (by linarith)]; simp
  have hchar : charFun (volume.withDensity fun x => (fp x : ENNReal)) =
      charFun (volume.withDensity fun x => (fn x : ENNReal)) := by
    funext t
    rw [charFun_apply_real, charFun_apply_real,
      integral_withDensity_eq_integral_smul hfpm, integral_withDensity_eq_integral_smul hfnm]
    have hbound : ∀ g : ℝ → ℂ, Integrable g →
        Integrable (fun x => g x * Complex.exp (t * x * I)) := by
      intro g hg
      refine hg.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Complex.norm_exp]
      simp
    have h1 := h t
    have heq : (fun x : ℝ => Complex.exp (t * x * I) * (f x : ℂ)) =
        fun x => ((fp x : ℝ) : ℂ) * Complex.exp (t * x * I) -
          ((fn x : ℝ) : ℂ) * Complex.exp (t * x * I) := by
      funext x; rw [hsplit x]; ring
    rw [heq, integral_sub (hbound _ hpInt) (hbound _ hnInt), sub_eq_zero] at h1
    simp only [NNReal.smul_def, Complex.real_smul]
    exact h1
  have hmeq := Measure.ext_of_charFun hchar
  have hae : (fun x => (fp x : ENNReal)) =ᵐ[volume] fun x => (fn x : ENNReal) := by
    rw [withDensity_eq_iff hfpm.coe_nnreal_ennreal.aemeasurable
      hfnm.coe_nnreal_ennreal.aemeasurable] at hmeq
    · exact hmeq
    · refine (lt_of_le_of_lt (lintegral_mono fun x => ?_) hfi.hasFiniteIntegral).ne
      show ENNReal.ofReal (f x) ≤ ‖f x‖ₑ
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hae' : f =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have hx' : fp x = fn x := by exact_mod_cast hx
    have := hsplit x
    rw [hx', sub_self] at this
    exact_mod_cast this
  exact (Continuous.ae_eq_iff_eq volume hf continuous_const).mp hae'


/-- Complex version: a continuous integrable function with vanishing Fourier transform is zero. -/
theorem eq_zero_of_fourier_eq_zero {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (h : ∀ u : ℝ, ∫ x : ℝ, Complex.exp (-I * u * x) * k x = 0) : k = 0 := by
  have hconj : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (t * x * I) * conj (k x) = 0 := by
    intro t
    have h1 : (fun x : ℝ => Complex.exp (t * x * I) * conj (k x)) =
        fun x : ℝ => conj (Complex.exp (-I * t * x) * k x) := by
      funext x
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp [map_mul, Complex.conj_ofReal]
      ring
    rw [h1, integral_conj, h t, map_zero]
  have hplain : ∀ t : ℝ, ∫ x : ℝ, Complex.exp (t * x * I) * k x = 0 := by
    intro t
    have := h (-t)
    rw [← this]
    congr 1; funext x; congr 2; push_cast; ring
  have hbound : ∀ (t : ℝ) (g : ℝ → ℂ), Integrable g →
      Integrable (fun x : ℝ => Complex.exp (t * x * I) * g x) := by
    intro t g hg
    refine hg.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun (x : ℝ) => ?_)
    rw [Complex.norm_exp]; simp
  have hkc : Integrable (fun x : ℝ => conj (k x)) :=
    hki.norm.mono' (Complex.continuous_conj.comp hk).aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
  have hre : (fun x => (k x).re) = 0 := by
    refine eq_zero_of_real_fourier_eq_zero (by fun_prop) hki.re fun t => ?_
    have heq : (fun x : ℝ => Complex.exp (t * x * I) * ((k x).re : ℂ)) =
        fun x : ℝ => (Complex.exp (t * x * I) * k x + Complex.exp (t * x * I) * conj (k x)) / 2 := by
      funext x; rw [Complex.re_eq_add_conj]; ring
    rw [heq, integral_div, integral_add (hbound t k hki) (hbound t _ hkc), hplain t, hconj t]
    simp
  have him : (fun x => (k x).im) = 0 := by
    refine eq_zero_of_real_fourier_eq_zero (by fun_prop) hki.im fun t => ?_
    have heq : (fun x : ℝ => Complex.exp (t * x * I) * ((k x).im : ℂ)) =
        fun x : ℝ => (Complex.exp (t * x * I) * k x - Complex.exp (t * x * I) * conj (k x)) /
          (2 * I) := by
      funext x; rw [Complex.im_eq_sub_conj]; ring
    rw [heq, integral_div, integral_sub (hbound t k hki) (hbound t _ hkc), hplain t, hconj t]
    simp
  funext x
  apply Complex.ext
  · exact congrFun hre x
  · exact congrFun him x

/-! ## Linearity of the source and the transform -/

section Linear

variable {F G : ℂ → ℂ}

theorem deriv_linear_comb (hF : DifferentiableOn ℂ F modUpperSet)
    (hG : DifferentiableOn ℂ G modUpperSet) (a b : ℂ) {p : ℂ} (hp : p ∈ modUpperSet) :
    deriv (fun τ => a * F τ + b * G τ) p = a * deriv F p + b * deriv G p := by
  have hn := isOpen_modUpperSet.mem_nhds hp
  have hFp := (hF p hp).differentiableAt hn
  have hGp := (hG p hp).differentiableAt hn
  exact ((hFp.hasDerivAt.const_mul a).add (hGp.hasDerivAt.const_mul b)).deriv

theorem deriv_deriv_linear_comb (hF : DifferentiableOn ℂ F modUpperSet)
    (hG : DifferentiableOn ℂ G modUpperSet) (a b : ℂ) {p : ℂ} (hp : p ∈ modUpperSet) :
    deriv (deriv (fun τ => a * F τ + b * G τ)) p =
      a * deriv (deriv F) p + b * deriv (deriv G) p := by
  have hev : deriv (fun τ => a * F τ + b * G τ) =ᶠ[𝓝 p]
      fun q => a * deriv F q + b * deriv G q := by
    filter_upwards [isOpen_modUpperSet.mem_nhds hp] with q hq
    exact deriv_linear_comb hF hG a b hq
  rw [hev.deriv_eq]
  have hn := isOpen_modUpperSet.mem_nhds hp
  have hF' := ((hF.deriv isOpen_modUpperSet) p hp).differentiableAt hn
  have hG' := ((hG.deriv isOpen_modUpperSet) p hp).differentiableAt hn
  exact ((hF'.hasDerivAt.const_mul a).add (hG'.hasDerivAt.const_mul b)).deriv

theorem modSource_linear_comb (hF : DifferentiableOn ℂ F modUpperSet)
    (hG : DifferentiableOn ℂ G modUpperSet) (a b : ℂ) (x : ℝ) :
    modSource (fun τ => a * F τ + b * G τ) x = a * modSource F x + b * modSource G x := by
  unfold modSource
  rw [deriv_linear_comb hF hG a b (modAxisPoint_mem x),
    deriv_deriv_linear_comb hF hG a b (modAxisPoint_mem x)]
  ring

variable {c : ℂ} {M : ℝ}

theorem integrable_modXiIntegrand (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im)) (w : ℂ) :
    Integrable (modXiIntegrand F w) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_modSource_le_exp (c := c) (M := M) hF hS hdec
    (B := |w.im| + 1) (by positivity)
  have hcont := continuous_modSource hF
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    (by unfold modXiIntegrand; fun_prop) (Eventually.of_forall fun x => ?_)
  rw [norm_modXiIntegrand]
  have hwx : w.im * x ≤ |w.im| * |x| := by
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
  calc Real.exp (w.im * x) * ‖modSource F x‖
      ≤ Real.exp (|w.im| * |x|) * (C * Real.exp (-((|w.im| + 1) * |x|))) :=
        mul_le_mul (Real.exp_le_exp.mpr hwx) (hC x) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-1 * |x|) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem integrable_modSource (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im)) :
    Integrable (modSource F) := by
  have := integrable_modXiIntegrand hF hS hdec 0
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [modXiIntegrand]

end Linear


/-! ## Recovering the form from a vanishing source -/

section Recovery

theorem tendsto_poly_mul_exp_neg_pi_exp (A B : ℝ) :
    Tendsto (fun x : ℝ => (A + B * Real.exp (2 * x)) * Real.exp (-π * Real.exp (2 * x)))
      atTop (𝓝 0) := by
  have hy : Tendsto (fun x : ℝ => Real.exp (2 * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos)
  have hπy : Tendsto (fun y : ℝ => π * y) atTop atTop := tendsto_id.const_mul_atTop Real.pi_pos
  have h0 : Tendsto (fun y : ℝ => Real.exp (-π * y)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hπy).congr fun y => ?_
    simp only [Function.comp_apply]; ring_nf
  have h1 : Tendsto (fun y : ℝ => y * Real.exp (-π * y)) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hπy).const_mul (1 / π)
    rw [mul_zero] at h
    refine h.congr fun y => ?_
    simp only [Function.comp_apply, pow_one]
    field_simp
  have hg : Tendsto (fun y : ℝ => (A + B * y) * Real.exp (-π * y)) atTop (𝓝 0) := by
    have h := (h0.const_mul A).add (h1.const_mul B)
    rw [mul_zero, mul_zero, add_zero] at h
    exact h.congr fun y => by ring
  exact hg.comp hy

variable {F : ℂ → ℂ} {M : ℝ}

theorem hasDerivAt_exp_neg_half_complex (x : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.exp (-x / 2) : ℂ)) (-(Real.exp (-x / 2) : ℂ) / 2) x := by
  have h := ((Real.hasDerivAt_exp (-x / 2)).comp x ((hasDerivAt_id x).neg.div_const 2)).ofReal_comp
  refine h.congr_deriv ?_
  push_cast; ring

theorem exp_neg_half_mul_exp_half (x : ℝ) :
    (Real.exp (-x / 2) : ℂ) * (Real.exp (x / 2) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, show -x / 2 + x / 2 = 0 by ring, Real.exp_zero,
    Complex.ofReal_one]

/-- **Recovery.**  If a cusp-decaying form with vanishing constant term has zero source, it
vanishes on the imaginary axis. -/
theorem modAxis_eq_zero_of_modSource_eq_zero (hF : DifferentiableOn ℂ F modUpperSet)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - 0‖ ≤ M * Real.exp (-π * τ.im))
    (hk : ∀ x, modSource F x = 0) (x : ℝ) : F (modAxisPoint x) = 0 := by
  have hM := cuspDecay_const_nonneg hdec
  have h2 : ∀ x, modTailDeriv2 F 0 x = modTail F 0 x / 4 := by
    intro x
    have := modSource_eq F 0 x
    rw [hk x] at this
    linear_combination -this
  set u : ℝ → ℂ := fun x => modTailDeriv F 0 x + modTail F 0 x / 2 with hudef
  have hu : ∀ x, HasDerivAt u (u x / 2) x := by
    intro x
    have h := (hasDerivAt_modTailDeriv 0 hF x).add ((hasDerivAt_modTail 0 hF x).div_const 2)
    refine h.congr_deriv ?_
    rw [hudef]; simp only; rw [h2 x]; ring
  set v : ℝ → ℂ := fun x => (Real.exp (-x / 2) : ℂ) * u x with hvdef
  have hv : ∀ x, HasDerivAt v 0 x := by
    intro x
    refine ((hasDerivAt_exp_neg_half_complex x).mul (hu x)).congr_deriv ?_
    ring
  have hvconst : ∀ x, v x = v 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hv y).differentiableAt) (fun y => (hv y).deriv) x 0
  have hvform : ∀ x, v x = F (modAxisPoint x) / 2 +
      modAxisPoint x * deriv F (modAxisPoint x) := by
    intro x
    rw [hvdef, hudef]
    simp only [modTailDeriv, modTail, sub_zero]
    have he := exp_neg_half_mul_exp_half x
    linear_combination (F (modAxisPoint x) / 2 + modAxisPoint x * deriv F (modAxisPoint x)) * he
  have hdec' : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; simpa using hdec τ hτ
  have hv0 : v 0 = 0 := by
    have hlim := tendsto_poly_mul_exp_neg_pi_exp (M / 2) (2 * M * Real.exp (π / 2))
    have hle : ∀ᶠ x in atTop, ‖v 0‖ ≤
        (M / 2 + 2 * M * Real.exp (π / 2) * Real.exp (2 * x)) *
          Real.exp (-π * Real.exp (2 * x)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [← hvconst x, hvform x]
      set y := Real.exp (2 * x) with hy
      have hy2 : 2 ≤ y := by
        have := Real.add_one_le_exp (2 * x); linarith
      have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
      have hF0 := hdec' (modAxisPoint x) (by rw [hpim]; linarith)
      have hF1 := norm_deriv_le_of_cuspDecay (c := 0) hF hdec (τ := modAxisPoint x)
        (by rw [hpim]; exact hy2)
      rw [hpim] at hF0 hF1
      calc ‖F (modAxisPoint x) / 2 + modAxisPoint x * deriv F (modAxisPoint x)‖
          ≤ ‖F (modAxisPoint x)‖ / 2 + y * ‖deriv F (modAxisPoint x)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_div, norm_mul, norm_modAxisPoint, ← hy]; norm_num
        _ ≤ M * Real.exp (-π * y) / 2 + y * (2 * M * Real.exp (π / 2) * Real.exp (-π * y)) := by
            gcongr
        _ = (M / 2 + 2 * M * Real.exp (π / 2) * y) * Real.exp (-π * y) := by ring
    have := ge_of_tendsto hlim hle
    exact norm_le_zero_iff.mp this
  have hu0 : ∀ x, u x = 0 := by
    intro x
    have h := hvconst x
    rw [hv0, hvdef] at h
    simp only at h
    have hne : (Real.exp (-x / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp h).resolve_left hne
  set w : ℝ → ℂ := fun x => (Real.exp (x / 2) : ℂ) * modTail F 0 x with hwdef
  have hw : ∀ x, HasDerivAt w 0 x := by
    intro x
    refine ((hasDerivAt_exp_half_complex x).mul (hasDerivAt_modTail 0 hF x)).congr_deriv ?_
    have := hu0 x
    rw [hudef] at this
    simp only at this
    linear_combination (Real.exp (x / 2) : ℂ) * this
  have hwconst : ∀ x, w x = w 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hw y).differentiableAt) (fun y => (hw y).deriv) x 0
  have hwform : ∀ x, w x = (Real.exp x : ℂ) * F (modAxisPoint x) / 2 := by
    intro x
    rw [hwdef]; simp only [modTail, sub_zero]
    have : (Real.exp (x / 2) : ℂ) * (Real.exp (x / 2) : ℂ) = (Real.exp x : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    linear_combination (F (modAxisPoint x) / 2) * this
  have hw0 : w 0 = 0 := by
    have hlim := tendsto_poly_mul_exp_neg_pi_exp 0 (M / 2)
    have hle : ∀ᶠ x in atTop, ‖w 0‖ ≤
        (0 + M / 2 * Real.exp (2 * x)) * Real.exp (-π * Real.exp (2 * x)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [← hwconst x, hwform x]
      set y := Real.exp (2 * x) with hy
      have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
      have hy1 : 1 ≤ y := by have := Real.add_one_le_exp (2 * x); linarith
      have hF0 := hdec' (modAxisPoint x) (by rw [hpim]; exact hy1)
      rw [hpim] at hF0
      have hexy : Real.exp x ≤ y := Real.exp_le_exp.mpr (by linarith)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        show ‖(2 : ℂ)‖ = 2 by norm_num, zero_add]
      calc Real.exp x * ‖F (modAxisPoint x)‖ / 2
          ≤ y * (M * Real.exp (-π * y)) / 2 := by gcongr
        _ = M / 2 * y * Real.exp (-π * y) := by ring
    have := ge_of_tendsto hlim hle
    exact norm_le_zero_iff.mp this
  have h := hwconst x
  rw [hw0, hwform x] at h
  have hne : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have : (Real.exp x : ℂ) * F (modAxisPoint x) = 0 := by linear_combination 2 * h
  exact (mul_eq_zero.mp this).resolve_left hne

end Recovery


/-! ## The theta-group countermodel family -/

section Countermodel

open Bottcher

theorem thetaGroupHauptmodul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaGroupHauptmodul τ ≠ 0 := by
  unfold thetaGroupHauptmodul
  have h2 := thetaTwo_ne_zero_of_im_pos hτ
  have h4 : thetaFour τ ≠ 0 := by
    rw [← thetaThree_add_one]; exact thetaThree_ne_zero_of_im_pos (by simpa using hτ)
  have h3 := thetaThree_ne_zero_of_im_pos hτ
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h4)) (pow_ne_zero _ h3)

/-- Transform of the source of the basis form `θ₃·h^j`. -/
def thetaGroupXi (j : ℕ) : ℂ → ℂ := modXi (thetaGroupBasis j)

theorem differentiable_thetaGroupXi (j : ℕ) : Differentiable ℂ (thetaGroupXi j) := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay j
  exact differentiable_modXi (c := thetaGroupBasisCusp j) (M := M)
    (differentiableOn_thetaGroupBasis j) (thetaGroupBasis_axis j) hM

theorem integrable_thetaGroupXiIntegrand (j : ℕ) (w : ℂ) :
    Integrable (modXiIntegrand (thetaGroupBasis j) w) := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay j
  exact integrable_modXiIntegrand (c := thetaGroupBasisCusp j) (M := M)
    (differentiableOn_thetaGroupBasis j) (thetaGroupBasis_axis j) hM w

theorem modXi_two_comb (a b : ℂ) {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F modUpperSet)
    (hG : DifferentiableOn ℂ G modUpperSet) (w : ℂ)
    (hFi : Integrable (modXiIntegrand F w)) (hGi : Integrable (modXiIntegrand G w)) :
    modXi (fun τ => a * F τ + b * G τ) w = a * modXi F w + b * modXi G w := by
  unfold modXi
  have heq : modXiIntegrand (fun τ => a * F τ + b * G τ) w =
      fun x => a * modXiIntegrand F w x + b * modXiIntegrand G w x := by
    funext x
    unfold modXiIntegrand
    rw [modSource_linear_comb hF hG a b]
    ring
  rw [heq, integral_add (hFi.const_mul a) (hGi.const_mul b), integral_const_mul,
    integral_const_mul]

theorem thetaGroupXi_independent (a b : ℝ)
    (h : ∀ w : ℂ, (a : ℂ) * thetaGroupXi 1 w + (b : ℂ) * thetaGroupXi 2 w = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨M₁, hM₁⟩ := thetaGroupBasis_cuspDecay 1
  obtain ⟨M₂, hM₂⟩ := thetaGroupBasis_cuspDecay 2
  have hc1 : thetaGroupBasisCusp 1 = 0 := by simp [thetaGroupBasisCusp]
  have hc2 : thetaGroupBasisCusp 2 = 0 := by simp [thetaGroupBasisCusp]
  set G : ℂ → ℂ := fun τ => (a : ℂ) * thetaGroupBasis 1 τ + (b : ℂ) * thetaGroupBasis 2 τ
    with hGdef
  have hG : DifferentiableOn ℂ G modUpperSet :=
    ((differentiableOn_thetaGroupBasis 1).const_mul _).add
      ((differentiableOn_thetaGroupBasis 2).const_mul _)
  have hGdec : ∀ τ : ℂ, 1 ≤ τ.im →
      ‖G τ - 0‖ ≤ (|a| * M₁ + |b| * M₂) * Real.exp (-π * τ.im) := by
    intro τ hτ
    have h1 := hM₁ τ hτ
    have h2 := hM₂ τ hτ
    rw [hc1, sub_zero] at h1
    rw [hc2, sub_zero] at h2
    rw [hGdef, sub_zero]
    calc ‖(a : ℂ) * thetaGroupBasis 1 τ + (b : ℂ) * thetaGroupBasis 2 τ‖
        ≤ |a| * ‖thetaGroupBasis 1 τ‖ + |b| * ‖thetaGroupBasis 2 τ‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ |a| * (M₁ * Real.exp (-π * τ.im)) + |b| * (M₂ * Real.exp (-π * τ.im)) := by
          gcongr
      _ = (|a| * M₁ + |b| * M₂) * Real.exp (-π * τ.im) := by ring
  have hXiG : ∀ w, modXi G w = 0 := by
    intro w
    rw [hGdef, modXi_two_comb _ _ (differentiableOn_thetaGroupBasis 1)
      (differentiableOn_thetaGroupBasis 2) w (integrable_thetaGroupXiIntegrand 1 w)
      (integrable_thetaGroupXiIntegrand 2 w)]
    exact h w
  have hGS : ∀ x : ℝ, G (modAxisPoint (-x)) = (Real.exp x : ℂ) * G (modAxisPoint x) := by
    intro x
    simp only [hGdef, thetaGroupBasis_axis]
    ring
  have hk : modSource G = 0 := by
    apply eq_zero_of_fourier_eq_zero (continuous_modSource hG)
      (integrable_modSource (c := 0) hG hGS hGdec)
    intro u
    exact hXiG u
  have hax : ∀ x, G (modAxisPoint x) = 0 :=
    modAxis_eq_zero_of_modSource_eq_zero hG hGdec (fun x => congrFun hk x)
  have hlin : ∀ x : ℝ, (a : ℂ) + (b : ℂ) * thetaGroupHauptmodul (modAxisPoint x) = 0 := by
    intro x
    have h0 := hax x
    simp only [hGdef, thetaGroupBasis] at h0
    have hθ := thetaThree_ne_zero_of_im_pos (modAxisPoint_mem x)
    have hh := thetaGroupHauptmodul_ne_zero (modAxisPoint_mem x)
    have hfac : thetaThree (modAxisPoint x) * thetaGroupHauptmodul (modAxisPoint x) *
        ((a : ℂ) + (b : ℂ) * thetaGroupHauptmodul (modAxisPoint x)) = 0 := by
      linear_combination h0
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd h1 (mul_ne_zero hθ hh)
    · exact h1
  have ha : a = 0 := by
    set Ch : ℝ := 4096 * thetaTwoCuspConstant ^ 4
    have hlim := tendsto_poly_mul_exp_neg_pi_exp (|b| * Ch) 0
    have hle : ∀ᶠ x in atTop, |a| ≤
        (|b| * Ch + 0 * Real.exp (2 * x)) * Real.exp (-π * Real.exp (2 * x)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hpim : (modAxisPoint x).im = Real.exp (2 * x) := modAxisPoint_im x
      have hy1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
      have hh := norm_thetaGroupHauptmodul_le (τ := modAxisPoint x) (by rw [hpim]; exact hy1)
      rw [hpim] at hh
      have hax' : (a : ℂ) = -((b : ℂ) * thetaGroupHauptmodul (modAxisPoint x)) := by
        linear_combination hlin x
      have hnorm : |a| = |b| * ‖thetaGroupHauptmodul (modAxisPoint x)‖ := by
        have := congrArg norm hax'
        rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs] at this
        exact this
      rw [hnorm, zero_mul, add_zero, mul_assoc]
      exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    have := ge_of_tendsto hlim hle
    exact abs_nonpos_iff.mp this
  refine ⟨ha, ?_⟩
  have h0 := hlin 0
  rw [ha] at h0
  simp only [Complex.ofReal_zero, zero_add] at h0
  have hh := thetaGroupHauptmodul_ne_zero (modAxisPoint_mem 0)
  have hb : (b : ℂ) = 0 := (mul_eq_zero.mp h0).resolve_right hh
  exact_mod_cast hb

/-- Cramer's rule over `ℝ` in `ℂ ≅ ℝ²`. -/
theorem exists_real_comb_eq {A B W : ℂ} (h : (A * conj B).im ≠ 0) :
    ∃ t₁ t₂ : ℝ, (t₁ : ℂ) * A + (t₂ : ℂ) * B = W := by
  have hd : (A * conj B).im = A.im * B.re - A.re * B.im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  have hd0 : A.im * B.re - A.re * B.im ≠ 0 := by rw [← hd]; exact h
  refine ⟨(W.im * B.re - W.re * B.im) / (A.im * B.re - A.re * B.im),
    (A.im * W.re - A.re * W.im) / (A.im * B.re - A.re * B.im), ?_⟩
  have hinv := mul_inv_cancel₀ hd0
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, div_eq_mul_inv]
    linear_combination W.re * hinv
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, div_eq_mul_inv]
    linear_combination W.im * hinv

/-- The strip `0 < im z < 1/2` contains a point where the two deformation transforms are
`ℝ`-independent. -/
theorem exists_strip_point_thetaGroupXi_independent :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ (thetaGroupXi 1 z * conj (thetaGroupXi 2 z)).im ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      (thetaGroupXi 1 z * conj (thetaGroupXi 2 z)).im = 0 := by
    intro z h1 h2
    by_contra hne
    exact hcon ⟨z, h1, h2, hne⟩
  set A := thetaGroupXi 1 with hAdef
  set B := thetaGroupXi 2 with hBdef
  have hA : AnalyticOnNhd ℂ A Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_thetaGroupXi 1)
  have hB : AnalyticOnNhd ℂ B Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_thetaGroupXi 2)
  set U : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < 1 / 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hmem : I / 4 ∈ U := by
    refine ⟨?_, ?_⟩
    · simp
    · simp; norm_num
  by_cases hBz : ∀ z ∈ U, B z = 0
  · have hBev : B =ᶠ[𝓝 (I / 4)] 0 := by
      filter_upwards [hUo.mem_nhds hmem] with z hz
      exact hBz z hz
    have hBzero := hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ _) hBev
    have := thetaGroupXi_independent 0 1 (fun w => by
      have := hBzero (Set.mem_univ w)
      simp only [Pi.zero_apply] at this
      rw [← hBdef, this]; simp)
    norm_num at this
  · rcases not_forall.mp hBz with ⟨z₁, hz⟩
    rcases Classical.not_imp.mp hz with ⟨hz₁U, hBz₁⟩
    set q : ℂ → ℂ := fun z => A z / B z with hqdef
    have hq : AnalyticAt ℂ q z₁ := (hA z₁ trivial).div (hB z₁ trivial) hBz₁
    have hBne : ∀ᶠ z in 𝓝 z₁, B z ≠ 0 := (hB z₁ trivial).continuousAt.eventually_ne hBz₁
    have hqreal : ∀ᶠ z in 𝓝 z₁, (q z).im = 0 := by
      filter_upwards [hUo.mem_nhds hz₁U, hBne] with z hzU hzB
      have h0 := hcon' z hzU.1 hzU.2
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
      have hns : Complex.normSq (B z) ≠ 0 := (Complex.normSq_pos.mpr hzB).ne'
      simp only [hqdef, Complex.div_im]
      field_simp
      linarith
    rcases hq.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · set r : ℝ := (q z₁).re with hr
      have hqr : q z₁ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hqreal.self_of_nhds])
      have hev : (fun z => A z - (r : ℂ) * B z) =ᶠ[𝓝 z₁] 0 := by
        filter_upwards [hconst, hBne] with z hz hzB
        have hz' : A z / B z = (r : ℂ) := hz.trans hqr
        rw [div_eq_iff hzB] at hz'
        simp only [Pi.zero_apply]
        rw [hz']
        ring
      have hAB : AnalyticOnNhd ℂ (fun z => A z - (r : ℂ) * B z) Set.univ :=
        hA.sub (fun z _ => analyticAt_const.mul (hB z trivial))
      have hzero := hAB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ z₁) hev
      have := thetaGroupXi_independent 1 (-r) (fun w => by
        have := hzero (Set.mem_univ w)
        simp only [Pi.zero_apply] at this
        rw [← hAdef, ← hBdef]
        push_cast
        linear_combination this)
      norm_num at this
    · have hR : {w : ℂ | w.im = 0} ∈ 𝓝 (q z₁) := hopen hqreal
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hR
      have hin : q z₁ + ((ε / 2 : ℝ) : ℂ) * I ∈ Metric.ball (q z₁) ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have h1 := hball hin
      simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at h1
      have h2 : (q z₁).im = 0 := hqreal.self_of_nhds
      linarith

/-- **Off-line strip zero in the theta-group family.**  Some real two-parameter deformation
`θ₃(1 + t₁h + t₂h²)` of the theta source has a transform zero with `0 < im z₀ < 1/2`. -/
theorem thetaGroup_offLine_strip_zero :
    ∃ t₁ t₂ : ℝ, ∃ z₀ : ℂ, 0 < z₀.im ∧ z₀.im < 1 / 2 ∧
      thetaGroupXi 0 z₀ + (t₁ : ℂ) * thetaGroupXi 1 z₀ + (t₂ : ℂ) * thetaGroupXi 2 z₀ = 0 := by
  obtain ⟨z₀, h1, h2, hind⟩ := exists_strip_point_thetaGroupXi_independent
  obtain ⟨t₁, t₂, ht⟩ := exists_real_comb_eq (W := -thetaGroupXi 0 z₀) hind
  exact ⟨t₁, t₂, z₀, h1, h2, by linear_combination ht⟩

end Countermodel

end

end RHTower
