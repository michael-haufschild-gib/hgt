import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerBoundaryEulerSource
import GaloisForLFunctions.RHTower.ThetaTailIntegralCalculus

/-!
# Causal division in the literal all-weight Meyer target

A vanishing Mellin moment admits a unique rapidly decreasing solution of
`(-d/dt - rho) u = g`.  The right tail integral equals the negative left tail;
this preserves every exponential weight.  Its differential equation then
preserves every derivative.  Thus division by a spectral linear factor takes
place in the actual source space, before any entire-function quotient.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics

namespace RHTower
noncomputable section

/-- Right causal primitive of a logarithmic source. -/
def deningerMeyerCausalDivision (rho : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(rho * x)) * ∫ t in Ioi x, Complex.exp (rho * t) * g t

private theorem integrable_exp_mul_strongLog {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (rho * t) * g t) := by
  have h := integrable_deningerMeyerStrongLogMellinJet hg 0 rho
  change Integrable (fun t : ℝ => (t : ℂ)^0 * Complex.exp (rho * t) * g t) at h
  simpa only [pow_zero, one_mul] using h

theorem hasDerivAt_deningerMeyerCausalDivision {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) (x : ℝ) :
    HasDerivAt (deningerMeyerCausalDivision rho g)
      (-rho * deningerMeyerCausalDivision rho g x - g x) x := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (rho * t) * g t) := by
    have := hg.smooth.continuous
    fun_prop
  have htail := hasDerivAt_setIntegral_Ioi (integrable_exp_mul_strongLog hg rho) hcont x
  have he : HasDerivAt (fun t : ℝ => Complex.exp (-(rho * t)))
      (-rho * Complex.exp (-(rho * x))) x := by
    have hlin : HasDerivAt (fun t : ℝ => -(rho * (t : ℂ))) (-rho) x := by
      simpa only [neg_mul, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
        (Complex.ofRealCLM.hasDerivAt.const_mul (-rho) (x := x))
    exact hlin.cexp.congr_deriv (by ring)
  refine (he.mul htail).congr_deriv ?_
  have hcancel : Complex.exp (-(rho * x)) * Complex.exp (rho * x) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  dsimp only [deningerMeyerCausalDivision]
  linear_combination -(g x) * hcancel

theorem deriv_deningerMeyerCausalDivision {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) :
    deriv (deningerMeyerCausalDivision rho g) =
      (-rho) • deningerMeyerCausalDivision rho g - g := by
  funext x
  exact (hasDerivAt_deningerMeyerCausalDivision hg rho x).deriv

theorem contDiff_deningerMeyerCausalDivision {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerMeyerCausalDivision rho g) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (rho * t) * g t) := by
    have := hg.smooth.continuous
    fun_prop
  have hexp (a : ℂ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => Complex.exp (a * (x : ℂ))) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => a * (x : ℂ)) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp hlin
  have htail : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => ∫ t in Ioi x, Complex.exp (rho * t) * g t) := by
    refine contDiff_infty_iff_deriv.mpr ⟨fun x =>
      (hasDerivAt_setIntegral_Ioi (integrable_exp_mul_strongLog hg rho) hcont x).differentiableAt, ?_⟩
    have hd : deriv (fun x : ℝ => ∫ t in Ioi x, Complex.exp (rho * t) * g t) =
        fun x : ℝ => -(Complex.exp (rho * x) * g x) := by
      funext x
      exact (hasDerivAt_setIntegral_Ioi (integrable_exp_mul_strongLog hg rho) hcont x).deriv
    rw [hd]
    exact ((hexp rho).mul hg.smooth).neg
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ℝ => Complex.exp (-(rho * (x : ℂ))) *
      ∫ t in Ioi x, Complex.exp (rho * t) * g t)
  simpa only [neg_mul] using (hexp (-rho)).mul htail

theorem deningerMeyerCausalDivision_eq_left {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) (x : ℝ) :
    deningerMeyerCausalDivision rho g x =
      -(Complex.exp (-(rho * x)) * ∫ t in Iic x, Complex.exp (rho * t) * g t) := by
  have h := integral_add_compl (measurableSet_Iic (a := x))
    (integrable_exp_mul_strongLog hg rho)
  have hz' : (∫ t : ℝ, Complex.exp (rho * t) * g t) = 0 := by
    simpa only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
      pow_zero, one_mul] using hz
  rw [compl_Iic, hz'] at h
  dsimp only [deningerMeyerCausalDivision]
  linear_combination Complex.exp (-(rho * x)) * h

private theorem causalDivision_right_bound {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) {a : ℝ} (ha : rho.re ≤ a)
    (x : ℝ) :
    ‖deningerMeyerCausalDivision rho g x‖ ≤
      Real.exp (-(a * x)) * ∫ t : ℝ, ‖Complex.exp ((a : ℂ) * t) * g t‖ := by
  have hi := (integrable_exp_mul_strongLog hg (a : ℂ)).norm
  rw [deningerMeyerCausalDivision, ← integral_const_mul]
  calc
    _ ≤ ∫ t in Ioi x, Real.exp (-(a * x)) *
        ‖Complex.exp ((a : ℂ) * t) * g t‖ := by
      apply norm_integral_le_of_norm_le (hi.integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← mul_assoc, ← Complex.exp_add, norm_mul, norm_mul,
        Complex.norm_exp, Complex.norm_exp, Complex.re_mul_ofReal,
        Complex.ofReal_re]
      have hr : (-(rho * (x : ℂ)) + rho * t).re = rho.re * (t - x) := by
        simp only [Complex.add_re, Complex.neg_re, Complex.re_mul_ofReal]
        ring
      rw [hr, ← mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (by have ht' : x < t := ht; nlinarith)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hi (Eventually.of_forall fun _ => norm_nonneg _))
        (Real.exp_pos _).le

private theorem causalDivision_left_bound {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0)
    {a : ℝ} (ha : a ≤ rho.re) (x : ℝ) :
    ‖deningerMeyerCausalDivision rho g x‖ ≤
      Real.exp (-(a * x)) * ∫ t : ℝ, ‖Complex.exp ((a : ℂ) * t) * g t‖ := by
  have hi := (integrable_exp_mul_strongLog hg (a : ℂ)).norm
  rw [deningerMeyerCausalDivision_eq_left hg rho hz, norm_neg, ← integral_const_mul]
  calc
    _ ≤ ∫ t in Iic x, Real.exp (-(a * x)) *
        ‖Complex.exp ((a : ℂ) * t) * g t‖ := by
      apply norm_integral_le_of_norm_le (hi.integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      rw [← mul_assoc, ← Complex.exp_add, norm_mul, norm_mul,
        Complex.norm_exp, Complex.norm_exp, Complex.re_mul_ofReal,
        Complex.ofReal_re]
      have hr : (-(rho * (x : ℂ)) + rho * t).re = rho.re * (t - x) := by
        simp only [Complex.add_re, Complex.neg_re, Complex.re_mul_ofReal]
        ring
      rw [hr, ← mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (by have ht' : t ≤ x := ht; nlinarith)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hi (Eventually.of_forall fun _ => norm_nonneg _))
        (Real.exp_pos _).le

private theorem causalDivision_decay_top {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ) (a : ℝ) :
    deningerMeyerCausalDivision rho g =O[atTop] fun t : ℝ => Real.exp t ^ (-a) := by
  let b := max rho.re a
  let C := ∫ t : ℝ, ‖Complex.exp ((b : ℂ) * t) * g t‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h := causalDivision_right_bound hg rho (a := b) (le_max_left rho.re a) x
  have hb : a ≤ b := le_max_right _ _
  have he : Real.exp (-(b*x)) ≤ Real.exp x ^ (-a) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos x) _)]
  change ‖deningerMeyerCausalDivision rho g x‖ ≤ Real.exp (-(b*x)) * C at h
  exact h.trans (by nlinarith)

private theorem causalDivision_decay_bot {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) (a : ℝ) :
    deningerMeyerCausalDivision rho g =O[atBot] fun t : ℝ => Real.exp t ^ a := by
  let b := min rho.re (-a)
  let C := ∫ t : ℝ, ‖Complex.exp ((b : ℂ) * t) * g t‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  apply IsBigO.of_bound C
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  have h := causalDivision_left_bound hg rho hz (a := b) (min_le_left rho.re (-a)) x
  have hb : b ≤ -a := min_le_right _ _
  have he : Real.exp (-(b*x)) ≤ Real.exp x ^ a := by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos x) _)]
  change ‖deningerMeyerCausalDivision rho g x‖ ≤ Real.exp (-(b*x)) * C at h
  exact h.trans (by nlinarith)

/-- Causal zero division preserves the full Meyer space, including every derivative. -/
theorem deningerMeyerCausalDivision_strongLogDecay {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) :
    DeningerMeyerStrongLogDecay (deningerMeyerCausalDivision rho g) := by
  have hs := contDiff_deningerMeyerCausalDivision hg rho
  have hrec (n : ℕ) :
      iteratedDeriv (n+1) (deningerMeyerCausalDivision rho g) =
        (-rho) • iteratedDeriv n (deningerMeyerCausalDivision rho g) - iteratedDeriv n g := by
    funext x
    rw [iteratedDeriv_succ', deriv_deningerMeyerCausalDivision hg rho]
    have hsm : ContDiff ℝ (⊤ : ℕ∞) ((-rho) • deningerMeyerCausalDivision rho g) :=
      hs.const_smul (-rho)
    rw [iteratedDeriv_sub (hsm.contDiffAt.of_le (mod_cast le_top))
      (hg.smooth.contDiffAt.of_le (mod_cast le_top))]
    simp only [iteratedDeriv_const_smul_field, Pi.sub_apply, Pi.smul_apply]
  refine ⟨hs, ?_, ?_⟩
  · intro n a
    induction n with
    | zero => exact causalDivision_decay_top hg rho a
    | succ n ih =>
        rw [hrec]
        exact (ih.const_smul_left (-rho)).sub (hg.decayTop n a)
  · intro n a
    induction n with
    | zero => exact causalDivision_decay_bot hg rho hz a
    | succ n ih =>
        rw [hrec]
        exact (ih.const_smul_left (-rho)).sub (hg.decayBot n a)

/-- Actual all-weight source obtained by division at one vanishing Mellin moment. -/
def deningerMeyerCausalDivide (g : DeningerMeyerStrongLogTarget) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) : DeningerMeyerStrongLogTarget :=
  ⟨deningerMeyerCausalDivision rho g, deningerMeyerCausalDivision_strongLogDecay g.property rho hz⟩

/-- Negative logarithmic differentiation on the actual all-weight target. -/
def deningerMeyerStrongLogGenerator : Module.End ℂ DeningerMeyerStrongLogTarget where
  toFun g := ⟨-deriv (g : ℝ → ℂ), g.property.deriv.neg⟩
  map_add' g h := by
    apply Subtype.ext
    funext x
    change -deriv ((g : ℝ → ℂ) + (h : ℝ → ℂ)) x =
      -deriv (g : ℝ → ℂ) x + -deriv (h : ℝ → ℂ) x
    rw [deriv_add (g.property.smooth.differentiable (by simp) x)
      (h.property.smooth.differentiable (by simp) x)]
    ring
  map_smul' c g := by
    apply Subtype.ext
    funext x
    change -deriv (c • (g : ℝ → ℂ)) x = c • -deriv (g : ℝ → ℂ) x
    rw [deriv_const_smul c (g.property.smooth.differentiable (by simp) x)]
    simp

theorem deningerMeyerStrongLogGenerator_causalDivide
    (g : DeningerMeyerStrongLogTarget) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) :
    deningerMeyerStrongLogGenerator (deningerMeyerCausalDivide g rho hz) =
      rho • deningerMeyerCausalDivide g rho hz + g := by
  apply Subtype.ext
  change -deriv (deningerMeyerCausalDivision rho g) =
    rho • deningerMeyerCausalDivision rho g + g
  rw [deriv_deningerMeyerCausalDivision g.property rho]
  module

theorem deningerMeyerStrongLogGenerator_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) s =
      s * deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellinLM s (-⟨deriv g, g.property.deriv⟩) = _
  rw [map_neg]
  change -deningerMeyerStrongLogMellin (deriv g) s = _
  rw [deningerMeyerStrongLogMellin_deriv g.property]
  ring

/-- Division is realized by the actual causal source on the entire spectral plane. -/
theorem deningerMeyerCausalDivide_mellin
    (g : DeningerMeyerStrongLogTarget) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) (s : ℂ) :
    (s-rho) * deningerMeyerStrongLogMellin (deningerMeyerCausalDivide g rho hz) s =
      deningerMeyerStrongLogMellin g s := by
  have h := congrArg (fun v => deningerMeyerStrongLogMellinLM s v)
    (deningerMeyerStrongLogGenerator_causalDivide g rho hz)
  rw [map_add, map_smul] at h
  change deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator _) s =
    rho * deningerMeyerStrongLogMellin _ s + deningerMeyerStrongLogMellin g s at h
  rw [deningerMeyerStrongLogGenerator_mellin] at h
  linear_combination h

end
end RHTower
