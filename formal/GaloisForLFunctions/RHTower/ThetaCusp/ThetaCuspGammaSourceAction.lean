import GaloisForLFunctions.RHTower.ThetaSourcePrimeAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation

/-!
# The continuous Gamma action on the complete theta source

The subtraction stays inside the singular integral. A derivative bound supplies
its cancellation at zero; absolute scalar Fubini gives the digamma multiplier.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform
noncomputable section
namespace RHTower.ThetaSourceWard

lemma theta_shift_small (x : ℝ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    |thetaCuspFullSource (x+u)-thetaCuspFullSource x| ≤
      thetaCuspDerivativeExpConstant 1 * Real.exp 1 * Real.exp (-|x|) * u := by
  have hd : Differentiable ℝ thetaCuspFullSource :=
    contDiff_thetaCuspFullSource.differentiable (by norm_num)
  have hb : ∀ y ∈ Ico x (x+u), ‖deriv thetaCuspFullSource y‖ ≤
      thetaCuspDerivativeExpConstant 1 * Real.exp 1 * Real.exp (-|x|) := by
    intro y hy
    have hxy : |x| ≤ |y| + 1 := by
      have he : x = y + (x-y) := by ring
      have hnorm := abs_add_le y (x-y)
      have hneg : x-y ≤ 0 := sub_nonpos.mpr hy.1
      rw [abs_of_nonpos hneg] at hnorm
      rw [← he] at hnorm
      linarith [hy.2]
    have he : Real.exp (-|y|) ≤ Real.exp 1 * Real.exp (-|x|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 1 y
    simp only [iteratedDeriv_one] at h
    rw [Real.norm_eq_abs]
    exact h.trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left he (thetaCuspDerivativeExpConstant_nonneg 1))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y _ => (hd y).hasDerivAt.hasDerivWithinAt) hb
    (x+u) ⟨by linarith, le_rfl⟩
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using h

def gammaSourceTerm (x u : ℝ) : ℝ :=
  (Real.exp (-2*u)*thetaCuspFullSource x -
    Real.exp (-u/2)*thetaCuspFullSource (x+u)) / (1-Real.exp (-2*u))

def gammaNearConstant : ℝ :=
  Real.exp 2 / 2 *
    ((5/2 : ℝ)*thetaCuspDerivativeExpConstant 0 +
      thetaCuspDerivativeExpConstant 1 * Real.exp 1)

lemma gammaNearConstant_nonneg : 0 ≤ gammaNearConstant := by
  have h0 := thetaCuspDerivativeExpConstant_nonneg 0
  have h1 := thetaCuspDerivativeExpConstant_nonneg 1
  unfold gammaNearConstant
  positivity

lemma abs_gammaSourceTerm_le_small (x : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    |gammaSourceTerm x u| ≤ gammaNearConstant * Real.exp (-|x|) := by
  have h0 := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  simp only [iteratedDeriv_zero] at h0
  have h1 := theta_shift_small x hu.le hu1
  have hc0 := thetaCuspDerivativeExpConstant_nonneg 0
  have hc1 := thetaCuspDerivativeExpConstant_nonneg 1
  have hdiff : |Real.exp (-2*u)-Real.exp (-u/2)| ≤ (5/2:ℝ)*u := by
    have h := norm_exp_neg_sub_exp_neg_mul_le (s := (1/4:ℂ)) (by norm_num)
      (show 0 ≤ 2*u by positivity)
    have hA : -(↑(2*u):ℂ) = ((-2*u:ℝ):ℂ) := by push_cast; ring
    have hB : -(1/4:ℂ)*(↑(2*u):ℂ) = ((-u/2:ℝ):ℂ) := by push_cast; ring
    rw [hA,hB, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    norm_num at h
    simp only [neg_mul]
    linarith
  have he : Real.exp (-u/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hnum : |Real.exp (-2*u)*thetaCuspFullSource x -
      Real.exp (-u/2)*thetaCuspFullSource (x+u)| ≤
      ((5/2:ℝ)*thetaCuspDerivativeExpConstant 0 +
        thetaCuspDerivativeExpConstant 1 * Real.exp 1) * Real.exp (-|x|) * u := by
    calc
      _ = |(Real.exp (-2*u)-Real.exp (-u/2))*thetaCuspFullSource x +
        Real.exp (-u/2)*(thetaCuspFullSource x-thetaCuspFullSource (x+u))| := by congr 1; ring
      _ ≤ |Real.exp (-2*u)-Real.exp (-u/2)| *|thetaCuspFullSource x| +
        Real.exp (-u/2)*|thetaCuspFullSource (x+u)-thetaCuspFullSource x| := by
          simpa only [abs_mul, abs_of_pos (Real.exp_pos (-u/2)), abs_sub_comm] using
            abs_add_le ((Real.exp (-2*u)-Real.exp (-u/2))*thetaCuspFullSource x)
              (Real.exp (-u/2)*(thetaCuspFullSource x-thetaCuspFullSource (x+u)))
      _ ≤ ((5/2:ℝ)*u)*(thetaCuspDerivativeExpConstant 0*Real.exp (-|x|)) +
        1*(thetaCuspDerivativeExpConstant 1*Real.exp 1*Real.exp (-|x|)*u) := by gcongr
      _ = _ := by ring
  have hden : 2*u*Real.exp (-2) ≤ 1-Real.exp (-2*u) := by
    have h := exp_neg_le_one_sub_exp_neg_div (2*u)
    have he : Real.exp (-2:ℝ) ≤ Real.exp (-(2*u)) := Real.exp_le_exp.mpr (by linarith)
    simpa only [neg_mul] using
      (mul_le_mul_of_nonneg_left he (show 0 ≤ 2*u by positivity)).trans h
  have hdpos : 0 < 1-Real.exp (-2*u) := by
    have := one_sub_exp_neg_pos (show 0 < 2*u by positivity)
    simpa only [neg_mul] using this
  have hmul : Real.exp 2 * Real.exp (-2:ℝ) = 1 := by rw [← Real.exp_add]; norm_num
  rw [gammaSourceTerm, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  have h := mul_le_mul_of_nonneg_left hden
    (mul_nonneg gammaNearConstant_nonneg (Real.exp_pos (-|x|)).le)
  have heq : gammaNearConstant*Real.exp (-|x|)*(2*u*Real.exp (-2)) =
      ((5/2:ℝ)*thetaCuspDerivativeExpConstant 0 +
        thetaCuspDerivativeExpConstant 1*Real.exp 1)*Real.exp (-|x|)*u := by
    unfold gammaNearConstant
    linear_combination
      (((5/2:ℝ)*thetaCuspDerivativeExpConstant 0 +
        thetaCuspDerivativeExpConstant 1*Real.exp 1)*Real.exp (-|x|)*u) * hmul
  rw [heq] at h
  exact hnum.trans h

def gammaLaplaceTerm (w : ℂ) (u x : ℝ) : ℂ :=
  (gammaSourceTerm x u : ℂ)*Complex.exp (w*x)

lemma gammaLaplaceTerm_eq (w : ℂ) (u x : ℝ) :
    gammaLaplaceTerm w u x =
      ((Real.exp (-2*u):ℂ)*laplaceIntegrand thetaCuspTiltSource w x -
        Complex.exp (-(1/2+w)*u)*laplaceIntegrand thetaCuspTiltSource w (x+u)) /
          ((1-Real.exp (-2*u):ℝ):ℂ) := by
  have he : Complex.exp (-(1/2+w)*u)*Complex.exp (w*((x+u:ℝ):ℂ)) =
      (Real.exp (-u/2):ℂ)*Complex.exp (w*x) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold gammaLaplaceTerm gammaSourceTerm laplaceIntegrand
  rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_mul]
  simp only [thetaCuspTiltSource_k]
  calc
    _ = ((Real.exp (-2*u):ℂ)*(thetaCuspFullSource x:ℂ)*Complex.exp (w*x) -
        (thetaCuspFullSource (x+u):ℂ)*
          ((Real.exp (-u/2):ℂ)*Complex.exp (w*x))) /
        ((1-Real.exp (-2*u):ℝ):ℂ) := by ring
    _ = _ := by rw [← he]; ring

lemma integrable_gammaLaplaceTerm (w : ℂ) (u : ℝ) :
    Integrable (gammaLaplaceTerm w u) := by
  have h := (((integrable_laplaceIntegrand thetaCuspTiltSource w).const_mul
      (Real.exp (-2*u):ℂ)).sub
    (((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).const_mul
      (Complex.exp (-(1/2+w)*u)))).div_const ((1-Real.exp (-2*u):ℝ):ℂ)
  exact h.congr (Filter.Eventually.of_forall fun x => (gammaLaplaceTerm_eq w u x).symm)

lemma integral_gammaLaplaceTerm (w : ℂ) (u : ℝ) :
    (∫ x : ℝ, gammaLaplaceTerm w u x) =
      (((Real.exp (-2*u):ℂ)-Complex.exp (-(1/2+w)*u)) /
        ((1-Real.exp (-2*u):ℝ):ℂ)) * bilateralLaplace thetaCuspTiltSource w := by
  simp_rw [gammaLaplaceTerm_eq]
  rw [integral_div, integral_sub
    ((integrable_laplaceIntegrand thetaCuspTiltSource w).const_mul _)
    (((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).const_mul _),
    integral_const_mul, integral_const_mul, integral_add_right_eq_self]
  change (_ * bilateralLaplace thetaCuspTiltSource w -
    _ * bilateralLaplace thetaCuspTiltSource w) / _ = _
  ring

lemma norm_gammaLaplaceTerm (w : ℂ) (u x : ℝ) :
    ‖gammaLaplaceTerm w u x‖ = |gammaSourceTerm x u| *Real.exp (w.re*x) := by
  simp [gammaLaplaceTerm, Complex.norm_exp, Complex.mul_re]

lemma norm_gammaLaplaceTerm_le_small (w : ℂ) (x : ℝ) {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖gammaLaplaceTerm w u x‖ ≤
      gammaNearConstant*Real.exp (-(1-|w.re|)*|x|) := by
  rw [norm_gammaLaplaceTerm]
  have he : Real.exp (-|x|)*Real.exp (w.re*x) ≤
      Real.exp (-(1-|w.re|)*|x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := le_abs_self (w.re*x)
    rw [abs_mul] at h
    nlinarith
  calc
    _ ≤ gammaNearConstant*Real.exp (-|x|)*Real.exp (w.re*x) :=
      mul_le_mul_of_nonneg_right (abs_gammaSourceTerm_le_small x hu hu1)
        (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left he gammaNearConstant_nonneg

lemma gammaLaplaceTerm_measurable (w : ℂ) :
    Measurable (fun p : ℝ × ℝ => gammaLaplaceTerm w p.1 p.2) := by
  have hc := contDiff_thetaCuspFullSource.continuous
  unfold gammaLaplaceTerm gammaSourceTerm
  fun_prop

lemma integral_norm_gammaLaplaceTerm_le_large (w : ℂ) {u : ℝ} (hu : 1 ≤ u) :
    (∫ x : ℝ, ‖gammaLaplaceTerm w u x‖) ≤
      (Real.exp (-2*u)+Real.exp (-(1/2+w.re)*u))/(1-Real.exp (-2:ℝ)) *
        ∫ x : ℝ, ‖laplaceIntegrand thetaCuspTiltSource w x‖ := by
  have hd : 0 < 1-Real.exp (-2:ℝ) := by
    have := Real.exp_lt_one_iff.mpr (show (-2:ℝ)<0 by norm_num)
    linarith
  have hden : 1-Real.exp (-2:ℝ) ≤ 1-Real.exp (-2*u) := by
    have := Real.exp_le_exp.mpr (show -2*u ≤ (-2:ℝ) by linarith)
    linarith
  have hdu : 0 < 1-Real.exp (-2*u) := hd.trans_le hden
  have hb : ‖Complex.exp (-(1/2+w)*(u:ℂ))‖ = Real.exp (-(1/2+w.re)*u) := by
    simp [Complex.norm_exp, Complex.mul_re]
  let f := fun x : ℝ =>
    (Real.exp (-2*u)*‖laplaceIntegrand thetaCuspTiltSource w x‖ +
      Real.exp (-(1/2+w.re)*u)*‖laplaceIntegrand thetaCuspTiltSource w (x+u)‖) /
        (1-Real.exp (-2:ℝ))
  have hfi : Integrable f :=
    (((integrable_laplaceIntegrand thetaCuspTiltSource w).norm.const_mul _).add
      (((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).norm.const_mul _)).div_const _
  have hle (x : ℝ) : ‖gammaLaplaceTerm w u x‖ ≤ f x := by
    rw [gammaLaplaceTerm_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdu]
    calc
      _ ≤ (‖(Real.exp (-2*u):ℂ)*laplaceIntegrand thetaCuspTiltSource w x‖ +
          ‖Complex.exp (-(1/2+w)*u)*laplaceIntegrand thetaCuspTiltSource w (x+u)‖) /
          (1-Real.exp (-2*u)) :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) hdu.le
      _ = (Real.exp (-2*u)*‖laplaceIntegrand thetaCuspTiltSource w x‖ +
          Real.exp (-(1/2+w.re)*u)*‖laplaceIntegrand thetaCuspTiltSource w (x+u)‖) /
          (1-Real.exp (-2*u)) := by
        rw [norm_mul,norm_mul,hb,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ f x := div_le_div_of_nonneg_left (by positivity) hd hden
  refine (integral_mono (integrable_gammaLaplaceTerm w u).norm hfi hle).trans_eq ?_
  dsimp [f]
  rw [integral_div, integral_add
    ((integrable_laplaceIntegrand thetaCuspTiltSource w).norm.const_mul _)
    (((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).norm.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun x : ℝ => ‖laplaceIntegrand thetaCuspTiltSource w x‖) u]
  ring

lemma gammaLaplaceTerm_integrable_prod {w : ℂ}
    (hw0 : -1/2 < w.re) (hw1 : |w.re| < 1) :
    Integrable (fun p : ℝ × ℝ => gammaLaplaceTerm w p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hm := (gammaLaplaceTerm_measurable w).aestronglyMeasurable
    (μ := (volume.restrict (Ioi (0:ℝ))).prod volume)
  rw [integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall (integrable_gammaLaplaceTerm w), ?_⟩
  have hr : 0 < 1-|w.re| := by linarith
  have hex : Integrable (fun x : ℝ => Real.exp (-(1-|w.re|)*|x|)) := by
    simpa only [pow_zero,one_mul] using HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hr
  have hsmall : IntegrableOn (fun u : ℝ => ∫ x : ℝ, ‖gammaLaplaceTerm w u x‖) (Ioc 0 1) := by
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => ∫ x : ℝ, ‖gammaLaplaceTerm w u x‖) (volume.restrict (Ioc 0 1)) :=
      ((gammaLaplaceTerm_measurable w).aestronglyMeasurable.norm.integral_prod_right')
    apply (integrable_const (gammaNearConstant *
      ∫ x : ℝ, Real.exp (-(1-|w.re|)*|x|))).mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    have h := integral_mono (integrable_gammaLaplaceTerm w u).norm
      (hex.const_mul gammaNearConstant) (fun x => norm_gammaLaplaceTerm_le_small w x hu.1 hu.2)
    rwa [integral_const_mul] at h
  have hlarge : IntegrableOn (fun u : ℝ => ∫ x : ℝ, ‖gammaLaplaceTerm w u x‖) (Ioi 1) := by
    have hbound : IntegrableOn (fun u : ℝ =>
        (Real.exp (-2*u)+Real.exp (-(1/2+w.re)*u))/(1-Real.exp (-2:ℝ)) *
          ∫ x : ℝ, ‖laplaceIntegrand thetaCuspTiltSource w x‖) (Ioi 1) :=
      (((integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 1).add
        (integrableOn_exp_mul_Ioi (a := -(1/2+w.re)) (by linarith) 1)).div_const _).mul_const _
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => ∫ x : ℝ, ‖gammaLaplaceTerm w u x‖) (volume.restrict (Ioi 1)) :=
      ((gammaLaplaceTerm_measurable w).aestronglyMeasurable.norm.integral_prod_right')
    apply hbound.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact integral_norm_gammaLaplaceTerm_le_large w hu.le
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hu : u ≤ 1
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr (lt_of_not_ge hu)
  rw [← hunion]
  exact integrableOn_union.mpr ⟨hsmall,hlarge⟩

lemma gammaLaplaceScalar_eq (w : ℂ) (u : ℝ) :
    (((Real.exp (-2*u):ℂ)-Complex.exp (-(1/2+w)*u)) /
      ((1-Real.exp (-2*u):ℝ):ℂ)) = gaussLaplaceKernel ((1/2+w)/2) (2*u) := by
  unfold gaussLaplaceKernel
  have ha : -(↑(2*u):ℂ) = ((-2*u:ℝ):ℂ) := by push_cast; ring
  have hb : -((1/2+w)/2)*(↑(2*u):ℂ) = -(1/2+w)*u := by push_cast; ring
  rw [ha,hb,← Complex.ofReal_exp,Complex.ofReal_sub,Complex.ofReal_one]

lemma gammaLaplaceTerm_integral_swap {w : ℂ}
    (hw0 : -1/2 < w.re) (hw1 : |w.re| < 1) :
    (∫ x : ℝ, ∫ u in Ioi (0:ℝ), gammaLaplaceTerm w u x) =
      ((∫ t in Ioi (0:ℝ), gaussLaplaceKernel ((1/2+w)/2) t)/2) *
        bilateralLaplace thetaCuspTiltSource w := by
  rw [← integral_integral_swap (gammaLaplaceTerm_integrable_prod hw0 hw1)]
  simp_rw [integral_gammaLaplaceTerm,gammaLaplaceScalar_eq]
  rw [integral_mul_const,integral_comp_mul_left_Ioi _ 0 (by norm_num : (0:ℝ)<2)]
  simp only [mul_zero,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

lemma abs_theta_le_const (x : ℝ) : |thetaCuspFullSource x| ≤ thetaCuspDerivativeExpConstant 0 := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 x
  simp only [iteratedDeriv_zero] at h
  have he : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  exact h.trans (by simpa using
    mul_le_mul_of_nonneg_left he (thetaCuspDerivativeExpConstant_nonneg 0))

def gammaSourceBound (u : ℝ) : ℝ :=
  gammaNearConstant * Real.exp 1 * Real.exp (-u) +
    thetaCuspDerivativeExpConstant 0 / (1-Real.exp (-2:ℝ)) *
      (Real.exp (-2*u)+Real.exp (-u/2))

lemma gammaSourceBound_integrable : IntegrableOn gammaSourceBound (Ioi (0:ℝ)) := by
  change Integrable (fun u : ℝ =>
    gammaNearConstant * Real.exp 1 * Real.exp (-u) +
      thetaCuspDerivativeExpConstant 0 / (1-Real.exp (-2:ℝ)) *
        (Real.exp (-2*u)+Real.exp (-u/2))) (volume.restrict (Ioi 0))
  have h1 := (integrableOn_exp_neg_Ioi 0).const_mul (gammaNearConstant*Real.exp 1)
  have h2 := ((integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 0).fun_add
    (integrableOn_exp_mul_Ioi (a := -1/2) (by norm_num) 0)).const_mul
      (thetaCuspDerivativeExpConstant 0/(1-Real.exp (-2:ℝ)))
  simpa only [gammaSourceBound, Pi.add_apply, neg_div, neg_mul, one_mul, div_mul_eq_mul_div] using h1.fun_add h2

lemma abs_gammaSourceTerm_le_bound (x : ℝ) {u : ℝ} (hu : 0 < u) :
    |gammaSourceTerm x u| ≤ gammaSourceBound u := by
  have hc := thetaCuspDerivativeExpConstant_nonneg 0
  have hg := gammaNearConstant_nonneg
  have hd : 0 < 1-Real.exp (-2:ℝ) := by
    have := Real.exp_lt_one_iff.mpr (show (-2:ℝ)<0 by norm_num)
    linarith
  by_cases hu1 : u ≤ 1
  · have he : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      linarith
    have hx : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
    have h := (abs_gammaSourceTerm_le_small x hu hu1).trans
      (mul_le_mul_of_nonneg_left hx hg)
    have hb := mul_le_mul_of_nonneg_left he hg
    have hp : 0 ≤ thetaCuspDerivativeExpConstant 0 / (1-Real.exp (-2:ℝ)) *
        (Real.exp (-2*u)+Real.exp (-u/2)) := by positivity
    unfold gammaSourceBound
    nlinarith
  · have hden : 1-Real.exp (-2:ℝ) ≤ 1-Real.exp (-2*u) := by
      have := Real.exp_le_exp.mpr (show -2*u ≤ (-2:ℝ) by linarith)
      linarith
    have hdu := hd.trans_le hden
    rw [gammaSourceTerm,abs_div,abs_of_pos hdu]
    have hn : |Real.exp (-2*u)*thetaCuspFullSource x -
        Real.exp (-u/2)*thetaCuspFullSource (x+u)| ≤
        Real.exp (-2*u)*thetaCuspDerivativeExpConstant 0 +
          Real.exp (-u/2)*thetaCuspDerivativeExpConstant 0 := by
      have ht := norm_sub_le (Real.exp (-2*u)*thetaCuspFullSource x)
        (Real.exp (-u/2)*thetaCuspFullSource (x+u))
      simp only [Real.norm_eq_abs] at ht
      refine ht.trans ?_
      rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_theta_le_const x) (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left (abs_theta_le_const (x+u)) (Real.exp_pos _).le)
    calc
      _ ≤ (Real.exp (-2*u)*thetaCuspDerivativeExpConstant 0 +
          Real.exp (-u/2)*thetaCuspDerivativeExpConstant 0)/(1-Real.exp (-2*u)) :=
        div_le_div_of_nonneg_right hn hdu.le
      _ ≤ (Real.exp (-2*u)*thetaCuspDerivativeExpConstant 0 +
          Real.exp (-u/2)*thetaCuspDerivativeExpConstant 0)/(1-Real.exp (-2:ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hd hden
      _ ≤ gammaSourceBound u := by
        unfold gammaSourceBound
        have hp : 0 ≤ gammaNearConstant*Real.exp 1*Real.exp (-u) := by positivity
        have heq : (Real.exp (-2*u)*thetaCuspDerivativeExpConstant 0 +
            Real.exp (-u/2)*thetaCuspDerivativeExpConstant 0)/(1-Real.exp (-2:ℝ)) =
            thetaCuspDerivativeExpConstant 0/(1-Real.exp (-2:ℝ))*
              (Real.exp (-2*u)+Real.exp (-u/2)) := by ring
        rw [heq]
        exact le_add_of_nonneg_left hp

lemma gammaSourceTerm_measurable (x : ℝ) :
    Measurable (fun u : ℝ => (gammaSourceTerm x u:ℂ)) := by
  have hc := contDiff_thetaCuspFullSource.continuous
  unfold gammaSourceTerm
  fun_prop

lemma gammaSourceTerm_continuous (u : ℝ) :
    Continuous (fun x : ℝ => (gammaSourceTerm x u:ℂ)) := by
  have hc := contDiff_thetaCuspFullSource.continuous
  unfold gammaSourceTerm
  fun_prop

lemma gammaSourceTerm_integrable (x : ℝ) :
    IntegrableOn (fun u : ℝ => (gammaSourceTerm x u:ℂ)) (Ioi 0) := by
  apply gammaSourceBound_integrable.mono' (gammaSourceTerm_measurable x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_gammaSourceTerm_le_bound x hu

def gammaSource (x : ℝ) : ℂ := ∫ u in Ioi (0:ℝ), (gammaSourceTerm x u:ℂ)

lemma gammaSource_continuous : Continuous gammaSource := by
  apply continuous_of_dominated (bound := gammaSourceBound)
    (fun x => (gammaSourceTerm_measurable x).aestronglyMeasurable)
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_gammaSourceTerm_le_bound x hu
  · exact gammaSourceBound_integrable
  · exact Filter.Eventually.of_forall gammaSourceTerm_continuous

lemma gammaSource_laplace_integrable {w : ℂ}
    (hw0 : -1/2 < w.re) (hw1 : |w.re| < 1) :
    Integrable (fun x : ℝ => gammaSource x*Complex.exp (w*x)) := by
  have h := (gammaLaplaceTerm_integrable_prod hw0 hw1).integral_prod_right
  apply h.congr
  filter_upwards with x
  exact integral_mul_const _ _

lemma integral_gammaSource_laplace {w : ℂ}
    (hw0 : -1/2 < w.re) (hw1 : |w.re| < 1) :
    (∫ x : ℝ, gammaSource x*Complex.exp (w*x)) =
      ((∫ t in Ioi (0:ℝ), gaussLaplaceKernel ((1/2+w)/2) t)/2) *
        bilateralLaplace thetaCuspTiltSource w := by
  rw [← gammaLaplaceTerm_integral_swap hw0 hw1]
  apply integral_congr_ae
  filter_upwards with x
  exact (integral_mul_const _ _).symm

end RHTower.ThetaSourceWard
