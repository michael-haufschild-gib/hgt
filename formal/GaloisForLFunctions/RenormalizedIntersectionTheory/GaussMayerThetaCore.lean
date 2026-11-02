import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerThetaProduct
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCore

/-! The scattering-subtracted Epstein–Mayer core is the actual Gaussian-ray
correlation. Five convergent source Mellins and the concrete theta functional
equation continue this identity without dividing by the zeta function. -/

open Complex Set Filter MeasureTheory HurwitzZeta
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaCore
open MayerThetaRay MayerThetaProduct MayerScatteringCore

private def thetaDefect (t : ℝ) : ℂ := (thetaSum t : ℂ)-1

private theorem thetaDefect_hasMellin {u : ℂ} (hu : 1/2 < u.re) :
    HasMellin thetaDefect u (2*completedRiemannZeta (2*u)) := by
  have h : HasMellin (fun t => (evenKernel 0 t : ℂ)-1) u ((hurwitzEvenFEPair 0).Λ u) := by
    simpa only [hurwitzEvenFEPair,Function.comp_def,ite_true] using!
      (hurwitzEvenFEPair 0).hasMellin hu
  have he : (hurwitzEvenFEPair 0).Λ u=2*completedRiemannZeta (2*u) := by
    rw [completedRiemannZeta,completedHurwitzZetaEven,show 2*u/2=u by ring]
    ring
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun h.1
      (fun t ht => by simp only [thetaDefect,thetaSum_eq_evenKernel ht]) measurableSet_Ioi
  · calc
      mellin thetaDefect u=mellin (fun t => (evenKernel 0 t : ℂ)-1) u := by
        unfold mellin
        exact setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => by simp only [thetaDefect,thetaSum_eq_evenKernel ht])
      _ = _ := h.2.trans he

private theorem square_cpow {a : ℝ} (ha : 0 < a) (u : ℂ) :
    ((a^2 : ℝ) : ℂ)^(-u)=(a : ℂ)^(-2*u) := by
  rw [pow_two,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le ha.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  congr 1
  ring

private theorem scaledTheta_hasMellin {a : ℝ} (ha : 0 < a) {u : ℂ} (hu : 1/2 < u.re) :
    HasMellin (fun t => thetaDefect (a^2*t)) u
      ((a : ℂ)^(-2*u)*(2*completedRiemannZeta (2*u))) := by
  have h := thetaDefect_hasMellin hu
  constructor
  · exact (MellinConvergent.comp_mul_left (sq_pos_of_pos ha)).mpr h.1
  · rw [mellin_comp_mul_left thetaDefect u (sq_pos_of_pos ha),h.2,square_cpow ha,smul_eq_mul]

/-- The five source Mellins determining the continued theta correlation. -/
def sourceExpression (a : ℝ) (ha : 0 < a) (u : ℂ) : ℂ :=
  epsteinLambda a ha u/4-
    completedRiemannZeta (2*u)*(1+(a : ℂ)^(-2*u))/2-
    completedRiemannZeta (2*u-1)*((a : ℂ)^(-1 : ℂ)+(a : ℂ)^(1-2*u))/2

private theorem weightedTheta_hasMellin {u : ℂ} (hu : 1 < u.re) :
    HasMellin (fun t : ℝ => (t : ℂ)^(-1/2 : ℂ) • thetaDefect t) u
      (2*completedRiemannZeta (2*u-1)) := by
  have hv : 1/2 < (u+(-1/2 : ℂ)).re := by simp; linarith only [hu]
  have h := thetaDefect_hasMellin hv
  constructor
  · exact MellinConvergent.cpow_smul.mpr h.1
  · rw [mellin_cpow_smul,h.2,show 2*(u+(-1/2 : ℂ))=2*u-1 by ring]

private theorem weightedScaledTheta_hasMellin {a : ℝ} (ha : 0 < a)
    {u : ℂ} (hu : 1 < u.re) :
    HasMellin (fun t : ℝ => (t : ℂ)^(-1/2 : ℂ) • thetaDefect (a^2*t)) u
      ((a : ℂ)^(1-2*u)*(2*completedRiemannZeta (2*u-1))) := by
  have hv : 1/2 < (u+(-1/2 : ℂ)).re := by simp; linarith only [hu]
  have h := scaledTheta_hasMellin ha hv
  constructor
  · exact MellinConvergent.cpow_smul.mpr h.1
  · rw [mellin_cpow_smul,h.2,show 2*(u+(-1/2 : ℂ))=2*u-1 by ring,
      show -2*(u+(-1/2 : ℂ))=1-2*u by ring]

private theorem productLambda_source {a : ℝ} (ha : 0 < a)
    {u : ℂ} (hu : 1 < u.re) :
    (productFEPair a ha).Λ u=sourceExpression a ha u := by
  have hhalf : 1/2 < u.re := by linarith only [hu]
  have hR : HasMellin (fun t => (rectTheta a t : ℂ)-1) u (epsteinLambda a ha u) :=
    (rectFEPair a ha).hasMellin hu
  have hT := thetaDefect_hasMellin hhalf
  have hS := scaledTheta_hasMellin ha hhalf
  have hW := weightedTheta_hasMellin hu
  have hA := hasMellin_const_smul hW.1 (a : ℂ)⁻¹
  have hV := weightedScaledTheta_hasMellin ha hu
  have h1 := hasMellin_sub hR.1 hT.1
  have h2 := hasMellin_sub h1.1 hS.1
  have h3 := hasMellin_sub h2.1 hA.1
  have hsum := hasMellin_sub h3.1 hV.1
  rw [h3.2,h2.2,h1.2,hR.2,hT.2,hS.2,hA.2,hW.2,hV.2] at hsum
  have hP := (productFEPair a ha).hasMellin hu
  have he : mellin
      (fun t : ℝ => (rectTheta a t : ℂ)-1-thetaDefect t-thetaDefect (a^2*t)-
        (a : ℂ)⁻¹ • ((t : ℂ)^(-1/2 : ℂ) • thetaDefect t)-
        (t : ℂ)^(-1/2 : ℂ) • thetaDefect (a^2*t)) u=
      4*(productFEPair a ha).Λ u := by
    calc
      _ = mellin (fun t => (4 : ℂ) •
          ((productFEPair a ha).f t-(productFEPair a ha).f₀)) u := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        apply congrArg (fun z : ℂ => (t : ℂ)^(u-1) • z)
        have hs := thetaProduct_source_expansion ha ht
        dsimp only [thetaDefect,productFEPair,renormalizedProduct]
        simp only [smul_eq_mul]
        linear_combination -hs
      _ = _ := by rw [mellin_const_smul,hP.2,smul_eq_mul]
  have hv := hsum.2
  rw [he] at hv
  unfold sourceExpression
  simp only [smul_eq_mul,Complex.cpow_neg_one] at hv ⊢
  linear_combination (1/4 : ℂ)*hv

#print axioms productLambda_source

private theorem nonreal_ne_real {u : ℂ} (hu : 0 < u.im) (r : ℝ) : u ≠ (r : ℂ) := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.ofReal_im] at hi
  exact hu.ne' hi

private theorem sourceExpression_differentiable {a : ℝ} (ha : 0 < a)
    {u : ℂ} (hu : 0 < u.im) : DifferentiableAt ℂ (sourceExpression a ha) u := by
  have hu0 : u ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real hu 0
  have hu1 : u ≠ 1 := by simpa only [Complex.ofReal_one] using nonreal_ne_real hu 1
  have h2im : 0 < (2*u).im := by simp; linarith only [hu]
  have h2subim : 0 < (2*u-1).im := by simp; linarith only [hu]
  have h20 : 2*u ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real h2im 0
  have h21 : 2*u ≠ 1 := by simpa only [Complex.ofReal_one] using nonreal_ne_real h2im 1
  have hs0 : 2*u-1 ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real h2subim 0
  have hs1 : 2*u-1 ≠ 1 := by simpa only [Complex.ofReal_one] using nonreal_ne_real h2subim 1
  have hE : DifferentiableAt ℂ (epsteinLambda a ha) u :=
    (rectFEPair a ha).differentiableAt_Λ (Or.inl hu0) (Or.inl hu1)
  have hZ : DifferentiableAt ℂ (fun v : ℂ => completedRiemannZeta (2*v)) u :=
    (differentiableAt_completedZeta h20 h21).comp u (by fun_prop)
  have hS : DifferentiableAt ℂ (fun v : ℂ => completedRiemannZeta (2*v-1)) u :=
    (differentiableAt_completedZeta hs0 hs1).comp u (by fun_prop)
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hP : DifferentiableAt ℂ (fun v : ℂ => (a : ℂ)^(-2*v)) u :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl ha0)
  have hQ : DifferentiableAt ℂ (fun v : ℂ => (a : ℂ)^(1-2*v)) u :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl ha0)
  exact ((hE.div_const 4).sub ((hZ.mul (differentiableAt_const _ |>.add hP)).div_const 2)).sub
    ((hS.mul (differentiableAt_const _ |>.add hQ)).div_const 2)

private def upperDomain : Set ℂ := {u : ℂ | 0 < u.im}

private theorem upperDomain_open : IsOpen upperDomain :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem upperDomain_preconnected : IsPreconnected upperDomain := by
  have hc : Convex ℝ upperDomain := by
    intro x hx y hy a b ha hb hab
    change 0 < (a • x+b • y).im
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
    by_cases ha0 : a=0
    · subst a
      have hb1 : b=1 := by simpa only [zero_add] using hab
      rw [hb1,zero_mul,zero_add,one_mul]
      exact hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hx) (mul_nonneg hb hy.le)
  exact hc.isPreconnected

private def defect (a : ℝ) (ha : 0 < a) (u : ℂ) : ℂ :=
  (productFEPair a ha).Λ u-sourceExpression a ha u

private theorem defect_analytic {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ (defect a ha) upperDomain := by
  have hd : DifferentiableOn ℂ (defect a ha) upperDomain := by
    intro u hu
    have hu0 : u ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real hu 0
    have hu1 : u ≠ 1 := by simpa only [Complex.ofReal_one] using nonreal_ne_real hu 1
    exact (((productFEPair a ha).differentiableAt_Λ (Or.inl hu0) (Or.inl hu1)).sub
      (sourceExpression_differentiable ha hu)).differentiableWithinAt
  exact hd.analyticOnNhd upperDomain_open

/-- The exact five-term source formula continues throughout the upper half-plane. -/
theorem productLambda_eq_sourceExpression {a : ℝ} (ha : 0 < a)
    {u : ℂ} (hu : 0 < u.im) :
    (productFEPair a ha).Λ u=sourceExpression a ha u := by
  have he : defect a ha =ᶠ[𝓝 (⟨2,1⟩ : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (⟨2,1⟩ : ℂ) ∈ {v : ℂ | 1 < v.re} by norm_num)] with v hv
    exact sub_eq_zero.mpr (productLambda_source ha hv)
  have hz := (defect_analytic ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    upperDomain_preconnected (show (⟨2,1⟩ : ℂ) ∈ upperDomain by norm_num [upperDomain]) he hu
  exact sub_eq_zero.mp hz

/-- The actual convergent theta correlation has the continued Epstein–zeta formula. -/
theorem thetaProduct_hasMellin_sourceExpression {a : ℝ} (ha : 0 < a) {u : ℂ}
    (hu : 0 < u.re) (hu1 : u.re < 1) (him : 0 < u.im) :
    HasMellin (thetaProduct a) u (sourceExpression a ha u) := by
  simpa only [productLambda_eq_sourceExpression ha him] using thetaProduct_hasMellin ha hu hu1

#print axioms productLambda_eq_sourceExpression
#print axioms thetaProduct_hasMellin_sourceExpression

private theorem sourceExpression_eq_core {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) :
    sourceExpression a ha (w/2)=Gammaℝ w*fieldCore w a/2 := by
  have hw0 : w ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real him 0
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hw
  have hGhalf : Gamma (w/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith only [hw])
  have hPi : (Real.pi : ℂ)^(w/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hE : Gammaℝ w*MayerEpsteinQuadrants.epsteinField w a=epsteinLambda a ha (w/2)/2 := by
    rw [MayerEpsteinQuadrants.epsteinField,dif_pos ha,Gammaℝ_def,
      show -w/2= -(w/2) by ring,Complex.cpow_neg]
    field_simp
  have hZ : Gammaℝ w*riemannZeta w=completedRiemannZeta w := by
    rw [riemannZeta_def_of_ne_zero hw0]
    field_simp
  have hminus : 0 < (w-1).im := by simpa only [Complex.sub_im,Complex.one_im,sub_zero] using him
  have hm0 : w-1 ≠ 0 := by simpa only [Complex.ofReal_zero] using nonreal_ne_real hminus 0
  have hR := _root_.RHTower.reflectedCompletedLambda_eq_completed hm0
    (_root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero hminus.ne')
  have hS : Gammaℝ w*scatteringCoefficient w=completedRiemannZeta (w-1) := by
    rw [scatteringCoefficient,div_eq_mul_inv,mul_left_comm,mul_inv_cancel₀ hG,mul_one,hR]
  simp only [sourceExpression,show 2*(w/2)=w by ring,show -2*(w/2)= -w by ring]
  unfold fieldCore scatteringPowers
  linear_combination -(1/2 : ℂ)*hE+((1+(a : ℂ)^(-w))/2)*hZ+
    (((a : ℂ)^(-1 : ℂ)+(a : ℂ)^(1-w))/2)*hS

/-- The actual theta-product Mellin integral is exactly the Gamma-normalized scattering core. -/
theorem core_theta_hasMellin {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    HasMellin (thetaProduct a) (w/2) (Gammaℝ w*fieldCore w a/2) := by
  have h := thetaProduct_hasMellin_sourceExpression ha
    (u := w/2) (by simp; linarith only [hw]) (by simp; linarith only [hw2])
    (by simp; linarith only [him])
  simpa only [sourceExpression_eq_core hw him ha] using h

/-- The finite-energy Mayer core is the literal Gaussian-ray correlation, including all
axis and scattering subtractions. -/
theorem core_theta_integral {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    fieldCore w a=2/Gammaℝ w*
      ∫ t in Ioi (0 : ℝ),(t : ℂ)^(w/2-1)*thetaRay t*thetaRay (a^2*t) := by
  have h := (core_theta_hasMellin hw hw2 him ha).2
  have hi : (∫ t in Ioi (0 : ℝ),(t : ℂ)^(w/2-1)*thetaRay t*thetaRay (a^2*t))=
      Gammaℝ w*fieldCore w a/2 := by
    simpa only [mellin,thetaProduct,smul_eq_mul,mul_assoc] using h
  rw [hi]
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hw
  field_simp

#print axioms core_theta_hasMellin
#print axioms core_theta_integral

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaCore
