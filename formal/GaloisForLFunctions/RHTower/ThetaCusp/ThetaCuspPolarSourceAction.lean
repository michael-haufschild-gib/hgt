import GaloisForLFunctions.RHTower.ThetaSourcePrimeAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltedSchwartz

/-!
# The pole action on the complete theta source

The two half-line actions are absolutely convergent and continuous, and their
Laplace multipliers are the two literal polar terms.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform
noncomputable section
namespace RHTower.ThetaSourceWard

def polarSourceTerm (a x u : ℝ) : ℂ :=
  (Real.exp (a*u):ℂ)*(thetaCuspFullSource (x+u):ℂ)

lemma norm_polarSourceTerm_le (a x u : ℝ) :
    ‖polarSourceTerm a x u‖ ≤
      thetaCuspDerivativeExpConstant 0*Real.exp |x| *Real.exp ((a-1)*u) := by
  have h := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs 0 (x+u)
  simp only [iteratedDeriv_zero] at h
  have hc := thetaCuspDerivativeExpConstant_nonneg 0
  have he : Real.exp (a*u)*Real.exp (-|x+u|) ≤
      Real.exp |x| *Real.exp ((a-1)*u) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self (x+u),neg_le_abs x]
  rw [polarSourceTerm,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (a*u)*(thetaCuspDerivativeExpConstant 0*Real.exp (-|x+u|)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = thetaCuspDerivativeExpConstant 0*(Real.exp (a*u)*Real.exp (-|x+u|)) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hc

lemma polarSourceTerm_continuous (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => polarSourceTerm a p.1 p.2) := by
  have hc := contDiff_thetaCuspFullSource.continuous
  unfold polarSourceTerm
  fun_prop

lemma polarSourceTerm_integrable {a : ℝ} (ha : a < 1) (x : ℝ) :
    IntegrableOn (polarSourceTerm a x) (Ioi 0) := by
  have hm : Continuous (polarSourceTerm a x) :=
    (polarSourceTerm_continuous a).comp (by fun_prop : Continuous (fun u : ℝ => (x,u)))
  apply ((integrableOn_exp_mul_Ioi (a := a-1) (by linarith) 0).const_mul
    (thetaCuspDerivativeExpConstant 0*Real.exp |x|)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_polarSourceTerm_le a x)

def polarSource (a x : ℝ) : ℂ := ∫ u in Ioi (0:ℝ), polarSourceTerm a x u

lemma polarSource_continuous {a : ℝ} (ha : a < 1) : Continuous (polarSource a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := thetaCuspDerivativeExpConstant_nonneg 0
  apply continuousAt_of_dominated (bound := fun u : ℝ =>
    thetaCuspDerivativeExpConstant 0*Real.exp (|x|+1)*Real.exp ((a-1)*u))
  · exact Filter.Eventually.of_forall fun y =>
      ((polarSourceTerm_continuous a).comp (by fun_prop : Continuous (fun u : ℝ => (y,u)))).aestronglyMeasurable
  · have hy : ∀ᶠ y in 𝓝 x, |y| < |x|+1 :=
      (continuous_abs.tendsto x).eventually (gt_mem_nhds (by linarith))
    filter_upwards [hy] with y hy
    filter_upwards with u
    exact (norm_polarSourceTerm_le a y u).trans
      (by gcongr)
  · exact (integrableOn_exp_mul_Ioi (a := a-1) (by linarith) 0).const_mul _
  · exact Filter.Eventually.of_forall fun u =>
      ((polarSourceTerm_continuous a).comp (by fun_prop : Continuous (fun y : ℝ => (y,u)))).continuousAt

lemma polarSourceTerm_laplace_point (a : ℝ) (w : ℂ) (u x : ℝ) :
    polarSourceTerm a x u*Complex.exp (w*x) =
      Complex.exp (((a:ℂ)-w)*u)*laplaceIntegrand thetaCuspTiltSource w (x+u) := by
  have he : Complex.exp (((a:ℂ)-w)*u)*Complex.exp (w*((x+u:ℝ):ℂ)) =
      (Real.exp (a*u):ℂ)*Complex.exp (w*x) := by
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold polarSourceTerm laplaceIntegrand
  rw [thetaCuspTiltSource_k]
  calc
    _ = (thetaCuspFullSource (x+u):ℂ)*
      ((Real.exp (a*u):ℂ)*Complex.exp (w*x)) := by ring
    _ = _ := by rw [← he]; ring

lemma polarSourceTerm_laplace_integrable_prod (a : ℝ) {w : ℂ} (hw : a < w.re) :
    Integrable (fun p : ℝ × ℝ => polarSourceTerm a p.2 p.1*Complex.exp (w*p.2))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      polarSourceTerm a p.2 p.1*Complex.exp (w*p.2)) :=
    ((polarSourceTerm_continuous a).comp continuous_swap).mul (by fun_prop)
  rw [integrable_prod_iff hc.aestronglyMeasurable]
  constructor
  · filter_upwards with u
    apply (((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).const_mul
      (Complex.exp (((a:ℂ)-w)*u))).congr
    exact Filter.Eventually.of_forall fun x => (polarSourceTerm_laplace_point a w u x).symm
  · have h := (integrableOn_exp_mul_Ioi (a := a-w.re) (by linarith) 0).mul_const
      (∫ x : ℝ, ‖laplaceIntegrand thetaCuspTiltSource w x‖)
    apply h.congr
    filter_upwards with u
    simp_rw [polarSourceTerm_laplace_point,norm_mul]
    rw [integral_const_mul,integral_add_right_eq_self
      (fun x : ℝ => ‖laplaceIntegrand thetaCuspTiltSource w x‖) u]
    simp [Complex.norm_exp,Complex.mul_re]

lemma polarSource_laplace_integrable (a : ℝ) {w : ℂ} (hw : a < w.re) :
    Integrable (fun x : ℝ => polarSource a x*Complex.exp (w*x)) := by
  apply (polarSourceTerm_laplace_integrable_prod a hw).integral_prod_right.congr
  filter_upwards with x
  exact integral_mul_const _ _

lemma integral_polarSource_laplace (a : ℝ) {w : ℂ} (hw : a < w.re) :
    (∫ x : ℝ, polarSource a x*Complex.exp (w*x)) =
      (w-(a:ℂ))⁻¹ * bilateralLaplace thetaCuspTiltSource w := by
  have h : (∫ x : ℝ, polarSource a x*Complex.exp (w*x)) =
      ∫ x : ℝ, ∫ u in Ioi (0:ℝ), polarSourceTerm a x u*Complex.exp (w*x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact (integral_mul_const _ _).symm
  rw [h,← integral_integral_swap (polarSourceTerm_laplace_integrable_prod a hw)]
  simp_rw [polarSourceTerm_laplace_point]
  simp_rw [integral_const_mul,integral_add_right_eq_self]
  rw [integral_mul_const,integral_exp_mul_complex_Ioi
    (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith)]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  change -1 / ((a:ℂ)-w)*bilateralLaplace thetaCuspTiltSource w = _
  have he : -(1:ℂ) / ((a:ℂ)-w) = (w-(a:ℂ))⁻¹ := by
    rw [div_eq_mul_inv,show (a:ℂ)-w = -(w-(a:ℂ)) by ring,inv_neg]
    ring
  rw [he]

lemma polarSource_half_point (x u : ℝ) :
    polarSourceTerm (1/2) x u + polarSourceTerm (-1/2) x u =
      ((2*Real.cosh (u/2)*thetaCuspFullSource (x+u):ℝ):ℂ) := by
  have hp : (1/2:ℝ)*u=u/2 := by ring
  have hm : (-1/2:ℝ)*u=-(u/2) := by ring
  simp only [polarSourceTerm,hp,hm,Real.cosh_eq]
  push_cast
  ring

lemma fullPolarSource_integrable (x : ℝ) :
    IntegrableOn (fun u : ℝ => ((2*Real.cosh (u/2)*thetaCuspFullSource (x+u):ℝ):ℂ)) (Ioi 0) := by
  apply ((polarSourceTerm_integrable (a := 1/2) (by norm_num) x).fun_add
    (polarSourceTerm_integrable (a := -1/2) (by norm_num) x)).congr
  exact Filter.Eventually.of_forall (polarSource_half_point x)

lemma polarSource_half_add (x : ℝ) :
    polarSource (1/2) x+polarSource (-1/2) x =
      ∫ u in Ioi (0:ℝ), ((2*Real.cosh (u/2)*thetaCuspFullSource (x+u):ℝ):ℂ) := by
  rw [polarSource,polarSource,← integral_add
    (polarSourceTerm_integrable (a := 1/2) (by norm_num) x)
    (polarSourceTerm_integrable (a := -1/2) (by norm_num) x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (polarSource_half_point x)

end RHTower.ThetaSourceWard
