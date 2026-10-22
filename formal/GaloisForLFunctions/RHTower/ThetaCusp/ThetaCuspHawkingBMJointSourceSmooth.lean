import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTimeField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalWarpJets

/-! The literal time-reduced source is smooth in both original time and tortoise radius. -/

open Complex Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section

/-- A positive-real complex power stays smooth after any smooth positive real parametrization. -/
theorem power_comp_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℂ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hp : ∀ x, 0 < f x) :
    ContDiff ℝ ∞ (fun x => power s (f x)) := by
  have he (x : E) : power s (f x) = Complex.exp (s * (Real.log (f x) : ℂ)) := by
    rw [power, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp x).ne'),
      ← Complex.ofReal_log (hp x).le]
    congr 1
    ring
  simp_rw [he]
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (hf.log (fun x => (hp x).ne')))).cexp

/-- The literal independent-frequency radial amplitude is smooth at every order. -/
theorem sourceAmplitude_smooth (s w a T : ℂ) :
    ContDiff ℝ ∞ (sourceAmplitude s w a T) := by
  have hp := power_comp_smooth (2*s)
    (contDiff_const.add D4BMJointConformal.radialUnit_smooth) radialUnit_add_one_pos
  unfold sourceAmplitude
  exact ((((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.mul hp).mul contDiff_const).mul
    contDiff_const)

/-- The literal causal onset is smooth at every order. -/
theorem timeOnset_smooth (v : ℂ) : ContDiff ℝ ∞ (timeOnset v) := by
  unfold timeOnset
  exact (Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff).mul
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- The differentiated literal causal onset is still smooth at every order. -/
theorem timeOnsetFirst_smooth (v : ℂ) : ContDiff ℝ ∞ (timeOnsetFirst v) := by
  have htransition : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hderiv : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp htransition).2
  unfold timeOnsetFirst
  exact ((Complex.ofRealCLM.contDiff.comp hderiv).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp htransition))).mul
      (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- The complete radial source coefficient is smooth at every order. -/
theorem reducedCoefficient_smooth (s w a T : ℂ) :
    ContDiff ℝ ∞ (reducedCoefficient s w a T) := by
  have hU : ContDiff ℝ ∞ (fun t : ℝ => (radialUnit t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp D4BMJointConformal.radialUnit_smooth
  have hP : ContDiff ℝ ∞ (fun t : ℝ => reducedPolynomial s w (radialUnit t)) := by
    unfold reducedPolynomial liftSecondPolynomial amplitudeRate
    fun_prop
  unfold reducedCoefficient
  exact (sourceAmplitude_smooth s w a T).mul hP

/-- The literal first radial lift is smooth at every order. -/
theorem radialLiftFirst_smooth (s w a T : ℂ) :
    ContDiff ℝ ∞ (radialLiftFirst s w a T) := by
  have hU : ContDiff ℝ ∞ (fun t : ℝ => (radialUnit t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp D4BMJointConformal.radialUnit_smooth
  have hP : ContDiff ℝ ∞ (fun t : ℝ => liftFirstPolynomial s w (radialUnit t)) := by
    unfold liftFirstPolynomial amplitudeRate
    fun_prop
  unfold radialLiftFirst
  exact contDiff_const.mul ((sourceAmplitude_smooth s w a T).mul hP)

/-- The exact original two-variable reduced source is smooth, retaining the positive-radius
complex power, radial lift, and differentiated causal onset. -/
theorem timeReducedCoefficient_smooth (s a : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => timeReducedCoefficient s a p.1 p.2) := by
  have hA := (reducedCoefficient_smooth s 0 a 1).comp
    (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  have hB := (timeOnset_smooth (2*s)).comp
    ((contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).add
      (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)))
  have hC := (radialLiftFirst_smooth s 0 a 1).comp
    (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  have hD := (timeOnsetFirst_smooth (2*s)).comp
    ((contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).add
      (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)))
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
    reducedCoefficient s 0 a 1 p.2*timeOnset (2*s) (p.1+p.2)+
      2*radialLiftFirst s 0 a 1 p.2*timeOnsetFirst (2*s) (p.1+p.2))
  exact (hA.mul hB).add ((contDiff_const.mul hC).mul hD)

end
end RHTower.D4BMJointSource
