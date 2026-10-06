import GaloisForLFunctions.RHTower.ThetaCuspRatioThirdSlope

namespace HTGeometry.ThetaRatioQuadraticSource
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource

def headMinor : Poly := signedMoment 1*signedMoment 3-(signedMoment 2)^2
def minorA : Poly :=
  signedMoment 1*signedMoment 3*signedMoment 7-signedMoment 1*(signedMoment 5)^2-
    (signedMoment 2)^2*signedMoment 7+2*signedMoment 2*signedMoment 4*signedMoment 5-
    signedMoment 3*(signedMoment 4)^2
def minorB : Poly :=
  -(signedMoment 1*signedMoment 3*signedMoment 6-signedMoment 1*signedMoment 4*signedMoment 5-
    (signedMoment 2)^2*signedMoment 6+signedMoment 2*signedMoment 3*signedMoment 5+
    signedMoment 2*(signedMoment 4)^2-(signedMoment 3)^2*signedMoment 4)

def sixthSlope (P : Poly) : Poly := sourceJet 0*lie P-6*P*lie (sourceJet 0)
def loadedConstant (c : ℂ) : Poly := minorA+3*C c*(sourceJet 0)^2*headMinor
def loadedLinear (c : ℂ) : Poly := 2*C c*sourceJet 0*headMinor*sourceJet 1
def slopeConstant (c : ℂ) : Poly := sixthSlope (loadedConstant c)+sourceJet 0*loadedLinear c
def slopeLinear (c : ℂ) : Poly := sixthSlope (loadedLinear c)
def sourceQuadratic (c center eta : ℂ) : Poly :=
  slopeConstant c+C center*slopeLinear c+2*C eta*sixthSlope minorB+C (eta^2)*thirdSlope

end
end HTGeometry.ThetaRatioQuadraticSource

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioQuadraticSource
open ThetaCuspModularRatio ThetaCuspOddDirectionTransport

theorem native_odd_moment {x : ℝ} (hx : 0 ≤ x) (i : Fin 7) :
    (moment i x:ℂ)=(sourceAmplitude x:ℂ)^2*eval (state x) (signedMoment (i.val+1)) := by
  unfold moment
  push_cast
  rw [native_reflection hx]
  simp only [signedMoment,map_mul,eval_C]
  ring

theorem native_cofactorA {x : ℝ} (hx : 0 ≤ x) :
    (cofactorA x:ℂ)=(sourceAmplitude x:ℂ)^6*eval (state x) minorA := by
  unfold cofactorA
  dsimp only
  push_cast
  simp_rw [native_odd_moment hx]
  norm_num [minorA]
  ring

theorem native_cofactorB {x : ℝ} (hx : 0 ≤ x) :
    (cofactorB x:ℂ)=(sourceAmplitude x:ℂ)^6*eval (state x) minorB := by
  unfold cofactorB
  dsimp only
  push_cast
  simp_rw [native_odd_moment hx]
  norm_num [minorB]
  ring

theorem native_headMinor {x : ℝ} (hx : 0 ≤ x) :
    (thetaCuspNativeOddHeadDet x:ℂ)=
      (sourceAmplitude x:ℂ)^4*eval (state x) headMinor := by
  unfold thetaCuspNativeOddHeadDet
  push_cast
  simp_rw [native_reflection hx]
  norm_num [headMinor,signedMoment]
  ring

theorem sourceAmplitude_ne {x : ℝ} (hx : 0 ≤ x) : (sourceAmplitude x:ℂ) ≠ 0 := by
  have hM := thetaCuspCompletedThetaProfile_pos x
  have ht := t_pos hx
  have hn : 0 < sourceAmplitude x := by unfold sourceAmplitude; positivity
  exact Complex.ofReal_ne_zero.mpr hn.ne'

theorem sourceZero_ne {x : ℝ} (hx : 0 ≤ x) : eval (state x) (sourceJet 0) ≠ 0 := by
  rw [sourceJet_zero_eval]
  change (k x:ℂ)-1/6 ≠ 0
  have hp : k x-1/6 ≠ 0 := by linarith [k_gt hx]
  convert Complex.ofReal_ne_zero.mpr hp using 1
  push_cast
  rfl

theorem normalizedB_value {x : ℝ} (hx : 0 ≤ x) :
    (normalizedB x:ℂ)=eval (state x) minorB/(eval (state x) (sourceJet 0))^6 := by
  have hp : (thetaCuspFullSource x:ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet 0) := by
    simpa only [iteratedDeriv_zero] using source_jet hx 0
  unfold normalizedB
  push_cast
  rw [native_cofactorB hx,hp]
  field_simp [sourceAmplitude_ne hx,sourceZero_ne hx]

theorem normalizedBase_value (c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (normalizedBase c x:ℂ)=
      (eval (state x) (loadedConstant (c:ℂ))+(x:ℂ)*eval (state x) (loadedLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^6 := by
  have hp : (thetaCuspFullSource x:ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet 0) := by
    simpa only [iteratedDeriv_zero] using source_jet hx 0
  have hp1 : ((deriv thetaCuspFullSource x:ℝ):ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet 1) := by
    simpa only [iteratedDeriv_one] using source_jet hx 1
  unfold normalizedBase thetaCuspCenterCompensationSource
  push_cast
  rw [native_cofactorA hx,native_headMinor hx,hp,hp1]
  simp only [loadedConstant,loadedLinear,map_add,map_mul,map_pow,map_ofNat,eval_C]
  field_simp [sourceAmplitude_ne hx,sourceZero_ne hx]
  ring

end
end RHTower.ThetaRatioSourceIncidence
