import GaloisForLFunctions.RHTower.ThetaCuspRatioSourceJets
import GaloisForLFunctions.RHTower.ThetaCuspModularCompensationDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddGapDerivative
/-! # Exact ratio-chart incidence of the complete theta source and native third minor. -/

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
open MvPolynomial HTGeometry.ThetaRatioSource
open ThetaCuspModularRatio

def state (x : ℝ) : Coord → ℂ
  | .U => u x
  | .K => k x
  | .J => J x

private theorem coordinate_eq {x : ℝ} (hx : 0≤x) (i : HTGeometry.ModularThetaLyapunovState) :
    eval (state x) (coordinate i)=thetaCuspModularLyapunovState i x := by
  rw [coordinate_eval]
  cases i with
  | S => simp [state,thetaCuspModularLyapunovState,u,thetaCuspModularMassDrift]
  | A =>
      change (4/3:ℂ)*(9-(u x:ℂ)^2)*((k x:ℂ)+1/3)=(A x:ℂ)
      rw [gap_eq_ratio_coordinates hx]
      simp only [t]
      push_cast
      ring
  | W =>
      change (u x:ℂ)*(k x:ℂ)-(J x:ℂ)=(w x:ℂ)
      simp only [J]
      push_cast
      ring

private theorem eval_pullback {x : ℝ} (hx : 0≤x) (P : HTGeometry.ModularThetaLyapunovPolynomial) :
    eval (state x) (pullback P)=eval (fun i => thetaCuspModularLyapunovState i x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [pullback]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
      simp only [map_mul,eval_X,hP]
      rw [show pullback (X i)=coordinate i by simp [pullback],coordinate_eq hx]

/-- Every actual source derivative retains the same exact ratio-chart mass. -/
theorem source_jet {x : ℝ} (hx : 0≤x) (n : ℕ) :
    ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet n) := by
  have h := thetaCuspFullSource_jet_eq_lyapunovSourcePolynomial n x
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile,← eval_pullback hx,
    sourceJet_pullback,map_mul,amplitudeFactor_eval] at h
  rw [h]
  simp only [state,sourceAmplitude,t]
  push_cast
  ring

end
end RHTower.ThetaRatioSourceIncidence
namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def reflectionJet (n : ℕ) : Poly :=
  ∑ i ∈ Finset.range (n+1), C ((n.choose i:ℂ)*(-1:ℂ)^(n-i))*sourceJet i*sourceJet (n-i)

def signedMoment (r : ℕ) : Poly := C ((-1:ℂ)^r)*reflectionJet (2*r)

def thirdMinor : Poly :=
  signedMoment 1*signedMoment 3*signedMoment 5-signedMoment 1*(signedMoment 4)^2-
  (signedMoment 2)^2*signedMoment 5+2*signedMoment 2*signedMoment 3*signedMoment 4-
  (signedMoment 3)^3

def thirdSlope : Poly := sourceJet 0*lie thirdMinor-6*thirdMinor*lie (sourceJet 0)

end
end HTGeometry.ThetaRatioSource
namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
open MvPolynomial HTGeometry.ThetaRatioSource ThetaCuspModularRatio

theorem native_reflection {x : ℝ} (hx : 0≤x) (n : ℕ) :
    (thetaCuspNativeReflectionJet n x:ℂ)=
      (sourceAmplitude x:ℂ)^2*eval (state x) (reflectionJet n) := by
  rw [thetaCuspNativeReflectionJet_eq]
  push_cast
  simp_rw [source_jet hx]
  simp only [reflectionJet,map_sum,map_mul,eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem native_third {x : ℝ} (hx : 0≤x) :
    (thetaCuspNativeOddHankelThreeDet x:ℂ)=
      (sourceAmplitude x:ℂ)^6*eval (state x) thirdMinor := by
  unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  push_cast
  simp_rw [native_reflection hx]
  norm_num [thirdMinor,signedMoment]
  ring

private theorem amplitude_pos {x : ℝ} (hx : 0≤x) : 0<sourceAmplitude x := by
  have hM := thetaCuspCompletedThetaProfile_pos x
  have ht := t_pos hx
  unfold sourceAmplitude
  positivity

theorem normalized_third {x : ℝ} (hx : 0≤x) :
    (ThetaCuspOddDirectionTransport.normalizedD x:ℂ)=
      eval (state x) thirdMinor/((k x:ℂ)-1/6)^6 := by
  unfold ThetaCuspOddDirectionTransport.normalizedD
  push_cast
  rw [native_third hx,source_eq_ratio_coordinates hx]
  have hN : (sourceAmplitude x:ℂ)≠0 := by exact_mod_cast (amplitude_pos hx).ne'
  have hp : (k x:ℂ)-1/6≠0 := by
    have hp : k x-1/6≠0 := by linarith [k_gt_fiveFourths hx]
    convert Complex.ofReal_ne_zero.mpr hp using 1 <;> push_cast <;> norm_num
  push_cast
  field_simp [hN,hp]

end
end RHTower.ThetaRatioSourceIncidence
