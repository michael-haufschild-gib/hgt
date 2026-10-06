import GaloisForLFunctions.RHTower.ThetaCuspRatioUpperCenterRealIdentity
import GaloisForLFunctions.RHTower.ThetaCuspOddSeamCurvature
import Mathlib.Analysis.Calculus.DSlope

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open scoped ContDiff
open ThetaCuspOddDirectionTransport ThetaOddSeamCurvature ThetaCuspModularRatio
local notation "Phi" => thetaCuspFullSource
local notation "H" => thetaCuspNativeOddHeadDet
local notation "D" => thetaCuspNativeOddHankelThreeDet
local notation "G" => thetaCuspCenterCompensationSource

private theorem source_smooth (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n Phi) := by
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_thetaCuspFullSource.iterate_deriv n

private theorem source_first_zero : deriv Phi 0=0 := by
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)

private theorem moment_jet (k : Fin 7) :
    SeamJet (moment k) (moment k 0) (deriv (deriv (moment k)) 0) := by
  refine ⟨?_,rfl,moment_first_zero k,rfl⟩
  have hs := source_smooth
  unfold moment
  simp_rw [thetaCuspNativeReflectionJet_eq]
  fun_prop

private theorem head_regular : ContDiff ℝ ∞ H ∧ deriv H 0=0 := by
  have h := ((moment_jet 0).mul (moment_jet 2)).sub ((moment_jet 1).mul (moment_jet 1))
  have he : (fun x => moment 0 x*moment 2 x-moment 1 x*moment 1 x)=H := by
    funext x
    norm_num [thetaCuspNativeOddHeadDet,moment]
    ring
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

private theorem cofactorA_regular : ContDiff ℝ ∞ cofactorA ∧ deriv cofactorA 0=0 := by
  let j := moment_jet
  have h := (((((j 0).mul (j 2)).mul (j 6)).sub ((j 0).mul ((j 4).mul (j 4)))).sub
    (((j 1).mul (j 1)).mul (j 6))).add ((((SeamJet.const 2).mul (j 1)).mul (j 3)).mul (j 4))
  have h := h.sub ((j 2).mul ((j 3).mul (j 3)))
  have he : (fun x => moment 0 x*moment 2 x*moment 6 x-
      moment 0 x*(moment 4 x*moment 4 x)-(moment 1 x*moment 1 x)*moment 6 x+
      2*moment 1 x*moment 3 x*moment 4 x-moment 2 x*(moment 3 x*moment 3 x))=cofactorA := by
    funext x
    unfold cofactorA
    ring
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

private theorem cofactorB_regular : ContDiff ℝ ∞ cofactorB ∧ deriv cofactorB 0=0 := by
  let j := moment_jet
  have h := ((((((j 0).mul (j 2)).mul (j 5)).sub (((j 0).mul (j 3)).mul (j 4))).sub
    (((j 1).mul (j 1)).mul (j 5))).add (((j 1).mul (j 2)).mul (j 4))).add
    ((j 1).mul ((j 3).mul (j 3)))
  have h := (h.sub (((j 2).mul (j 2)).mul (j 3))).neg
  have he : (fun x => -(moment 0 x*moment 2 x*moment 5 x-
      moment 0 x*moment 3 x*moment 4 x-(moment 1 x*moment 1 x)*moment 5 x+
      moment 1 x*moment 2 x*moment 4 x+moment 1 x*(moment 3 x*moment 3 x)-
      (moment 2 x*moment 2 x)*moment 3 x))=cofactorB := by
    funext x
    unfold cofactorB
    ring
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

private theorem third_regular : ContDiff ℝ ∞ D ∧ deriv D 0=0 := by
  let j := moment_jet
  have h := (((((j 0).mul (j 2)).mul (j 4)).sub ((j 0).mul ((j 3).mul (j 3)))).sub
    (((j 1).mul (j 1)).mul (j 4))).add ((((SeamJet.const 2).mul (j 1)).mul (j 2)).mul (j 3))
  have h := h.sub (((j 2).mul (j 2)).mul (j 2))
  have he : (fun x => moment 0 x*moment 2 x*moment 4 x-
      moment 0 x*(moment 3 x*moment 3 x)-(moment 1 x*moment 1 x)*moment 4 x+
      2*moment 1 x*moment 2 x*moment 3 x-(moment 2 x*moment 2 x)*moment 2 x)=D := by
    funext x
    norm_num [thetaCuspNativeOddHankelThreeDet,HilbertMetric.signedEvenHankelThreeDet,moment]
    ring
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

private theorem compensation_regular : ContDiff ℝ ∞ G ∧ deriv G 0=0 := by
  have hp : ContDiff ℝ ∞ (deriv Phi) := by
    simpa only [iteratedDeriv_one] using source_smooth 1
  have h0 : HasDerivAt Phi 0 0 := by
    simpa only [source_first_zero] using
      (contDiff_thetaCuspFullSource.differentiable (by simp) 0).hasDerivAt
  have h1 := (hp.differentiable (by simp) 0).hasDerivAt
  constructor
  · unfold thetaCuspCenterCompensationSource
    have hs := contDiff_thetaCuspFullSource
    fun_prop
  · have hd := ((h0.pow 2).const_mul 3).add
      ((((hasDerivAt_id (0:ℝ)).const_mul 2).mul h0).mul h1)
    have he : HasDerivAt G 0 0 := by
      convert hd using 1 <;>
        first | rfl | simp [source_first_zero]
    exact he.deriv

private theorem inverse_six_jet :
    SeamJet (fun x => (Phi x^6)⁻¹) ((Phi 0^6)⁻¹)
      (deriv (deriv (fun x => (Phi x^6)⁻¹)) 0) := by
  have h0 : HasDerivAt Phi 0 0 := by
    simpa only [source_first_zero] using
      (contDiff_thetaCuspFullSource.differentiable (by simp) 0).hasDerivAt
  have hn (x : ℝ) : Phi x^6 ≠ 0 := pow_ne_zero _ (thetaCuspFullSource_pos_all x).ne'
  refine ⟨(contDiff_thetaCuspFullSource.pow 6).inv hn,rfl,?_,rfl⟩
  have hd := (h0.pow 6).inv (hn 0)
  change HasDerivAt (fun x => (Phi x^6)⁻¹) _ 0 at hd
  simpa using hd.deriv

theorem normalizedBase_regular (c : ℝ) :
    ContDiff ℝ ∞ (normalizedBase c) ∧ deriv (normalizedBase c) 0=0 := by
  have ja : SeamJet cofactorA (cofactorA 0) (deriv (deriv cofactorA) 0) :=
    ⟨cofactorA_regular.1,rfl,cofactorA_regular.2,rfl⟩
  have jg : SeamJet G (G 0) (deriv (deriv G) 0) :=
    ⟨compensation_regular.1,rfl,compensation_regular.2,rfl⟩
  have jh : SeamJet H (H 0) (deriv (deriv H) 0) :=
    ⟨head_regular.1,rfl,head_regular.2,rfl⟩
  have h := (ja.add ((SeamJet.const c).mul (jg.mul jh))).mul inverse_six_jet
  have he : (fun x => (cofactorA x+c*(G x*H x))*(Phi x^6)⁻¹)=normalizedBase c := by
    funext x
    unfold normalizedBase
    rw [div_eq_mul_inv]
    ring
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

theorem normalizedB_regular : ContDiff ℝ ∞ normalizedB ∧ deriv normalizedB 0=0 := by
  have jb : SeamJet cofactorB (cofactorB 0) (deriv (deriv cofactorB) 0) :=
    ⟨cofactorB_regular.1,rfl,cofactorB_regular.2,rfl⟩
  have h := jb.mul inverse_six_jet
  have he : (fun x => cofactorB x*(Phi x^6)⁻¹)=normalizedB := by
    funext x
    simp only [normalizedB,div_eq_mul_inv]
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

theorem normalizedD_regular : ContDiff ℝ ∞ normalizedD ∧ deriv normalizedD 0=0 := by
  have jd : SeamJet D (D 0) (deriv (deriv D) 0) :=
    ⟨third_regular.1,rfl,third_regular.2,rfl⟩
  have h := jd.mul inverse_six_jet
  have he : (fun x => D x*(Phi x^6)⁻¹)=normalizedD := by
    funext x
    simp only [normalizedD,div_eq_mul_inv]
  rw [he] at h
  exact ⟨h.smooth,h.first⟩

theorem centerDrive_smooth (c : ℝ) : ContDiff ℝ ∞ (ThetaCuspHeadGrowth.centerDrive c) := by
  have hl : ContDiff ℝ ∞ (deriv thetaCuspLogSource) := by
    simpa using contDiff_thetaCuspLogSource.iterate_deriv 1
  have hh := head_regular.1
  have hp := contDiff_thetaCuspFullSource
  have hn (x : ℝ) : Phi x^4 ≠ 0 := pow_ne_zero _ (thetaCuspFullSource_pos_all x).ne'
  unfold ThetaCuspHeadGrowth.centerDrive ThetaCuspHeadGrowth.normalizedHead
  fun_prop

end
end RHTower.ThetaCuspUpperSeam
