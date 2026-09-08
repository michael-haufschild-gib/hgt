import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarCutoffBoundaryValue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularModularity

/-! Actual physical angular field and its zero/nonzero cutoff calibration at every Xi target. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

def physicalAngularParameter (q : XiZeroCopy) : ℂ :=
  Complex.I*thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)

theorem physicalAngularParameter_eq (q : XiZeroCopy) :
    physicalAngularParameter q = ((q.1:ℂ)-1)/2 := by
  unfold physicalAngularParameter thetaCuspHawkingTopologicalBlackHoleAngularMomentum xiSpectralPoint
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem physical_parameter_nonreal (q : XiZeroCopy) :
    (physicalAngularParameter q).im ≠ 0 := by
  rw [physicalAngularParameter_eq]
  simpa using div_ne_zero (xi_divisor_support_im_ne_zero q.1) (by norm_num : (2:ℝ) ≠ 0)

private theorem lambda_at_xi (q : XiZeroCopy) : reflectedCompletedLambda (q.1:ℂ) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hne1 : (q.1:ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    linarith [hstrip.2]
  have hz := (xi_eq_zero_iff hstrip.1 hne1).mp (xi_eq_zero_of_mem_divisor_support q.1)
  rw [reflectedCompletedLambda,hz,mul_zero]

private theorem lambda_before_xi_nonzero (q : XiZeroCopy) :
    reflectedCompletedLambda ((q.1:ℂ)-1) ≠ 0 := by
  have hi : ((q.1:ℂ)-1).im ≠ 0 := by simpa using xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1:ℂ)-1 ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have he : reflectedCompletedLambda ((q.1:ℂ)-1) = completedRiemannZeta ((q.1:ℂ)-1) := by
    rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
    field_simp [gammaR_ne_zero_of_im_ne hi]
  have hr : 1 < (2-(q.1:ℂ)).re := by
    change 1 < 2-(q.1:ℂ).re
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  have hj : (2-(q.1:ℂ)).im ≠ 0 := by
    simpa using neg_ne_zero.mpr (xi_divisor_support_im_ne_zero q.1)
  have hn : 2-(q.1:ℂ) ≠ 0 := by intro h; exact hj (by rw [h]; rfl)
  rw [he,← completedRiemannZeta_one_sub ((q.1:ℂ)-1),
    show 1-((q.1:ℂ)-1)=2-(q.1:ℂ) by ring]
  intro hz
  apply riemannZeta_ne_zero_of_one_lt_re hr
  rw [riemannZeta_def_of_ne_zero hn,hz,zero_div]

private theorem physical_weyl (q : XiZeroCopy) :
    d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false = 1-(q.1:ℂ)/2 ∧
    d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) true = (q.1:ℂ)/2 ∧
    d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) false =
      reflectedCompletedLambda ((q.1:ℂ)-1) ∧
    d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) true = 0 := by
  rw [physicalAngularParameter_eq]
  simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCuspSign,Bool.false_eq_true,ite_false,ite_true,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul]
  refine ⟨by ring,by ring,?_,?_⟩
  · congr 1
    ring
  · rw [show 1+2*(((q.1:ℂ)-1)/2)=(q.1:ℂ) by ring,lambda_at_xi q]

/-- At every physical Xi parameter the full principal part retains exactly the nonzero Weyl branch. -/
theorem physicalScalar_principal (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    principal (physicalAngularParameter q) z =
      reflectedCompletedLambda ((q.1:ℂ)-1)*(z 1:ℂ)^(1-(q.1:ℂ)/2) := by
  obtain ⟨hm,hp,hcm,hcp⟩ := physical_weyl q
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor,mul_one,hm,hp,hcm,hcp,zero_mul,add_zero]

/-- The actual full physical testing field obeys modular inversion, including its complete tail. -/
theorem physicalScalar_invert (q : XiZeroCopy) (z : D4BMUpperHalfPlaneCoordinate) :
    scalar (physicalAngularParameter q)
      ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      scalar (physicalAngularParameter q) ![z.x,z.y] := by
  have hi := physical_parameter_nonreal q
  have h0 : physicalAngularParameter q ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have hm : 2*physicalAngularParameter q-1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact hi (by linarith)
  have hp : 2*physicalAngularParameter q+1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact hi (by linarith)
  have hc : clearFactor (physicalAngularParameter q) ≠ 0 := mul_ne_zero (mul_ne_zero h0 hm) hp
  have h := clearedScalar_invert (physicalAngularParameter q) z
  rw [clearedScalar_eq _ hi,clearedScalar_eq _ hi] at h
  exact (mul_left_cancel₀ hc) h

/-- Every Xi target has an exact nonzero cutoff pairing on one original indicial branch
and a zero pairing on its complement. This calibrates actual angular integrals, not a full QNM residue. -/
theorem physicalScalar_cutoff_calibration (q : XiZeroCopy) :
    scalarCutoffPeriod (physicalAngularParameter q) ((q.1:ℂ)/2) =
        ((q.1:ℂ)-1)*reflectedCompletedLambda ((q.1:ℂ)-1) ∧
      scalarCutoffPeriod (physicalAngularParameter q) ((q.1:ℂ)/2) ≠ 0 ∧
      scalarCutoffPeriod (physicalAngularParameter q) (1-(q.1:ℂ)/2) = 0 := by
  obtain ⟨hm,hp,hcm,hcp⟩ := physical_weyl q
  have hplus := scalarCutoffPeriod_weyl (physicalAngularParameter q) true
  have hminus := scalarCutoffPeriod_weyl (physicalAngularParameter q) false
  simp only [Bool.not_true,hp,hcm] at hplus
  simp only [Bool.not_false,hm,hcp,mul_zero] at hminus
  have he : scalarCutoffPeriod (physicalAngularParameter q) ((q.1:ℂ)/2) =
      ((q.1:ℂ)-1)*reflectedCompletedLambda ((q.1:ℂ)-1) := by
    rw [hplus]
    ring
  refine ⟨he,?_,hminus⟩
  rw [he]
  refine mul_ne_zero ?_ (lambda_before_xi_nonzero q)
  intro h
  have hh := congrArg Complex.im h
  simp at hh
  exact xi_divisor_support_im_ne_zero q.1 hh

end
end RHTower.D4BMJointSource
