import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.Coercivity
import GaloisForLFunctions.HTGeometry.ThermodynamicProjectiveRecurrenceDesertLaw

/-! # Detecting a projective return by commuting probes -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section

/-- If H and the probes have scalar joint commutant, their stability constant
bounds the empty-circuit error at every time by the error of any target that
leaves the probes fixed. -/
theorem phase_distance_control {I : Type} {J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    (r : I) (H : selfAdjoint (Matrix I I ℂ)) (P : J → Matrix I I ℂ)
    (hscalar : ∀ X : Matrix I I ℂ, H.val*X = X*H.val →
      (∀ j, P j*X = X*P j) → X = X r r • (1 : Matrix I I ℂ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ∀ V : Matrix I I ℂ, (∀ j, P j*V = V*P j) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution H.val t-c • (1 : Matrix I I ℂ)‖ ≤
        A*‖unitaryEvolution H.val t-V‖ := by
  obtain ⟨K,hK,hbound⟩ := (scalar_commutant_iff_estimate r H.val P).mp hscalar
  refine ⟨2*(1+K*(2*‖H.val‖)),by positivity,?_⟩
  intro t V hP
  let U := unitaryEvolution H.val t
  let z := V r r
  let c := anchorPhase H.2.isHermitian.eigenvalues r t
  have hcomm : H.val*U = U*H.val := (((Commute.refl H.val).smul_right (-Complex.I)).smul_right t).exp_right.eq
  have htest : (fun j => P j*V-V*P j) = 0 := funext fun j => sub_eq_zero.mpr (hP j)
  have hdef : ‖H.val*V - V*H.val‖ ≤ 2*‖H.val‖*‖U-V‖ := by
    have he : H.val*V-V*H.val = H.val*(V-U)-(V-U)*H.val := by
      rw [mul_sub,sub_mul,hcomm]
      abel
    rw [he]
    have hh := (norm_sub_le (H.val*(V-U)) ((V-U)*H.val)).trans
      (add_le_add (norm_mul_le H.val (V-U)) (norm_mul_le (V-U) H.val))
    rw [norm_sub_rev V U] at hh
    linarith only [hh]
  have hV := hbound V
  rw [htest,norm_zero,max_eq_left (norm_nonneg _)] at hV
  have hnear : ‖U-z • (1 : Matrix I I ℂ)‖ ≤ (1+K*(2*‖H.val‖))*‖U-V‖ := by
    have htri := norm_sub_le_norm_sub_add_norm_sub U V (z • (1 : Matrix I I ℂ))
    nlinarith only [htri,hV,mul_le_mul_of_nonneg_left hdef hK.le]
  refine ⟨c,by simp [c,anchorPhase,Complex.norm_exp],?_⟩
  have hh := norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar H.2.isHermitian r t z
  exact hh.trans ((mul_le_mul_of_nonneg_left hnear zero_le_two).trans_eq (mul_assoc ..).symm)

#print axioms phase_distance_control
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
