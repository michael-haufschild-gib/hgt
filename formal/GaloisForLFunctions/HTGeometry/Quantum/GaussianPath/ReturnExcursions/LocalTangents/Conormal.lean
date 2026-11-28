import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Sweep
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence

/-! # A norming functional for an optimal laboratory contact -/

open Metric Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
open _root_.HTGeometry.ConstraintRelativity
noncomputable section

/-- All local rotations and the free phase form a real linear space at a fixed circuit. -/
private def tangentMap {n : ℕ} (Q : Register (n+2)) :
    (PathShell n × ℝ) →ₗ[ℝ] Register (n+2) :=
  (LinearMap.mulRight ℝ Q).comp ((-Complex.I) •
    ((pathHamiltonianLM n).comp (LinearMap.fst ℝ _ _) -
      (LinearMap.snd ℝ _ _).smulRight (1 : Register (n+2))))

private theorem tangentMap_apply {n : ℕ} (Q : Register (n+2)) (y : PathShell n) (c : ℝ) :
    tangentMap Q (y,c)=direction Q y c := by rfl

/-- At a contact where one further sweep cannot reduce the error, a single
real functional attains the operator error and annihilates every local
Hamiltonian rotation as well as the global phase direction. -/
theorem contact_conormal {n : ℕ} (U : Register (n+2)) (C : TwoQubitCircuit (n+2))
    {z : ℂ} (hz : ‖z‖=1) :
    let Q := z • C.eval.val
    (∀ (D : TwoQubitCircuit (n+2)), D.gateCount ≤ C.gateCount+(n+1) →
      ∀ w : ℂ, ‖w‖=1 → ‖U-Q‖ ≤ ‖U-w • D.eval.val‖) →
    ∃ φ : StrongDual ℝ (Register (n+2)), ‖φ‖ ≤ 1 ∧ ‖φ (U-Q)‖=‖U-Q‖ ∧
      ∀ y c, φ (direction Q y c)=0 := by
  intro Q hmin
  let S := LinearMap.range (tangentMap Q)
  let X := U-Q
  have hdist : quotientDistance S X=‖X‖ := by
    apply le_antisymm
    · exact (infDist_le_dist_of_mem (show (0 : Register (n+2))∈S from S.zero_mem)).trans_eq (dist_zero_right _)
    · apply (le_infDist ⟨0,S.zero_mem⟩).mpr
      rintro A ⟨⟨y,c⟩,rfl⟩
      rw [dist_eq_norm,tangentMap_apply]
      change ‖U-Q‖≤‖U-Q-direction Q y c‖
      rw [sub_sub]
      by_contra! h
      obtain ⟨D,hD,w,hw,hfit⟩ := improve_affine_fit U C hz y c h
      exact hfit.not_ge (hmin D hD w hw)
  obtain ⟨φ,hφ,h₁,hX⟩ := exists_conormal_eq_quotientDistance S X
  refine ⟨φ,h₁,hX.trans hdist,fun y c => hφ _ ⟨(y,c),tangentMap_apply ..⟩⟩

#print axioms contact_conormal
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents
