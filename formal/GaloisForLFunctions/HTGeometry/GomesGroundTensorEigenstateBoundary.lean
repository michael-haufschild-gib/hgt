import GaloisForLFunctions.HTGeometry.GomesGroundStateEigenvalueReconstruction

/-!
# Eigenstate reconstruction for pointwise tensor products of finite ground states

The common-connection tensor viewpoint of arXiv:2509.25276v7 section 5.2 has an exact
scalar consequence on the corpus's Schwartz fields. Tensor products are eigenstates
precisely in the summed connection class, or the opposite quadratic class. In particular,
no energy shift makes the product an eigenstate of either original factor Hamiltonian.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Finite target Hamiltonians admit a tensor ground state only at zero energy in the summed connection class. -/
theorem gomesPolynomialGroundTensor_finite_eigen_iff (P Q R : GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM R.val (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) =
      (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) ↔
        dilatonSuperchargeCLM (P.val + Q.val) = dilatonSuperchargeCLM R.val ∧ e = 0 := by
  rw [gomesPolynomialGroundState_tensor]
  exact gomesPolynomialGroundState_finite_eigen_iff (P + Q) R e

/-- The finite eigenstate inverse problem recovers exactly the sum profile up to constant amplitude. -/
theorem gomesPolynomialGroundTensor_finite_profile_iff (P Q R : GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM R.val (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) =
      (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) ↔
        (∃ c : ℝ, P.val + Q.val = R.val + C c) ∧ e = 0 := by
  rw [gomesPolynomialGroundTensor_finite_eigen_iff, gomesDilatonConnection_constant_iff]

/-- Every polynomial target is classified, including the unique positive-energy opposite quadratic possibility. -/
theorem gomesPolynomialGroundTensor_arbitrary_eigen_iff (P Q : GomesFinitePolynomialProfile) (K : ℝ[X]) (e : ℝ) :
    dilatonHamiltonianCLM K (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) =
      (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) ↔
        (dilatonSuperchargeCLM (P.val + Q.val) = dilatonSuperchargeCLM K ∧ e = 0) ∨
          (0 < e ∧ (P.val + Q.val).derivative.derivative = C (-e) ∧
            ∃ c : ℝ, K = -(P.val + Q.val) + C c) := by
  rw [gomesPolynomialGroundState_tensor]
  exact gomesPolynomialGroundState_eigen_profiles_iff (P + Q) K e

/-- No scalar energy adjustment makes a nontrivial finite tensor product an eigenstate of its left factor. -/
theorem gomesPolynomialGroundTensor_left_not_eigen (P Q : GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM P.val (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) ≠
      (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) := by
  intro h
  have hc := ((gomesPolynomialGroundTensor_finite_eigen_iff P Q P e).mp h).1
  have hd := (gomesDilatonConnection_eq_iff (P.val + Q.val) P.val).mp hc
  simp only [derivative_add] at hd
  have hq : Q.val.derivative = 0 := by linear_combination hd
  apply gomesFinitePolynomialProfile_curvature_ne_zero Q
  rw [hq, derivative_zero]

/-- The same obstruction holds for the right factor, independently of profile degrees and energy. -/
theorem gomesPolynomialGroundTensor_right_not_eigen (P Q : GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM Q.val (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) ≠
      (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q) := by
  intro h
  have hc := ((gomesPolynomialGroundTensor_finite_eigen_iff P Q Q e).mp h).1
  have hd := (gomesDilatonConnection_eq_iff (P.val + Q.val) Q.val).mp hc
  simp only [derivative_add] at hd
  have hp : P.val.derivative = 0 := by linear_combination hd
  apply gomesFinitePolynomialProfile_curvature_ne_zero P
  rw [hp, derivative_zero]

/-- A positive tensor eigenvalue exists exactly when the summed finite profile is quadratic. -/
theorem gomesPolynomialGroundTensor_positive_eigen_iff (P Q : GomesFinitePolynomialProfile) :
    (∃ K : ℝ[X], ∃ e : ℝ, 0 < e ∧
      dilatonHamiltonianCLM K (mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) =
        (e : ℂ) • mulS (gomesPolynomialGroundState P) (gomesPolynomialGroundState Q)) ↔
          (P.val + Q.val).derivative.derivative.derivative = 0 := by
  constructor
  · rintro ⟨K, e, he, h⟩
    rcases (gomesPolynomialGroundTensor_arbitrary_eigen_iff P Q K e).mp h with ⟨_, hz⟩ | ⟨_, hd, _⟩
    · exact False.elim (he.ne' hz)
    · rw [hd, derivative_C]
  · intro h
    let PQ : {R : GomesFinitePolynomialProfile // R.val.derivative.derivative.derivative = 0} := ⟨P + Q, h⟩
    obtain ⟨he, hh⟩ := gomesPolynomialGroundState_quadratic_dual_eigen PQ
    refine ⟨-(P.val + Q.val), -(P.val + Q.val).derivative.derivative.eval 0, he, ?_⟩
    rw [gomesPolynomialGroundState_tensor]
    exact hh

end GaloisForLFunctions.HTGeometry
