import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialDegreeRigidity

/-!
# Arbitrary finite tensor families of polynomial ground states

A distinguished first factor and a list of further factors encode every nonempty finite
family without introducing a nonexistent finite tensor unit. The full family retains the
largest polynomial degree. Its exceptional positive-energy class exists exactly when
every factor is quadratic.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The finite profile of a nonempty family, with one distinguished initial factor. -/
def gomesFinitePolynomialTensorFold (P : GomesFinitePolynomialProfile)
    (L : List GomesFinitePolynomialProfile) : GomesFinitePolynomialProfile :=
  L.foldr (fun Q R => Q + R) P

/-- The degree of a nonempty tensor family is its exact maximum factor degree. -/
theorem gomesFinitePolynomialTensorFold_natDegree (P : GomesFinitePolynomialProfile)
    (L : List GomesFinitePolynomialProfile) :
    (gomesFinitePolynomialTensorFold P L).val.natDegree =
      L.foldr (fun Q n => max Q.val.natDegree n) P.val.natDegree := by
  induction L with
  | nil => rfl
  | cons Q L ih =>
    change (Q.val + (gomesFinitePolynomialTensorFold P L).val).natDegree =
      max Q.val.natDegree (L.foldr (fun R n => max R.val.natDegree n) P.val.natDegree)
    rw [gomesFinitePolynomialProfile_add_natDegree, ih]

/-- Degree bounds for a tensor family hold exactly when every factor obeys the bound. -/
theorem gomesFinitePolynomialTensorFold_degree_le_iff (P : GomesFinitePolynomialProfile)
    (L : List GomesFinitePolynomialProfile) (n : ℕ) :
    (gomesFinitePolynomialTensorFold P L).val.natDegree ≤ n ↔
      P.val.natDegree ≤ n ∧ ∀ Q ∈ L, Q.val.natDegree ≤ n := by
  induction L with
  | nil => simp [gomesFinitePolynomialTensorFold]
  | cons Q L ih =>
    change (Q.val + (gomesFinitePolynomialTensorFold P L).val).natDegree ≤ n ↔ _
    rw [gomesFinitePolynomialProfile_add_degree_le_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- Quadratic exceptional behavior survives a family exactly factor by factor. -/
theorem gomesFinitePolynomialTensorFold_quadratic_iff (P : GomesFinitePolynomialProfile)
    (L : List GomesFinitePolynomialProfile) :
    (gomesFinitePolynomialTensorFold P L).val.derivative.derivative.derivative = 0 ↔
      P.val.derivative.derivative.derivative = 0 ∧
        ∀ Q ∈ L, Q.val.derivative.derivative.derivative = 0 := by
  simp only [gomesPolynomial_third_derivative_zero_iff_degree,
    gomesFinitePolynomialTensorFold_degree_le_iff]

/-- The literal iterated Schwartz product is the ground state of the combined profile. -/
theorem gomesPolynomialGroundState_tensor_family (P : GomesFinitePolynomialProfile)
    (L : List GomesFinitePolynomialProfile) :
    L.foldr (fun Q ψ => mulS (gomesPolynomialGroundState Q) ψ)
      (gomesPolynomialGroundState P) =
        gomesPolynomialGroundState (gomesFinitePolynomialTensorFold P L) := by
  induction L with
  | nil => rfl
  | cons Q L ih =>
    simp only [List.foldr_cons, ih, gomesPolynomialGroundState_tensor]
    rfl

/-- A finite ground state admits a positive energy under some target exactly in the quadratic case. -/
theorem gomesPolynomialGroundState_positive_eigen_iff (P : GomesFinitePolynomialProfile) :
    (∃ (K : ℝ[X]) (e : ℝ), 0 < e ∧
      dilatonHamiltonianCLM K (gomesPolynomialGroundState P) =
        (e : ℂ) • gomesPolynomialGroundState P) ↔
      P.val.derivative.derivative.derivative = 0 := by
  constructor
  · rintro ⟨K, e, he, h⟩
    rcases (gomesPolynomialGroundState_eigen_profiles_iff P K e).mp h with ⟨_, hz⟩ | ⟨_, hd, _⟩
    · exact (ne_of_gt he hz).elim
    · rw [hd, derivative_C]
  · intro h
    let Q : {P : GomesFinitePolynomialProfile // P.val.derivative.derivative.derivative = 0} := ⟨P, h⟩
    exact ⟨-P.val, -P.val.derivative.derivative.eval 0,
      gomesPolynomialGroundState_quadratic_dual_eigen Q⟩

/-- A product of any nonempty finite family admits positive energy exactly when every factor is quadratic. -/
theorem gomesPolynomialGroundState_tensor_family_positive_eigen_iff
    (P : GomesFinitePolynomialProfile) (L : List GomesFinitePolynomialProfile) :
    (∃ (K : ℝ[X]) (e : ℝ), 0 < e ∧
      dilatonHamiltonianCLM K
        (L.foldr (fun Q ψ => mulS (gomesPolynomialGroundState Q) ψ) (gomesPolynomialGroundState P)) =
          (e : ℂ) • L.foldr (fun Q ψ => mulS (gomesPolynomialGroundState Q) ψ)
            (gomesPolynomialGroundState P)) ↔
      P.val.derivative.derivative.derivative = 0 ∧
        ∀ Q ∈ L, Q.val.derivative.derivative.derivative = 0 := by
  rw [gomesPolynomialGroundState_tensor_family,
    gomesPolynomialGroundState_positive_eigen_iff, gomesFinitePolynomialTensorFold_quadratic_iff]

/-- Every finite target compatible with a whole tensor family has its summed connection and zero energy. -/
theorem gomesPolynomialGroundState_tensor_family_finite_eigen_iff
    (P R : GomesFinitePolynomialProfile) (L : List GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM R.val
      (L.foldr (fun Q ψ => mulS (gomesPolynomialGroundState Q) ψ) (gomesPolynomialGroundState P)) =
        (e : ℂ) • L.foldr (fun Q ψ => mulS (gomesPolynomialGroundState Q) ψ)
          (gomesPolynomialGroundState P) ↔
      dilatonSuperchargeCLM (gomesFinitePolynomialTensorFold P L).val =
        dilatonSuperchargeCLM R.val ∧ e = 0 := by
  rw [gomesPolynomialGroundState_tensor_family]
  exact gomesPolynomialGroundState_finite_eigen_iff _ R e

end GaloisForLFunctions.HTGeometry
