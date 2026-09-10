import GaloisForLFunctions.HTGeometry.GomesFiniteCenteredPotentialFibers

/-!
# Which polynomial Hamiltonians admit a fixed canonical ground state as an eigenstate?

The energy-reference reconstruction experiment becomes a complete eigenstate inverse
problem. A finite profile's nowhere-zero canonical state can be an eigenstate of another
polynomial Hamiltonian only at zero energy in its own connection class, or at one positive
energy in the opposite quadratic class. All operators act on the actual Schwartz space.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- One canonical half-density eigenstate detects a scalar shift of the entire Hamiltonian. -/
theorem gomesPolynomialGroundState_eigen_shift_iff (P : GomesFinitePolynomialProfile) (K : ℝ[X]) (e : ℝ) :
    dilatonHamiltonianCLM K (gomesPolynomialGroundState P) = (e : ℂ) • gomesPolynomialGroundState P ↔
      gomesDilatonEnergyShift P.val K (-e) := by
  constructor
  · intro h
    apply (gomesDilatonEnergyShift_potential_iff P.val K (-e)).mpr
    intro x
    have hk := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) h
    have hp := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) (gomesPolynomialGroundState_kernel P)
    change dilatonHamiltonianCLM K (gomesPolynomialGroundState P) x =
      (e : ℂ) * gomesPolynomialGroundState P x at hk
    change dilatonHamiltonianCLM P.val (gomesPolynomialGroundState P) x = 0 at hp
    rw [dilatonHamiltonianCLM_apply] at hk hp
    have he : (dilatonPotential P.val x : ℂ) * gomesPolynomialGroundState P x =
        ((dilatonPotential K x : ℂ) - e) * gomesPolynomialGroundState P x := by
      linear_combination hp - hk
    have hc := mul_right_cancel₀ (gomesPolynomialGroundState_pointwise_ne_zero P x) he
    have hr : dilatonPotential P.val x = dilatonPotential K x - e := by exact_mod_cast hc
    simpa only [sub_eq_add_neg] using hr
  · intro h
    ext x
    have hs := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) (h (gomesPolynomialGroundState P))
    rw [gomesPolynomialGroundState_kernel] at hs
    change (0 : ℂ) = dilatonHamiltonianCLM K (gomesPolynomialGroundState P) x +
      ((-e : ℝ) : ℂ) * gomesPolynomialGroundState P x at hs
    change dilatonHamiltonianCLM K (gomesPolynomialGroundState P) x =
      (e : ℂ) * gomesPolynomialGroundState P x
    push_cast at hs
    linear_combination -hs

/-- The full inverse-eigenstate classification: zero in the original class or positive energy in the dual quadratic class. -/
theorem gomesPolynomialGroundState_eigen_profiles_iff (P : GomesFinitePolynomialProfile) (K : ℝ[X]) (e : ℝ) :
    dilatonHamiltonianCLM K (gomesPolynomialGroundState P) = (e : ℂ) • gomesPolynomialGroundState P ↔
      (dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM K ∧ e = 0) ∨
        (0 < e ∧ P.val.derivative.derivative = C (-e) ∧ ∃ c : ℝ, K = -P.val + C c) := by
  rw [gomesPolynomialGroundState_eigen_shift_iff, gomesFinitePolynomialEnergyShift_arbitrary_iff]
  simp only [neg_eq_zero, neg_lt_zero]

/-- A canonical finite-profile state can only have eigenvalue zero for another finite profile. -/
theorem gomesPolynomialGroundState_finite_eigen_iff (P Q : GomesFinitePolynomialProfile) (e : ℝ) :
    dilatonHamiltonianCLM Q.val (gomesPolynomialGroundState P) = (e : ℂ) • gomesPolynomialGroundState P ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val ∧ e = 0 := by
  rw [gomesPolynomialGroundState_eigen_shift_iff, gomesFinitePolynomialEnergyShift_iff]
  simp only [neg_eq_zero]

/-- All eigenvalues obtainable for this fixed half-density by varying the polynomial Hamiltonian. -/
def gomesPolynomialGroundStateEigenvalues (P : GomesFinitePolynomialProfile) : Set ℝ :=
  {e | ∃ K : ℝ[X], dilatonHamiltonianCLM K (gomesPolynomialGroundState P) =
    (e : ℂ) • gomesPolynomialGroundState P}

/-- Admissible eigenvalues are exactly the negatives of the admissible scalar energy offsets. -/
theorem gomesPolynomialGroundStateEigenvalues_mem_iff (P : GomesFinitePolynomialProfile) (e : ℝ) :
    e ∈ gomesPolynomialGroundStateEigenvalues P ↔ -e ∈ gomesFinitePolynomialEnergyOffsets P := by
  change (∃ K, _) ↔ ∃ K, _
  simp only [gomesPolynomialGroundState_eigen_shift_iff]

/-- Every eigenvalue of a fixed canonical half-density under any polynomial Hamiltonian is nonnegative. -/
theorem gomesPolynomialGroundStateEigenvalues_nonnegative (P : GomesFinitePolynomialProfile) :
    gomesPolynomialGroundStateEigenvalues P ⊆ Set.Ici 0 := by
  intro e h
  have he := gomesFinitePolynomialEnergyOffsets_nonpositive P
    ((gomesPolynomialGroundStateEigenvalues_mem_iff P e).mp h)
  change -e ≤ (0 : ℝ) at he
  change (0 : ℝ) ≤ e
  linarith

/-- The exact eigenvalue set is zero, with one extra positive value precisely for a finite quadratic. -/
theorem gomesPolynomialGroundStateEigenvalues_exact (P : GomesFinitePolynomialProfile) :
    gomesPolynomialGroundStateEigenvalues P =
      if P.val.derivative.derivative.derivative = 0
      then {0, -P.val.derivative.derivative.eval 0} else {0} := by
  classical
  ext e
  rw [gomesPolynomialGroundStateEigenvalues_mem_iff, gomesFinitePolynomialEnergyOffsets_exact]
  split_ifs <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_eq_iff_eq_neg, neg_zero]

/-- The dual quadratic Hamiltonian has this canonical state at a strictly positive, exactly measured energy. -/
theorem gomesPolynomialGroundState_quadratic_dual_eigen
    (P : {P : GomesFinitePolynomialProfile // P.val.derivative.derivative.derivative = 0}) :
    0 < -P.val.val.derivative.derivative.eval 0 ∧
      dilatonHamiltonianCLM (-P.val.val) (gomesPolynomialGroundState P.val) =
        ((-P.val.val.derivative.derivative.eval 0 : ℝ) : ℂ) • gomesPolynomialGroundState P.val := by
  obtain ⟨hk, hd⟩ := gomesFinitePolynomialProfile_quadratic_origin_curvature P
  refine ⟨neg_pos.mpr hk, ?_⟩
  apply (gomesPolynomialGroundState_eigen_profiles_iff P.val (-P.val.val) _).mpr
  exact Or.inr ⟨neg_pos.mpr hk, by simpa only [neg_neg] using hd, 0, by simp⟩

end GaloisForLFunctions.HTGeometry
