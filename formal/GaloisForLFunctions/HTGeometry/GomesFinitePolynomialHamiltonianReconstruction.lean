import GaloisForLFunctions.HTGeometry.GomesNormalizedFiniteMomentReconstruction

/-!
# Finite moment observations reconstruct the polynomial Hamiltonian

In the finite polynomial sector, the unique nonzero ground line reconstructs the
shared connection from the Hamiltonian itself. Combining this with finite moment
identifiability shows that a bounded list of normalized moments determines the full
Schwartz Hamiltonian and its scalar potential.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Equality of Schwartz Hamiltonians is exactly equality of their scalar potentials. -/
theorem gomesDilatonHamiltonian_potential_eq_iff (H K : ℝ[X]) :
    dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ↔ dilatonPotential H = dilatonPotential K := by
  constructor
  · intro h
    funext x
    have hx := congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T gaussianSchwartz x) h
    rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply] at hx
    have he : (dilatonPotential H x : ℂ) * gaussianSchwartz x =
        (dilatonPotential K x : ℂ) * gaussianSchwartz x := by
      linear_combination hx
    have hg : gaussianSchwartz x ≠ 0 := by
      rw [gaussianSchwartz_apply]
      exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
    exact Complex.ofReal_inj.mp (mul_right_cancel₀ hg he)
  · intro h
    ext ψ x
    rw [dilatonHamiltonianCLM_apply, dilatonHamiltonianCLM_apply, congrFun h x]

/-- A finite polynomial Hamiltonian reconstructs its induced first-order connection. -/
theorem gomesFinitePolynomialHamiltonian_connection_iff (P Q : GomesFinitePolynomialProfile) :
    dilatonHamiltonianCLM P.val = dilatonHamiltonianCLM Q.val ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  constructor
  · intro h
    have hk : dilatonHamiltonianCLM Q.val (gomesPolynomialGroundState P) = 0 := by
      rw [← h]
      exact gomesPolynomialGroundState_kernel P
    obtain ⟨c, hc⟩ := (gomesPolynomialGroundState_kernel_span Q (gomesPolynomialGroundState P)).mp hk
    have hn : c ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hc
      exact gomesPolynomialGroundState_ne_zero P hc
    exact (gomesPolynomialGroundState_projective_connection_iff P Q).mp ⟨c, hn, hc⟩
  · intro h
    obtain ⟨c, hc⟩ := (gomesDilatonConnection_constant_iff P.val Q.val).mp h
    rw [hc, gomesDilatonHamiltonian_constant]

/-- A scalar potential determines exactly one finite-profile connection class. -/
theorem gomesFinitePolynomialPotential_connection_iff (P Q : GomesFinitePolynomialProfile) :
    dilatonPotential P.val = dilatonPotential Q.val ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [← gomesDilatonHamiltonian_potential_eq_iff, gomesFinitePolynomialHamiltonian_connection_iff]

/-- Equal finite-profile Hamiltonians have exactly the same canonical ground line. -/
theorem gomesFinitePolynomialHamiltonian_ground_iff (P Q : GomesFinitePolynomialProfile) :
    dilatonHamiltonianCLM P.val = dilatonHamiltonianCLM Q.val ↔
      ∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q := by
  rw [gomesFinitePolynomialHamiltonian_connection_iff,
    gomesPolynomialGroundState_projective_connection_iff]

/-- The Hamiltonian determines the canonical normalized log-profile exactly. -/
theorem gomesFinitePolynomialHamiltonian_canonical_iff (P Q : GomesFinitePolynomialProfile) :
    dilatonHamiltonianCLM P.val = dilatonHamiltonianCLM Q.val ↔
      gomesFinitePolynomialNormalizedProfile P = gomesFinitePolynomialNormalizedProfile Q := by
  rw [gomesFinitePolynomialHamiltonian_connection_iff,
    gomesFinitePolynomialNormalizedProfile_eq_iff, gomesFinitePolynomialProfile_normalized_eq_iff,
    gomesDilatonConnection_constant_iff]

/-- Positive moments through the degree cutoff reconstruct the entire Schwartz Hamiltonian. -/
theorem gomesFinitePolynomialProfile_finite_moments_hamiltonian_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, 0 < n → n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      dilatonHamiltonianCLM P.val = dilatonHamiltonianCLM Q.val := by
  rw [gomesFinitePolynomialProfile_positive_finite_moments_connection_iff,
    gomesFinitePolynomialHamiltonian_connection_iff]

/-- The same finite moments reconstruct the full scalar potential pointwise. -/
theorem gomesFinitePolynomialProfile_finite_moments_potential_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, 0 < n → n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      dilatonPotential P.val = dilatonPotential Q.val := by
  rw [gomesFinitePolynomialProfile_finite_moments_hamiltonian_iff,
    gomesDilatonHamiltonian_potential_eq_iff]

/-- A fixed finite moment vector has exactly the Hamiltonian equivalence kernel. -/
theorem gomesBoundedPolynomialNormalizedRecord_hamiltonian_iff
    (d : ℕ) (P Q : GomesBoundedPolynomialProfile d) :
    gomesBoundedPolynomialNormalizedRecord d P = gomesBoundedPolynomialNormalizedRecord d Q ↔
      dilatonHamiltonianCLM P.val.val = dilatonHamiltonianCLM Q.val.val := by
  rw [gomesBoundedPolynomialNormalizedRecord_eq_iff, gomesFinitePolynomialHamiltonian_connection_iff]

end GaloisForLFunctions.HTGeometry
