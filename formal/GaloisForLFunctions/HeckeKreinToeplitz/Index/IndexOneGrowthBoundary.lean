import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveHyperplaneQuadraticGrowth
import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubexponentialPositiveHyperplane

/-!
# The quadratic boundary at index one

For an abelian Hermitian kernel of negative index at most one, cyclic
subexponential growth is equivalent to a positive unitary-character mass
hyperplane and to cyclic quadratic growth. The unitary hyperplane supplies
the quadratic bound; the reflected-pair dichotomy supplies the converse.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- At index one, cyclic subexponential growth is exactly the unitary-hyperplane case. -/
theorem cyclic_subexponential_iff_unitary_positive_hyperplane
    (hk : IsHermKernel k) (hi : negIndex k ≤ 1) :
    (∀ (g : G) (ε : ℝ), 0 < ε →
      ∃ C : ℝ, ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * Real.exp (ε * n)) ↔
    ∃ χ : G →* ℂ, IsUnitaryChar χ ∧ ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c := by
  constructor
  · exact exists_unitary_positive_hyperplane_of_cyclic_subexponential hk hi
  · rintro ⟨χ, hχ, hpos⟩ g ε hε
    obtain ⟨C, hC, hbound⟩ := cyclic_quadratic_of_positive_unitary_hyperplane hk χ hχ hpos g
    exact subexponential_of_quadratic_bound (fun n => k (g ^ n)) hC hbound hε

/-- Every cyclic subexponential index-one kernel in fact has cyclic quadratic growth. -/
theorem cyclic_subexponential_iff_quadratic
    (hk : IsHermKernel k) (hi : negIndex k ≤ 1) :
    (∀ (g : G) (ε : ℝ), 0 < ε →
      ∃ C : ℝ, ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * Real.exp (ε * n)) ↔
    ∀ g : G, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖k (g ^ n)‖ ≤ C * ((n : ℝ) + 1) ^ 2 := by
  constructor
  · intro hsub
    obtain ⟨χ, hχ, hpos⟩ := exists_unitary_positive_hyperplane_of_cyclic_subexponential hk hi hsub
    exact cyclic_quadratic_of_positive_unitary_hyperplane hk χ hχ hpos
  · intro hquad g ε hε
    obtain ⟨C, hC, hbound⟩ := hquad g
    exact subexponential_of_quadratic_bound (fun n => k (g ^ n)) hC hbound hε

#print axioms cyclic_subexponential_iff_unitary_positive_hyperplane
#print axioms cyclic_subexponential_iff_quadratic

end GaloisForLFunctions.HeckeKreinToeplitz
