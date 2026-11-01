import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianFiniteSums

/-!
# Finite spaces of pairing functions

Pairing a finite-dimensional subspace against an arbitrary family gives
a function space of no larger dimension. Conjugating basis coefficients
converts the conjugate-linear dependence into an ordinary linear synthesis.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {G H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem pairing_submodule_basis_sum {ι : Type*} [Fintype ι]
    (U : Submodule ℂ (H × E)) (b : ι → U) (c : ι → ℂ) (v : H × E) :
    pairing ((∑ i, c i • b i : U) : H × E) v =
      ∑ i, conj (c i) * pairing (b i : H × E) v := by
  change pairing (U.subtype (∑ i, c i • b i)) v = _
  rw [map_sum]
  rw [hermitianForm_sum_right isHermitianForm_reverse_pairing]
  simp only [map_smul, pairing_smul_left]
  rfl

/-- Pairings against a finite subspace form a finite-dimensional function space. -/
theorem exists_finite_pairing_function_space
    (U : Submodule ℂ (H × E)) [FiniteDimensional ℂ U] (z : G → H × E) :
    ∃ Φ : Submodule ℂ (G → ℂ), FiniteDimensional ℂ Φ ∧ finrank ℂ Φ ≤ finrank ℂ U ∧
      ∀ f : G → ℂ, f ∈ Φ ↔ ∃ u : U, f = fun g => pairing (u : H × E) (z g) := by
  classical
  let b := Module.finBasis ℂ U
  let F : (Fin (finrank ℂ U) → ℂ) →ₗ[ℂ] (G → ℂ) :=
    Fintype.linearCombination ℂ (fun i g => pairing (b i : H × E) (z g))
  have hF (c : Fin (finrank ℂ U) → ℂ) (g : G) :
      F c g = ∑ i, c i * pairing (b i : H × E) (z g) := by
    simp only [F, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨F.range, inferInstance, ?_, ?_⟩
  · simpa using F.finrank_range_le
  · intro f
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨∑ i, conj (c i) • b i, ?_⟩
      funext g
      rw [hF, pairing_submodule_basis_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun a : ℂ => a * pairing (b i : H × E) (z g))
        (show c i = conj (conj (c i)) from (star_star (c i)).symm)
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => conj (b.repr u i), ?_⟩
      funext g
      rw [hF]
      rw [← pairing_submodule_basis_sum, b.sum_repr]

#print axioms exists_finite_pairing_function_space

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
