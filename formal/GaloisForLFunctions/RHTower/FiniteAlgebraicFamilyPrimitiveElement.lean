import Mathlib

open Polynomial
open scoped Classical

namespace GaloisForLFunctions.RHTower

/-- A finite algebraic family lies in one simple number field and therefore has simultaneous
polynomial coordinates in one algebraic primitive element. -/
theorem exists_primitive_polynomial_representation {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ θ : ℂ, ∃ q : ι → ℚ[X], IsAlgebraic ℚ θ ∧
      (∀ i, (q i).natDegree < (minpoly ℚ θ).natDegree) ∧
      ∀ i, α i = Polynomial.aeval θ (q i) := by
  classical
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  letI : Finite (Set.range α) := Set.finite_range α
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with ⟨i, rfl⟩
    exact (hα i).isIntegral
  let pb : PowerBasis ℚ K := Field.powerBasisOfFiniteOfSeparable ℚ K
  let αK : ι → K := fun i =>
    ⟨α i, IntermediateField.subset_adjoin ℚ (Set.range α) (Set.mem_range_self i)⟩
  choose q hqdeg hq using fun i => pb.exists_eq_aeval (αK i)
  let θ : ℂ := algebraMap K ℂ pb.gen
  have hθalg : IsAlgebraic ℚ θ := by
    exact (Algebra.IsAlgebraic.isAlgebraic pb.gen).algHom (IsScalarTower.toAlgHom ℚ K ℂ)
  have hmin : minpoly ℚ θ = minpoly ℚ pb.gen := by
    simpa [θ] using minpoly.algebraMap_eq (algebraMap K ℂ).injective pb.gen
  refine ⟨θ, q, hθalg, ?_, ?_⟩
  · intro i
    rw [hmin, pb.natDegree_minpoly]
    exact hqdeg i
  · intro i
    have hi := congrArg (algebraMap K ℂ) (hq i)
    simpa [αK, θ, ← Polynomial.aeval_algHom_apply] using hi

end GaloisForLFunctions.RHTower
