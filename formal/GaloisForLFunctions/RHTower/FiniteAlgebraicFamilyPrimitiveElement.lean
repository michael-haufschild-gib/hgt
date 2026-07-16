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

/-- A finite algebraic family admits simultaneous rational-polynomial coordinates in one
**algebraic-integer** primitive element.  Scaling an arbitrary primitive generator by a nonzero
integer preserves the generated number field; rebuilding the power basis at the scaled generator
keeps the strict minimal-polynomial degree bounds. -/
theorem exists_integral_primitive_polynomial_representation {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ θ : ℂ, ∃ q : ι → ℚ[X], IsIntegral ℤ θ ∧
      (∀ i, (q i).natDegree < (minpoly ℚ θ).natDegree) ∧
      ∀ i, α i = Polynomial.aeval θ (q i) := by
  classical
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  letI : Finite (Set.range α) := Set.finite_range α
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with ⟨i, rfl⟩
    exact (hα i).isIntegral
  let pb : PowerBasis ℚ K := Field.powerBasisOfFiniteOfSeparable ℚ K
  have hgenZ : IsAlgebraic ℤ pb.gen :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (Algebra.IsAlgebraic.isAlgebraic pb.gen)
  obtain ⟨y, hy0, hyint⟩ := hgenZ.exists_integral_multiple
  let θK : K := y • pb.gen
  have hθKQ : IsIntegral ℚ θK :=
    (Algebra.IsAlgebraic.isAlgebraic θK).isIntegral
  have htop : Algebra.adjoin ℚ ({θK} : Set K) = ⊤ := by
    apply pb.adjoin_eq_top_of_gen_mem_adjoin
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy0
    have hθKcast : θK = (y : ℚ) • pb.gen := by
      simp [θK, Algebra.smul_def]
    have hgen : pb.gen = (y : ℚ)⁻¹ • θK := by
      rw [hθKcast, smul_smul, inv_mul_cancel₀ hyQ, one_smul]
    rw [hgen]
    exact Subalgebra.smul_mem _
      (Algebra.subset_adjoin (Set.mem_singleton θK)) _
  let pb' : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hθKQ htop
  let αK : ι → K := fun i =>
    ⟨α i, IntermediateField.subset_adjoin ℚ (Set.range α) (Set.mem_range_self i)⟩
  choose q hqdeg hq using fun i => pb'.exists_eq_aeval (αK i)
  let θ : ℂ := algebraMap K ℂ pb'.gen
  have hθint : IsIntegral ℤ θ := by
    have hgen : pb'.gen = θK := PowerBasis.ofAdjoinEqTop_gen hθKQ htop
    change IsIntegral ℤ (algebraMap K ℂ pb'.gen)
    rw [hgen]
    have hθKint : IsIntegral ℤ θK := by simpa [θK] using hyint
    exact hθKint.map (IsScalarTower.toAlgHom ℤ K ℂ)
  have hmin : minpoly ℚ θ = minpoly ℚ pb'.gen := by
    simpa [θ] using minpoly.algebraMap_eq (algebraMap K ℂ).injective pb'.gen
  refine ⟨θ, q, hθint, ?_, ?_⟩
  · intro i
    rw [hmin, pb'.natDegree_minpoly]
    exact hqdeg i
  · intro i
    have hi := congrArg (algebraMap K ℂ) (hq i)
    simpa [αK, θ, ← Polynomial.aeval_algHom_apply] using hi

end GaloisForLFunctions.RHTower
