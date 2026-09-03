import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpUniformizerPowerLength
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Noncommutative product quotients and diagonal uniformizer lengths

Mathlib's coordinatewise quotient equivalence assumes a commutative scalar ring.  The completed
pseudodifferential valuation ring is noncommutative, so this leaf constructs the left-module
equivalence directly.  Applying it to coordinatewise uniformizer powers makes quotient length the
sum of the coordinate exponents.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- Coordinate quotient map for a family of submodules over an arbitrary scalar ring. -/
def noncommutativePiQuotientMap {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : ι → Submodule R M) :
    (ι → M) →ₗ[R] (∀ i, M ⧸ p i) where
  toFun x i := Submodule.Quotient.mk (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate quotient map descended through the product submodule. -/
def noncommutativeQuotientPiLinearMap {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : ι → Submodule R M) :
    ((ι → M) ⧸ Submodule.pi Set.univ p) →ₗ[R] (∀ i, M ⧸ p i) :=
  Submodule.liftQ (Submodule.pi Set.univ p) (noncommutativePiQuotientMap p) (by
    intro x hx
    rw [LinearMap.mem_ker]
    funext i
    change Submodule.Quotient.mk (p := p i) (x i) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx i (Set.mem_univ i))

/-- The descended coordinate quotient map is injective. -/
theorem noncommutativeQuotientPiLinearMap_injective {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : ι → Submodule R M) :
    Function.Injective (noncommutativeQuotientPiLinearMap p) := by
  intro q q'
  refine Submodule.Quotient.induction_on (Submodule.pi Set.univ p) q ?_
  intro x
  refine Submodule.Quotient.induction_on (Submodule.pi Set.univ p) q' ?_
  intro y hxy
  rw [Submodule.Quotient.eq]
  intro i _
  change (fun i => Submodule.Quotient.mk (p := p i) (x i)) =
    (fun i => Submodule.Quotient.mk (p := p i) (y i)) at hxy
  exact (Submodule.Quotient.eq (p i)).1 (congrFun hxy i)

/-- The descended coordinate quotient map is surjective. -/
theorem noncommutativeQuotientPiLinearMap_surjective {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : ι → Submodule R M) :
    Function.Surjective (noncommutativeQuotientPiLinearMap p) := by
  intro y
  choose x hx using fun i => Submodule.Quotient.mk_surjective (p i) (y i)
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  change (fun i => Submodule.Quotient.mk (p := p i) (x i)) = y
  funext i
  exact hx i

/-- A quotient by a coordinatewise product submodule is the product of coordinate quotients,
over an arbitrary, possibly noncommutative, scalar ring. -/
def noncommutativeQuotientPiLinearEquiv {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (p : ι → Submodule R M) :
    ((ι → M) ⧸ Submodule.pi Set.univ p) ≃ₗ[R] (∀ i, M ⧸ p i) :=
  LinearEquiv.ofBijective (noncommutativeQuotientPiLinearMap p)
    ⟨noncommutativeQuotientPiLinearMap_injective p, noncommutativeQuotientPiLinearMap_surjective p⟩

variable [Fintype ι]

/-- Coordinatewise product of completed uniformizer-power lattices. -/
def completedPseudoDiffOpUniformizerPowerPi (n : ι → ℕ) : Submodule (CompletedPseudoDiffOpInteger (K := K)) (ι → CompletedPseudoDiffOpInteger (K := K)) :=
  Submodule.pi Set.univ fun i => completedPseudoDiffOpUniformizerPower (K := K) (n i)

/-- The quotient by coordinatewise powers has length equal to the sum of their exponents. -/
theorem completedPseudoDiffOpUniformizerPowerPiQuotient_length (n : ι → ℕ) :
    Module.length (CompletedPseudoDiffOpInteger (K := K)) ((ι → CompletedPseudoDiffOpInteger (K := K)) ⧸ completedPseudoDiffOpUniformizerPowerPi (K := K) n) =
      ∑ i, n i := by
  unfold completedPseudoDiffOpUniformizerPowerPi
  calc
    Module.length (CompletedPseudoDiffOpInteger (K := K))
        ((ι → CompletedPseudoDiffOpInteger (K := K)) ⧸ Submodule.pi Set.univ
          (fun i => completedPseudoDiffOpUniformizerPower (K := K) (n i))) =
      Module.length (CompletedPseudoDiffOpInteger (K := K))
        (∀ i : ι, CompletedPseudoDiffOpInteger (K := K) ⧸ completedPseudoDiffOpUniformizerPower (K := K) (n i)) :=
      (noncommutativeQuotientPiLinearEquiv
        (fun i => completedPseudoDiffOpUniformizerPower (K := K) (n i))).length_eq
    _ = ∑ i, Module.length (CompletedPseudoDiffOpInteger (K := K))
        (CompletedPseudoDiffOpInteger (K := K) ⧸ completedPseudoDiffOpUniformizerPower (K := K) (n i)) :=
      Module.length_pi_of_fintype (CompletedPseudoDiffOpInteger (K := K))
        (fun i : ι => CompletedPseudoDiffOpInteger (K := K) ⧸ completedPseudoDiffOpUniformizerPower (K := K) (n i))
    _ = ∑ i, n i := by
      simp_rw [completedPseudoDiffOpUniformizerPowerQuotient_length]
      norm_cast

end

end GaloisForLFunctions.HTGeometry.DiffOp
