import GaloisForLFunctions.HTGeometry.LinearWidthPrincipalSymbolCompletion

/-!
# Finite-dimensional linear holographic completion

The linear-width completion is not a coordinate phenomenon.  A linear equivalence from an
arbitrary law space to finite coordinates transports the completed pencil, its scalar identity,
and the injective exterior commutator symbol.  Choosing the canonical finite-dimensional basis
provided by mathlib gives a completion for every finite-dimensional law space `V`, with detector
width `d(2 finrank(V)+1)`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {V : Type w} [AddCommGroup V] [Module K V]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- Transport the finite-coordinate completion to an arbitrary linearly equivalent law space. -/
def coordinateFreeLinearWidthPrincipalSymbolCompletion
    (q : K) (hq : q ^ d = 1)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) :
    V →ₗ[K] Module.End K (LinearPrincipalCompletionState M n d) :=
  (linearWidthPrincipalSymbolCompletion q hq
    (A₀.comp e.symm.toLinearMap)).comp e.toLinearMap

/-- Coordinate transport preserves the represented scalar law exactly. -/
theorem coordinateFreeLinearWidthPrincipalSymbolCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id) (v : V) :
    (coordinateFreeLinearWidthPrincipalSymbolCompletion q hq.pow_eq_one e A₀ v) ^ d =
      F v • LinearMap.id := by
  have hcoord : ∀ c : Fin n → K,
      ((A₀.comp e.symm.toLinearMap) c) ^ d =
        F (e.symm c) • LinearMap.id := by
    intro c
    exact hA₀ (e.symm c)
  simpa [coordinateFreeLinearWidthPrincipalSymbolCompletion] using
    (linearWidthPrincipalSymbolCompletion_pow
      q hq hd (A₀.comp e.symm.toLinearMap) (fun c ↦ F (e.symm c)) hcoord (e v))

/-- Coordinate transport preserves maximal exterior principal-symbol rank. -/
theorem coordinateFreeLinearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (coordinateFreeLinearWidthPrincipalSymbolCompletion q hq.pow_eq_one e A₀)) := by
  rw [coordinateFreeLinearWidthPrincipalSymbolCompletion,
    endomorphismCommutatorMap_comp]
  exact
    (linearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
      q hq (A₀.comp e.symm.toLinearMap) m hm).comp
      (exteriorPower.map_injective_field (n := 2) e.injective)

/-- **Coordinate-free before-time horizon theorem.**  Every finite-coordinate presentation of a
law space gives the same exact scalar horizon and maximal exterior differential symbol. -/
theorem coordinateFreeLinearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (coordinateFreeLinearWidthPrincipalSymbolCompletion q hq.pow_eq_one e A₀ v)
          (linearPrincipalCompletionRoot (n := n) (d := d) m))} =
      {v : V | F v = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (coordinateFreeLinearWidthPrincipalSymbolCompletion q hq.pow_eq_one e A₀))) := by
  constructor
  · apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
      (coordinateFreeLinearWidthPrincipalSymbolCompletion q hq.pow_eq_one e A₀) F d
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
      (linearPrincipalCompletionRoot (n := n) (d := d) m)
      (linearPrincipalCompletionRoot_ne_zero m hm)
    exact coordinateFreeLinearWidthPrincipalSymbolCompletion_pow q hq hd e A₀ F hA₀
  · rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact
      coordinateFreeLinearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
        q hq e A₀ m hm

variable [FiniteDimensional K V]

/-- The chosen finite coordinate presentation of an arbitrary finite-dimensional law space. -/
def finiteDimensionalLawCoordinates :
    V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
  (Module.finBasis K V).equivFun

/-- The basis-free completion obtained from the chosen finite-dimensional coordinates. -/
def finiteDimensionalLinearHolographicCompletion
    (q : K) (hq : q ^ d = 1)
    (A₀ : V →ₗ[K] Module.End K M) :
    V →ₗ[K] Module.End K
      (LinearPrincipalCompletionState M (Module.finrank K V) d) :=
  coordinateFreeLinearWidthPrincipalSymbolCompletion
    q hq finiteDimensionalLawCoordinates A₀

/-- The basis-free completion preserves every represented degree-`d` scalar law for `d ≥ 3`. -/
theorem finiteDimensionalLinearHolographicCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id) (v : V) :
    (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀ v) ^ d =
      F v • LinearMap.id :=
  coordinateFreeLinearWidthPrincipalSymbolCompletion_pow
    q hq hd finiteDimensionalLawCoordinates A₀ F hA₀ v

/-- The basis-free completion has injective exterior commutator symbol. -/
theorem finiteDimensionalLinearHolographicCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : V →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀)) :=
  coordinateFreeLinearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    q hq finiteDimensionalLawCoordinates A₀ m hm

/-- The exact detector-coordinate count for a finite-dimensional law space. -/
theorem finiteDimensionalLinearHolographicCompletionCoordinate_card :
    Fintype.card
        (LinearWidthDetectorIndex (Module.finrank K V) × ZMod d) =
      (2 * Module.finrank K V + 1) * d :=
  linearPrincipalCompletionCoordinate_card

/-- **Finite-dimensional linear holographic horizon theorem.** -/
theorem finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀ v)
          (linearPrincipalCompletionRoot
            (n := Module.finrank K V) (d := d) m))} =
      {v : V | F v = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀))) :=
  coordinateFreeLinearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    q hq hd finiteDimensionalLawCoordinates A₀ F hA₀ m hm

end

end GaloisForLFunctions.HTGeometry
