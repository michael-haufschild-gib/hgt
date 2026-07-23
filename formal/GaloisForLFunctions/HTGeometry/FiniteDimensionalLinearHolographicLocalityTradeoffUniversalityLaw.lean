import GaloisForLFunctions.HTGeometry.FiniteDimensionalLinearHolographicCompletion
import GaloisForLFunctions.HTGeometry.HolographicLocalityBound

/-!
# Finite-dimensional linear holography versus bounded membrane locality

The coordinate-free completion achieves exact horizon recovery and maximal exterior symbol with
linear detector width, while every bounded-valence membrane presentation of its canonical
coordinate model must pay the universal two-plane covering bound.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {d : ℕ} [NeZero d] [Fact (1 < d)]
  {H : Type*} [Fintype H]

/-- Canonical finite-coordinate symbol before transport back to the law space. -/
def finiteDimensionalLinearHolographicCoordinateSymbol
    (q : K) (hq : q ^ d = 1)
    (A₀ : V →ₗ[K] Module.End K M) :
    (Fin (Module.finrank K V) → K) →ₗ[K]
      Module.End K
        (LinearPrincipalCompletionState M (Module.finrank K V) d) :=
  linearWidthPrincipalSymbolCompletion q hq
    (A₀.comp finiteDimensionalLawCoordinates.symm.toLinearMap)

/-- **Finite-dimensional linear holographic locality tradeoff.** Exact scalar horizon,
maximal exterior symbol, and linear detector width coexist with the quadratic bounded-locality
covering obstruction in canonical coordinates. -/
theorem finiteDimensionalLinearHolographicCompletion_localityTradeoffUniversality
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id)
    (m : M) (hm : m ≠ 0)
    (support : H → Finset (Fin (Module.finrank K V))) (Δ : ℕ)
    (hmembrane :
      MembraneLocalPrincipalBrackets
        (finiteDimensionalLinearHolographicCoordinateSymbol
          q hq.pow_eq_one A₀)
        support)
    (hlocal : MembraneValenceAtMost support Δ) :
    (({v : V | ¬ AlgebraicIndependent K
          (generalizedCliffordShiftFieldJet
            (finiteDimensionalLinearHolographicCompletion
              q hq.pow_eq_one A₀ v)
            (linearPrincipalCompletionRoot
              (n := Module.finrank K V) (d := d) m))} =
        {v : V | F v = 0}) ∧
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw
            (finiteDimensionalLinearHolographicCompletion
              q hq.pow_eq_one A₀)))) ∧
    Fintype.card
        (LinearWidthDetectorIndex (Module.finrank K V) × ZMod d) =
      (2 * Module.finrank K V + 1) * d ∧
    MembranePairComplete support ∧
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card H * Nat.choose Δ 2 := by
  have hhorizon :=
    finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq hd A₀ F hA₀ m hm
  have hLI :
      LinearIndependent K
        (principalBracketPair
          (finiteDimensionalLinearHolographicCoordinateSymbol
            q hq.pow_eq_one A₀)) := by
    exact
      linearWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
        q hq (A₀.comp finiteDimensionalLawCoordinates.symm.toLinearMap) m hm
  have hcomplete : MembranePairComplete support :=
    membranePairComplete_of_principalBracketPair_linearIndependent
      (finiteDimensionalLinearHolographicCoordinateSymbol
        q hq.pow_eq_one A₀)
      support hmembrane hLI
  exact ⟨hhorizon,
    finiteDimensionalLinearHolographicCompletionCoordinate_card,
    hcomplete,
    by
      simpa using holographicLocality_choose_bound support Δ hcomplete hlocal⟩

end

end GaloisForLFunctions.HTGeometry
