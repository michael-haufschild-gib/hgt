import GaloisForLFunctions.RHTower.XiZeroHurwitzObservableFactorization
import GaloisForLFunctions.RHTower.XiZeroHurwitzObservableNet

/-!
# Xi-zero Hurwitz factorizing observable-net universality

The Xi-zero-labelled Hurwitz observable-field map is simultaneously an order embedding and a
factorizing net: it reconstructs every finite jet-resolution vector, while disjoint supports give
linearly disjoint fields with coefficient-field intersection and domain tensor product.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential TensorProduct

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- **Factorizing faithful observable-net law.**  The Xi-zero Hurwitz field map reflects the full
resolution poset and converts disjoint coordinate supports into algebraically factorized fields. -/
theorem xiZeroHurwitz_factorizingFaithfulObservableNet
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    (∀ M N : I → ℕ,
      differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ≤
          differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
        M ≤ N) ∧
      (∀ M N : I → ℕ,
        differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M =
            differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
          M = N) ∧
      ∀ M N : I → ℕ, (∀ i, M i = 0 ∨ N i = 0) →
        (differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M).LinearDisjoint
          (differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N) ∧
        differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ⊓
            differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N = ⊥ ∧
        IsDomain
          (differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ⊗[RatFunc ℂ]
            differentialFamilyObservableField (RatFunc ℂ)
              (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  refine ⟨?_, ?_, ?_⟩
  · intro M N
    exact xiZeroHurwitz_familyObservableField_le_iff ρ hρ M N
  · intro M N
    exact xiZeroHurwitz_familyObservableField_eq_iff ρ hρ M N
  · intro M N hdisjoint
    exact ⟨xiZeroHurwitz_disjoint_familyObservableFields_linearDisjoint
        ρ hρ M N hdisjoint,
      xiZeroHurwitz_disjoint_familyObservableFields_inf_eq_bot
        ρ hρ M N hdisjoint,
      xiZeroHurwitz_disjoint_familyObservableFields_tensor_isDomain
        ρ hρ M N hdisjoint⟩

end


end RHTower
