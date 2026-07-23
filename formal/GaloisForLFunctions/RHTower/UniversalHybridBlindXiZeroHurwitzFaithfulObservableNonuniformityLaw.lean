import GaloisForLFunctions.HTGeometry.UniversalHybridObservableBlindnessDefectUniversalityLaw
import GaloisForLFunctions.RHTower.XiZeroHurwitzFactorizingObservableNetUniversalityLaw

/-!
# Hybrid-blind / Xi-zero-Hurwitz-faithful observable nonuniformity

The same finite differential observable-field construction behaves in opposite exact ways on two
source classes.  Universal orientation/prime-residue chambers remain field-indistinguishable while
their joint Herglotz defect records the hidden chamber.  Xi-zero-labelled Hurwitz jets instead
reflect their full resolution order, reconstruct equal resolutions, and tensor-factorize disjoint
coordinate sectors.

Thus finite differential observation is neither intrinsically faithful nor intrinsically blind:
source geometry decides which extreme occurs.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential TensorProduct

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- **Hybrid-blind / Xi-zero-Hurwitz-faithful observable nonuniformity law.**  Under one
coefficient field and one observable-field functor, universal gauge chambers are invisible at
every finite resolution, whereas injective Xi-zero Hurwitz nets are order-reflecting and
factorizing. -/
theorem universalHybridBlind_xiZeroHurwitzFaithfulObservableNonuniformity
    (k : ℕ) (J : Finset Nat.Primes)
    (resolution : UniversalFacetOrbitIndex → ℕ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ) :
    let S := universalOrientationSupport k
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitOrientedSource S S) resolution =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource J) resolution ∧
      ((((∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S S z).im) ∧
            (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im)) ↔
          universalHybridOrientationDephasingDefect k J = 0) ∧
        universalHybridOrientationDephasingDefect k J =
          (k : ℝ) + (primeChamberHammingDistance J ∅ : ℝ)) ∧
      ((∀ M N : I → ℕ,
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
                (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N)) := by
  dsimp only
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  have hblind :=
    universalHybridChamber_sameObservableField_Herglotz_iff_defect_zero
      k J resolution
  have hfaithful := xiZeroHurwitz_factorizingFaithfulObservableNet ρ hρ
  exact ⟨hblind.1, hblind.2, hfaithful⟩

end

end RHTower
