import GaloisForLFunctions.HTGeometry.MinimalHTCompletionArchitecture
import GaloisForLFunctions.RHTower.UniversalHybridBlindXiZeroHurwitzFaithfulObservableNonuniformityLaw

/-!
# Universal hybrid Krein/Xi-Hurwitz observable nonuniformity

The hybrid blind/faithful observable law and the minimal HT prime-polarization architecture share
the same prime chamber.  At the empty reference chamber, Hamming defect equals exact negative
Krein inertia dimension, while completed rings remain blind and Xi-Hurwitz nets remain faithful.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential TensorProduct

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

local instance : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra
local instance : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Blind-side field/ring equivalence, exact Krein discrimination, and faithful Xi-Hurwitz
factorization under one observable-field functor. -/
structure UniversalHybridKreinXiHurwitzObservableNonuniformityCertificate
    (k : ℕ) (J : Finset Nat.Primes)
    (resolution : UniversalFacetOrbitIndex → ℕ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) : Prop where
  sameObservableField :
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitOrientedSource
            (universalOrientationSupport k) (universalOrientationSupport k)) resolution =
      differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitPrimeOrientedSource J) resolution
  completedRingBlindness :
    ∀ ε δ : Nat.Primes → Bool,
      primeOrientationCompletedRing ε = primeOrientationCompletedRing δ
  exactNegativeInertia :
    PrimeChamberExactNegativeInertia J ∅
  exactPositiveInertia :
    PrimeChamberExactPositiveInertia J ∅
  defectEqIndexAddNegativeInertiaDimension :
    universalHybridOrientationDephasingDefect k J =
      (k : ℝ) + (J.card : ℝ)
  herglotzIffTrivialChamber :
    ((∀ z : ℂ, 0 < z.im →
        0 ≤ (universalOrientedHerglotz
          (universalOrientationSupport k) (universalOrientationSupport k) z).im) ∧
      (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im)) ↔
        k = 0 ∧ J = ∅
  xiResolutionOrderReflecting :
    ∀ M N : I → ℕ,
      differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M ≤
          differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
        M ≤ N
  xiResolutionReconstructing :
    ∀ M N : I → ℕ,
      differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) M =
          differentialFamilyObservableField (RatFunc ℂ)
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N ↔
        M = N
  xiDisjointFactorization :
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
            (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) N)

/-- **Universal hybrid Krein/Xi-Hurwitz observable nonuniformity law.** -/
theorem universalHybrid_kreinXiHurwitzObservableNonuniformity
    (k : ℕ) (J : Finset Nat.Primes)
    (resolution : UniversalFacetOrbitIndex → ℕ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ) :
    UniversalHybridKreinXiHurwitzObservableNonuniformityCertificate
      k J resolution ρ := by
  have hhybrid :=
    universalHybridBlind_xiZeroHurwitzFaithfulObservableNonuniformity
      k J resolution ρ hρ
  have hpolar := primeOrientationBlindnessAndPolarization
  have hinertia := hpolar.2.2 J ∅
  refine
    ⟨hhybrid.1, hpolar.2.1, hinertia.1, hinertia.2.1, ?_, ?_,
      hhybrid.2.2.1, hhybrid.2.2.2.1, hhybrid.2.2.2.2⟩
  · calc
      universalHybridOrientationDephasingDefect k J =
          (k : ℝ) + (primeChamberHammingDistance J ∅ : ℝ) :=
        hhybrid.2.1.2
      _ = (k : ℝ) + (J.card : ℝ) := by
        simp [primeChamberHammingDistance]
  · exact hhybrid.2.1.1.trans
      (universalHybridOrientationDephasingDefect_eq_zero_iff k J)

end

end RHTower
