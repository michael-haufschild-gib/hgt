import GaloisForLFunctions.RHTower.DeningerCompletedXiHellingerGammaCofaceClosedSaturation
import GaloisForLFunctions.RHTower.DeningerCalderonWittResolvedCrossEffectBoundary

/-!
# Resolved-provenance completion of the Xi Hellinger--Gamma coface

The ordinary completed Hodge coface loses its relative quotient away from
zero displacement: its closed range saturation is the whole two-channel
carrier.  This file constructs the minimal graph lift forced by that
obstruction.  Each balanced Hodge vertex is paired with its unchanged
completed Xi incidence source before adjacent differences are formed.

The Hodge endpoint still tends to zero, but the joined vertex tends to the
nonzero vertical provenance `(0,x)`.  Adjacent cofaces have zero provenance,
so the continuous provenance projection descends through their closed span.
The induced source map into the relative quotient has this descended map as
a left inverse and is therefore injective for every displacement.

Finite divisor coordinates decode the retained channel to the actual
Calderón--Witt antidiagonal resolved defect.  Thus this is a source-resolved
graph lift, not an extra scalar label.  It closes the quotient-faithfulness
gate for the Hellinger coface itself; comparison with the actual global
Green resolved range and Hermitian descent remain separate obligations.
-/

open Complex Set Finset Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open CompletedXiHellingerGammaPureHodgeCoface

abbrev HellingerGammaResolvedProvenanceCofaceCompletion
    (p q : Nat.Primes) (hpq : p ≠ q) :=
  HellingerGammaPureHodgeXiCofaceCompletion p q hpq ×
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq

def hellingerGammaResolvedProvenanceVertex
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    HellingerGammaResolvedProvenanceCofaceCompletion p q hpq :=
  (hellingerGammaCompletedBalancedPrimitive hpq a n x, x)

def hellingerGammaResolvedProvenanceAdjacentCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    HellingerGammaResolvedProvenanceCofaceCompletion p q hpq :=
  hellingerGammaResolvedProvenanceVertex hpq a (n + 1) x -
    hellingerGammaResolvedProvenanceVertex hpq a n x

@[simp]
theorem hellingerGammaResolvedProvenanceAdjacentCoface_eq
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceAdjacentCoface hpq a n x =
      (hellingerGammaCompletedAdjacentCoface hpq a n x, 0) := by
  simp [hellingerGammaResolvedProvenanceAdjacentCoface,
    hellingerGammaResolvedProvenanceVertex,
    hellingerGammaCompletedAdjacentCoface]

theorem hellingerGammaResolvedProvenanceVertex_tendsto
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    Tendsto
      (fun n : ℕ => hellingerGammaResolvedProvenanceVertex hpq a n x)
      atTop (𝓝 (0, x)) := by
  exact
    (hellingerGammaCompletedBalancedPrimitive_tendsto_zero hpq a x).prodMk_nhds
      tendsto_const_nhds

def hellingerGammaResolvedProvenanceProjection
    {p q : Nat.Primes} {hpq : p ≠ q} :
    HellingerGammaResolvedProvenanceCofaceCompletion p q hpq →L[ℂ]
      DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  ContinuousLinearMap.snd ℂ
    (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
    (DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)

def hellingerGammaResolvedProvenanceInsertion
    {p q : Nat.Primes} {hpq : p ≠ q} :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq →ₗ[ℂ]
      HellingerGammaResolvedProvenanceCofaceCompletion p q hpq where
  toFun := fun x => (0, x)
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem hellingerGammaResolvedProvenanceProjection_insertion
    {p q : Nat.Primes} {hpq : p ≠ q}
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceProjection
        (hellingerGammaResolvedProvenanceInsertion x) = x :=
  rfl

def hellingerGammaResolvedProvenanceAdjacentCofaceSet
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    Set (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq) :=
  {z | ∃ (n : ℕ)
      (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq),
    z = hellingerGammaResolvedProvenanceAdjacentCoface hpq a n x}

def hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    Submodule ℂ (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq) :=
  (Submodule.span ℂ
    (hellingerGammaResolvedProvenanceAdjacentCofaceSet hpq a)).topologicalClosure

theorem hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_le_ker
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a ≤
      LinearMap.ker hellingerGammaResolvedProvenanceProjection.toLinearMap := by
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro z ⟨n, x, rfl⟩
    simp [hellingerGammaResolvedProvenanceProjection]
  · exact hellingerGammaResolvedProvenanceProjection.isClosed_ker

def hellingerGammaResolvedProvenanceQuotientProjection
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
        hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) →ₗ[ℂ]
      DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).liftQ
    hellingerGammaResolvedProvenanceProjection.toLinearMap
    (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_le_ker hpq a)

def hellingerGammaResolvedProvenanceQuotientSource
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq →ₗ[ℂ]
      (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
        hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) :=
  (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).mkQ.comp
    hellingerGammaResolvedProvenanceInsertion

@[simp]
theorem hellingerGammaResolvedProvenanceQuotientProjection_source
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceQuotientProjection hpq a
        (hellingerGammaResolvedProvenanceQuotientSource hpq a x) = x := by
  change
    (((hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).liftQ
      hellingerGammaResolvedProvenanceProjection.toLinearMap
      (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_le_ker hpq a)).comp
        (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).mkQ)
      (hellingerGammaResolvedProvenanceInsertion x) = x
  rw [Submodule.liftQ_mkQ]
  rfl

theorem hellingerGammaResolvedProvenanceQuotientSource_injective
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    Function.Injective (hellingerGammaResolvedProvenanceQuotientSource hpq a) := by
  intro x y hxy
  have := congrArg
    (hellingerGammaResolvedProvenanceQuotientProjection hpq a) hxy
  simpa using this

def hellingerGammaResolvedProvenanceSourceDefectValue
    {p q : Nat.Primes} (hpq : p ≠ q) (r : XiZeroCopy) :
    HellingerGammaResolvedProvenanceCofaceCompletion p q hpq →ₗ[ℂ]
      (deningerCalderonWittGlobalMilnorIncidence ×
        deningerCalderonWittGlobalMilnorIncidence) :=
  (resolvedDefectAntidiagonal (R := ℂ)
      (Z := deningerCalderonWittGlobalMilnorIncidence)).comp
    ((deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
      p q hpq r).comp hellingerGammaResolvedProvenanceProjection.toLinearMap)

@[simp]
theorem hellingerGammaResolvedProvenanceSourceDefectValue_vertex
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (r : XiZeroCopy)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceSourceDefectValue hpq r
        (hellingerGammaResolvedProvenanceVertex hpq a n x) =
      resolvedDefectAntidiagonal (R := ℂ)
        (deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
          p q hpq r x) :=
  rfl

@[simp]
theorem hellingerGammaResolvedProvenanceSourceDefectValue_coface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (r : XiZeroCopy)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceSourceDefectValue hpq r
        (hellingerGammaResolvedProvenanceAdjacentCoface hpq a n x) = 0 := by
  simp [hellingerGammaResolvedProvenanceSourceDefectValue,
    hellingerGammaResolvedProvenanceProjection]

end

end RHTower
