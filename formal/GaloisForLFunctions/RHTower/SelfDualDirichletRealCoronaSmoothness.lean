import GaloisForLFunctions.RHTower.CompleteStripRealCoronaCompactification
import GaloisForLFunctions.RHTower.DirichletLZerosInfinite
import GaloisForLFunctions.RHTower.SelfDualDirichletRealZeros

/-!
# P3 for actual self-dual primitive Dirichlet L-functions

Every nontrivial primitive self-dual Dirichlet character gives an actual completed automorphic
GL(1) L-function.  Its completed divisor satisfies the universal complete-strip reflection law:
the zero set is infinite, all zeros lie in the open critical strip, closed-disc zero packets are
finite, and self-duality turns the functional equation into `rho ↦ 1-rho` invariance.

Therefore none of these automorphic completions has a smooth Real-corona idempotent in the natural
dense endpoint-entire reflection crossed product.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.RHTower

variable {N : ℕ} [NeZero N]

/-- Actual completed GL(1) automorphic divisor as an instance of the universal compactification
law. -/
def selfDualPrimitiveDirichletCompleteStripDivisor
    (chi : SelfDualPrimitiveDirichletDatum N) : CompleteStripReflectionDivisor where
  completed := DirichletCharacter.completedLFunction chi.character
  zeroSetInfinite := _root_.RHTower.completedLFunction_zeroSet_infinite chi.nontrivial
  zero_mem_openUnitStrip := fun hz =>
    _root_.RHTower.completedLFunction_zero_mem_openUnitStrip
      chi.nontrivial chi.primitive hz
  zero_reflect := by
    intro z hz
    have hFE := chi.primitive.completedLFunction_one_sub z
    rw [chi.selfDual, hz, mul_zero] at hFE
    exact hFE
  zeros_closedBall_finite :=
    _root_.RHTower.completedLFunction_zeros_closedBall_finite chi.nontrivial

/-- Exact smoothness classification for each actual self-dual primitive Dirichlet completion. -/
theorem selfDualPrimitiveDirichlet_corona_crossedProduct_iff_finite
    (chi : SelfDualPrimitiveDirichletDatum N) :
    let D := selfDualPrimitiveDirichletCompleteStripDivisor chi
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∈
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      D.upperSector.Finite ∧ D.lowerSector.Finite := by
  exact (selfDualPrimitiveDirichletCompleteStripDivisor chi).corona_crossedProduct_iff_finite

/-- **P3 for the full actual self-dual primitive Dirichlet family:** smoothness never occurs. -/
theorem selfDualPrimitiveDirichlet_corona_not_mem_smoothCrossedProductRange
    (chi : SelfDualPrimitiveDirichletDatum N) :
    let D := selfDualPrimitiveDirichletCompleteStripDivisor chi
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) := by
  exact (selfDualPrimitiveDirichletCompleteStripDivisor chi).corona_not_mem_smoothCrossedProductRange

/-- Functional-equation reflection acts on the actual automorphic corona by complement. -/
theorem selfDualPrimitiveDirichlet_odd_smul_corona_eq_complement
    (chi : SelfDualPrimitiveDirichletDatum N) :
    let D := selfDualPrimitiveDirichletCompleteStripDivisor chi
    let R := D.holomorphicReflection
    letI := R.functionAction
    ReflectionParity.odd • endpointRealCoronaIdempotent D.upperSector D.lowerSector =
      1 - endpointRealCoronaIdempotent D.upperSector D.lowerSector := by
  exact (selfDualPrimitiveDirichletCompleteStripDivisor chi).odd_smul_corona_eq_complement

end GaloisForLFunctions.RHTower
