import GaloisForLFunctions.HTGeometry.TailHadamardReducedProduct
import GaloisForLFunctions.RHTower.PrimeEulerNodalPhaseBarrierLaw

/-!
# Prime Euler--Hadamard nodal scalar-unit universality

Boolean prime orientations become involutions in the Hadamard algebra of coefficient tails.
Multiplying two such classes exposes exactly the nonlinear Euler relation between them: product
`1` is same-sheet finite Euler gauge, while product `-1` is opposite-sheet cyclotomic-norm
complementarity. There are no other scalar modes.

Outside these two scalar units, every continuous positive-weight residue deformation between the
orientations must cross infinitely many coordinate zero walls. Thus one algebraic product
simultaneously classifies both Euler lifting sheets and their nodal phase barrier.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open Set Topology

noncomputable section

/-- Hadamard product `1` is exactly same-sheet finite Euler gauge equivalence. -/
theorem primeOrientationHadamardTail_mul_eq_one_iff_eulerGauge
    {P : Type*} (epsilon delta : P → Bool) :
    HTGeometry.primeOrientationHadamardTail epsilon *
        HTGeometry.primeOrientationHadamardTail delta = 1 ↔
      PrimeEulerTailGaugeEquivalent epsilon delta := by
  rw [primeEulerTailGaugeEquivalent_iff_eventuallyEqual]
  change HTGeometry.tailHadamardClass
        (fun p => primeDirichletRealSign (epsilon p)) *
      HTGeometry.tailHadamardClass
        (fun p => primeDirichletRealSign (delta p)) = 1 ↔ _
  rw [← HTGeometry.tailHadamardClass_mul, ← HTGeometry.tailHadamardClass_one,
    HTGeometry.tailHadamardClass_eq_iff]
  simp only [HTGeometry.FiniteTailEquivalent, PrimeOrientationsEventuallyEqual]
  have hset :
      {p | primeDirichletRealSign (epsilon p) *
          primeDirichletRealSign (delta p) ≠ 1} =
        {p | epsilon p ≠ delta p} := by
    ext p
    simp only [Set.mem_setOf_eq]
    cases epsilon p <;> cases delta p <;>
      norm_num [primeDirichletRealSign]
  rw [hset]

/-- Hadamard product `-1` is exactly opposite-sheet Euler norm complementarity. -/
theorem primeOrientationHadamardTail_mul_eq_neg_one_iff_eulerNorm
    {P : Type*} (epsilon delta : P → Bool) :
    HTGeometry.primeOrientationHadamardTail epsilon *
        HTGeometry.primeOrientationHadamardTail delta = -1 ↔
      PrimeEulerTailNormComplementary epsilon delta := by
  rw [primeEulerTailNormComplementary_iff_eventuallyOpposite]
  change HTGeometry.tailHadamardClass
        (fun p => primeDirichletRealSign (epsilon p)) *
      HTGeometry.tailHadamardClass
        (fun p => primeDirichletRealSign (delta p)) = -1 ↔ _
  rw [← HTGeometry.tailHadamardClass_mul]
  change HTGeometry.tailHadamardClass
      (fun p => primeDirichletRealSign (epsilon p) *
        primeDirichletRealSign (delta p)) =
      HTGeometry.tailHadamardClass (fun _ : P => -1) ↔ _
  rw [HTGeometry.tailHadamardClass_eq_iff]
  simp only [HTGeometry.FiniteTailEquivalent, PrimeOrientationsEventuallyOpposite]
  have hset :
      {p | primeDirichletRealSign (epsilon p) *
          primeDirichletRealSign (delta p) ≠ -1} =
        {p | epsilon p = delta p} := by
    ext p
    simp only [Set.mem_setOf_eq]
    cases epsilon p <;> cases delta p <;>
      norm_num [primeDirichletRealSign]
  rw [hset]

/-- **Prime Euler--Hadamard nodal scalar-unit universality.** The two nonlinear Euler lifting
modes are precisely the two scalar units of the endpoint Hadamard product. If that product is
neither scalar unit, every continuous positive-weight residue deformation has infinite nodal
support. -/
theorem primeEulerHadamardNodal_completeScalarUnitUniversality
    (epsilon delta : ℕ → Bool) (w : ℕ → ℝ) (r : ℝ → ℕ → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1)) :
    (HTGeometry.primeOrientationHadamardTail epsilon *
          HTGeometry.primeOrientationHadamardTail delta = 1 ↔
        PrimeEulerTailGaugeEquivalent epsilon delta) ∧
    (HTGeometry.primeOrientationHadamardTail epsilon *
          HTGeometry.primeOrientationHadamardTail delta = -1 ↔
        PrimeEulerTailNormComplementary epsilon delta) ∧
    (HTGeometry.primeOrientationHadamardTail epsilon *
          HTGeometry.primeOrientationHadamardTail delta ≠ 1 →
      HTGeometry.primeOrientationHadamardTail epsilon *
          HTGeometry.primeOrientationHadamardTail delta ≠ -1 →
      (HTGeometry.residuePathNodalSupport r).Infinite) := by
  refine ⟨primeOrientationHadamardTail_mul_eq_one_iff_eulerGauge epsilon delta,
    primeOrientationHadamardTail_mul_eq_neg_one_iff_eulerNorm epsilon delta, ?_⟩
  intro hone hneg
  apply residuePathNodalSupport_infinite_of_no_primeEulerMode
    epsilon delta w r hw hr0 hr1 hcontinuous
  push Not
  exact ⟨fun hgauge =>
    hone ((primeOrientationHadamardTail_mul_eq_one_iff_eulerGauge epsilon delta).2 hgauge),
    fun hnorm =>
      hneg ((primeOrientationHadamardTail_mul_eq_neg_one_iff_eulerNorm epsilon delta).2 hnorm)⟩

end

end GaloisForLFunctions.RHTower
