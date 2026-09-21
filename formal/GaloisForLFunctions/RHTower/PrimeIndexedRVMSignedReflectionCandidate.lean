import GaloisForLFunctions.RHTower.PrimeIndexedRVMPontryaginBoundarySurvivor
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockDouble

/-!
# Signed-reflection repair candidate for the quartic K-RVM carrier

The literal paired determinant has a forced nonzero cubic coefficient, so it cannot equal
normalized centered Xi. Pairing the literal determinant with its sign reflection removes every
odd Taylor coefficient. This module proves that this repair preserves the source-matched second
and fourth jets exactly. The remaining problem is operator-realization: prove that this function
is the regularized determinant of the literal block carrier (T \oplus (-T)).
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open KRVMPaired

private theorem routeKQuarticallyAdmittedEntireDet_differentiable' :
    Differentiable ℂ routeKQuarticallyAdmittedEntireDet := by
  simpa [routeKQuarticallyAdmittedEntireDet] using
    differentiable_entireDet2 routeKQuarticallyAdmittedKernel_isHS

private theorem routeKQuarticallyAdmittedEntireDet_zero' :
    routeKQuarticallyAdmittedEntireDet 0 = 1 := by
  rw [routeKQuarticallyAdmittedEntireDet]
  exact (isRegularizedDet_entireDet2
    routeKQuarticallyAdmittedKernel_isHS).eq_one_at_zero

private theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_one' :
    taylorCoeff routeKQuarticallyAdmittedEntireDet 1 = 0 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    taylorCoeff_entireDet2_eq_detCoeff
      routeKQuarticallyAdmittedKernel_isHS,
    detCoeff_one_eq_zero routeKQuarticallyAdmittedKernel_isHS]

/-- Literal doubled carrier with the second channel sign-reversed. -/
noncomputable def routeKQuarticallySignedReflectionKernel :
    (Nat.Primes ⊕ Nat.Primes) × (Nat.Primes ⊕ Nat.Primes) → ℂ :=
  HilbertSchmidt.blockDouble routeKQuarticallyAdmittedKernel
    (-routeKQuarticallyAdmittedKernel)

/-- The signed reflection carrier remains Hilbert--Schmidt. -/
theorem routeKQuarticallySignedReflectionKernel_isHS :
    HilbertSchmidt.IsHS routeKQuarticallySignedReflectionKernel := by
  unfold routeKQuarticallySignedReflectionKernel
  exact HilbertSchmidt.isHS_blockDouble routeKQuarticallyAdmittedKernel_isHS
    (HilbertSchmidt.isHS_neg routeKQuarticallyAdmittedKernel_isHS)

/-- The original literal quartic kernel represents the already certified self-adjoint carrier. -/
theorem routeKQuarticallyAdmittedKernel_isSelfAdjoint :
    IsSelfAdjoint
      (HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS) := by
  rw [routeKQuarticallyAdmittedKernel_toOperator]
  exact routeKQuarticallyAdmittedOperator_isSelfAdjoint

private theorem routeKQuarticallyAdmittedKernel_hsAdjoint :
    HilbertSchmidt.hsAdjoint routeKQuarticallyAdmittedKernel =
      routeKQuarticallyAdmittedKernel := by
  have hself : ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS) =
      HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      routeKQuarticallyAdmittedKernel_isSelfAdjoint
  calc
    HilbertSchmidt.hsAdjoint routeKQuarticallyAdmittedKernel =
        HilbertSchmidt.matrixOf (ContinuousLinearMap.adjoint
          (HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS)) := by
      rw [HilbertSchmidt.matrixOf_adjoint,
        HilbertSchmidt.matrixOf_toOperator]
    _ = HilbertSchmidt.matrixOf
        (HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS) :=
      congrArg HilbertSchmidt.matrixOf hself
    _ = routeKQuarticallyAdmittedKernel :=
      HilbertSchmidt.matrixOf_toOperator routeKQuarticallyAdmittedKernel_isHS

/-- The signed literal block carrier is self-adjoint. -/
theorem routeKQuarticallySignedReflectionKernel_isSelfAdjoint :
    IsSelfAdjoint
      (HilbertSchmidt.toOperator routeKQuarticallySignedReflectionKernel_isHS) := by
  have hnegself :
      HilbertSchmidt.hsAdjoint (-routeKQuarticallyAdmittedKernel) =
        -routeKQuarticallyAdmittedKernel := by
    calc
      HilbertSchmidt.hsAdjoint (-routeKQuarticallyAdmittedKernel) =
          -HilbertSchmidt.hsAdjoint routeKQuarticallyAdmittedKernel := by
        funext p
        simp [HilbertSchmidt.hsAdjoint]
      _ = -routeKQuarticallyAdmittedKernel := by
        rw [routeKQuarticallyAdmittedKernel_hsAdjoint]
  simpa only [routeKQuarticallySignedReflectionKernel] using
    (HilbertSchmidt.isSelfAdjoint_toOperator_blockDouble
      routeKQuarticallyAdmittedKernel_isHS
      (HilbertSchmidt.isHS_neg routeKQuarticallyAdmittedKernel_isHS)
      routeKQuarticallyAdmittedKernel_hsAdjoint hnegself)

/-- Determinant-level signed pairing of the literal quartic K-RVM carrier. -/
noncomputable def routeKQuarticallySignedReflectionEntireDet : ℂ → ℂ :=
  fun z => routeKQuarticallyAdmittedEntireDet z *
    routeKQuarticallyAdmittedEntireDet (-z)

/-- The signed-reflection function is the regularized determinant of the literal
block carrier K \oplus (-K). -/
theorem entireDet2_routeKQuarticallySignedReflectionKernel :
    entireDet2 routeKQuarticallySignedReflectionKernel =
      routeKQuarticallySignedReflectionEntireDet := by
  have hneg : (-routeKQuarticallyAdmittedKernel) =
      (-1 : ℂ) • routeKQuarticallyAdmittedKernel := by
    ext p
    simp
  rw [routeKQuarticallySignedReflectionKernel,
    HilbertSchmidt.entireDet2_blockDouble routeKQuarticallyAdmittedKernel_isHS
      (HilbertSchmidt.isHS_neg routeKQuarticallyAdmittedKernel_isHS), hneg,
    entireDet2_smul routeKQuarticallyAdmittedKernel_isHS (-1 : ℂ)]
  funext z
  change entireDet2 routeKQuarticallyAdmittedKernel z *
      entireDet2 routeKQuarticallyAdmittedKernel (-1 * z) =
    entireDet2 routeKQuarticallyAdmittedKernel z *
      entireDet2 routeKQuarticallyAdmittedKernel (-z)
  congr 1
  ring

/-- Sign pairing makes the candidate even. -/
theorem routeKQuarticallySignedReflectionEntireDet_even :
    Function.Even routeKQuarticallySignedReflectionEntireDet := by
  intro z
  simp [routeKQuarticallySignedReflectionEntireDet, mul_comm]

private theorem routeKQuarticallySignedReflectionEntireDet_differentiable :
    Differentiable ℂ routeKQuarticallySignedReflectionEntireDet := by
  unfold routeKQuarticallySignedReflectionEntireDet
  exact routeKQuarticallyAdmittedEntireDet_differentiable'.mul
    (routeKQuarticallyAdmittedEntireDet_differentiable'.comp differentiable_neg)

/-- The signed reflection has zero cubic coefficient for structural, not numerical, reasons. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_three :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 3 = 0 := by
  rw [taylorCoeff,
    iteratedDeriv_zero_of_even_of_odd
      routeKQuarticallySignedReflectionEntireDet_even (by decide), mul_zero]

/-- The signed reflection keeps the source-matched quadratic jet. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_two :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 2 =
      -(routeKSourceZerothMoment : ℂ) / 2 := by
  unfold routeKQuarticallySignedReflectionEntireDet
  rw [taylorCoeff_reflectionProduct_two_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable'
    routeKQuarticallyAdmittedEntireDet_zero'
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one',
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two]
  ring

/-- The signed reflection keeps the source-matched quartic jet. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_four :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 4 =
      (routeKSourceZerothMoment : ℂ) ^ 2 / 8 -
        (routeKSourceFirstMoment : ℂ) / 4 := by
  unfold routeKQuarticallySignedReflectionEntireDet
  rw [taylorCoeff_reflectionProduct_four_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable'
    routeKQuarticallyAdmittedEntireDet_zero'
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one',
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_four,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two]
  ring

/-- The signed reflection and original squared pairing agree through degree four. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_two_eq_squared :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 2 =
      taylorCoeff routeKQuarticallyAdmittedSquaredEntireDet 2 := by
  rw [taylorCoeff_routeKQuarticallySignedReflectionEntireDet_two,
    taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_two]

/-- The signed reflection and original squared pairing agree through degree four. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_four_eq_squared :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 4 =
      taylorCoeff routeKQuarticallyAdmittedSquaredEntireDet 4 := by
  rw [taylorCoeff_routeKQuarticallySignedReflectionEntireDet_four,
    taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_four]

end

end RHTower
