import GaloisForLFunctions.RHTower.PrimeIndexedRVMPontryaginBoundarySurvivor
import GaloisForLFunctions.RHTower.PrimeArchThetaThirdCumulantProductKernel
import GaloisForLFunctions.RHTower.CompletedPrimeGammaSecondMomentCenterPositive
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockDouble
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.HTGeometry.QuantumReplicaHausdorff

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

/-- At the center, the continued prime--archimedean source and the signed
K-RVM resolvent have identical first jets.  This is the first local
source-to-carrier identity; extending it to every odd trace remains the
operator-realization problem. -/
theorem hasDerivAt_routeKQuarticallySignedResolventBridge_zero :
    HasDerivAt
      (fun z : ℂ =>
        continuedPrimeArchSourceRelativeTrace z +
          HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel z -
          HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel (-z))
      0 0 := by
  have hsourceDeriv :
      deriv continuedPrimeArchSourceRelativeTrace 0 =
        -(normalizedPrimeArchMoment 0 : ℂ) := by
    have hgerm : normalizedPrimeArchMomentGerm 0 =
        -deriv continuedPrimeArchSourceRelativeTrace 0 := by
      rw [normalizedPrimeArchMomentGerm, normalizedTraceMomentGerm, dslope_same]
    rw [normalizedPrimeArchMomentGerm_zero] at hgerm
    have hneg := congrArg Neg.neg hgerm
    simpa only [neg_neg] using hneg.symm
  have hsource : HasDerivAt continuedPrimeArchSourceRelativeTrace
      (-(normalizedPrimeArchMoment 0 : ℂ)) 0 := by
    simpa only [hsourceDeriv] using
      analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt.hasDerivAt
  have htrace :
      (∑' p : Nat.Primes,
        HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 1 (p, p)) =
          (normalizedPrimeArchMoment 0 : ℂ) / 2 := by
    rw [routeKQuarticallyAdmittedKernel_square_trace]
    have h := two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator
    rw [routeKSourceZerothMoment_eq_normalizedPrimeArchMoment] at h
    linear_combination h / 2
  have hres : HasDerivAt
      (HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel)
      ((normalizedPrimeArchMoment 0 : ℂ) / 2) 0 := by
    simpa only [htrace] using
      hasDerivAt_resolventTrace_zero
        routeKQuarticallyAdmittedKernel_isHS
  have hresNeg : HasDerivAt
      (fun z : ℂ => HilbertSchmidt.resolventTrace
        routeKQuarticallyAdmittedKernel (-z))
      (-((normalizedPrimeArchMoment 0 : ℂ) / 2)) 0 := by
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) 0 :=
      (hasDerivAt_id 0).neg
    have hres' : HasDerivAt
        (HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel)
        ((normalizedPrimeArchMoment 0 : ℂ) / 2) ((fun z : ℂ => -z) 0) := by
      simpa using hres
    have hcomp : HasDerivAt
        (HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel ∘
          fun z : ℂ => -z)
        (((normalizedPrimeArchMoment 0 : ℂ) / 2) * (-1)) 0 :=
      HasDerivAt.comp 0 hres' hneg
    simpa only [Function.comp_def, mul_neg, mul_one] using hcomp
  have h := (hsource.add hres).sub hresNeg
  have hderiv :
      -(normalizedPrimeArchMoment 0 : ℂ) +
          (normalizedPrimeArchMoment 0 : ℂ) / 2 -
          (-((normalizedPrimeArchMoment 0 : ℂ) / 2)) = 0 := by
    ring
  change HasDerivAt
    (continuedPrimeArchSourceRelativeTrace +
      HilbertSchmidt.resolventTrace routeKQuarticallyAdmittedKernel -
      (fun z : ℂ => HilbertSchmidt.resolventTrace
        routeKQuarticallyAdmittedKernel (-z))) 0 0
  simpa only [hderiv] using h

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

/-- The sixth Hilbert--Schmidt trace of the literal quartic K-RVM kernel is
the ordinary sixth trace of its represented operator. -/
theorem routeKQuarticallyAdmittedKernel_sixth_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 5 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) := by
  rw [← HilbertSchmidt.hsComp_hsPow
    routeKQuarticallyAdmittedKernel_isHS 2 2]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 2)
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 2)]
  rw [HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 2,
    routeKQuarticallyAdmittedKernel_toOperator]
  congr 1

/-- The literal K-RVM determinant's sixth coefficient exposes the next trace
coordinate not fixed by quartic admission. -/
theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_six :
    taylorCoeff routeKQuarticallyAdmittedEntireDet 6 =
      -ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) / 6 +
        (routeKSourceZerothMoment : ℂ) * (routeKSourceFirstMoment : ℂ) / 32 +
        (ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 3)) ^ 2 / 18 -
        (routeKSourceZerothMoment : ℂ) ^ 3 / 384 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    taylorCoeff_entireDet2_six routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_sixth_trace,
    routeKQuarticallyAdmittedKernel_square_trace,
    routeKQuarticallyAdmittedKernel_fourth_trace,
    routeKQuarticallyAdmittedKernel_cube_trace]
  have h2 := two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator
  have h4 := two_mul_opTrace_four_routeKQuarticallyAdmittedOperator
  have h2' : ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 2) =
      (routeKSourceZerothMoment : ℂ) / 2 := by
    linear_combination h2 / 2
  have h4' : ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 4) =
      (routeKSourceFirstMoment : ℂ) / 2 := by
    linear_combination h4 / 2
  rw [h2', h4']
  ring

/-- The signed reflection cancels the cubic trace at degree six and leaves the
literal sixth trace as the next unresolved K-RVM coordinate. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_six :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 6 =
      -ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) / 3 +
        (routeKSourceZerothMoment : ℂ) * (routeKSourceFirstMoment : ℂ) / 8 -
        (routeKSourceZerothMoment : ℂ) ^ 3 / 48 := by
  unfold routeKQuarticallySignedReflectionEntireDet
  rw [taylorCoeff_reflectionProduct_six_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable'
    routeKQuarticallyAdmittedEntireDet_zero'
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one',
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_six,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_three,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_four]
  ring

/-- The source differential equation fixes the normalized sixth centered Xi
coefficient using its first three prime--archimedean moments. -/
theorem normalized_XiC_sixth_jet_eq_source_moments :
    iteratedDeriv 6 XiC 0 / XiC 0 / 720 =
      -(normalizedPrimeArchMoment 0 : ℂ) ^ 3 / 48 +
        (normalizedPrimeArchMoment 0 : ℂ) * (normalizedPrimeArchMoment 1 : ℂ) / 8 -
        (normalizedPrimeArchMoment 2 : ℂ) / 6 := by
  have htwo := normalizedPrimeArch_recurrence_one_moment
  have hfour := normalizedPrimeArch_recurrence_three
  have hsix := normalizedPrimeArch_recurrence_five
  have hzero : XiC 0 ≠ 0 := XiC_zero_ne
  have hmain : iteratedDeriv 6 XiC 0 =
      (-15 * (normalizedPrimeArchMoment 0 : ℂ) ^ 3 +
        90 * (normalizedPrimeArchMoment 0 : ℂ) * (normalizedPrimeArchMoment 1 : ℂ) -
        120 * (normalizedPrimeArchMoment 2 : ℂ)) * XiC 0 := by
    linear_combination hsix - 5 * (normalizedPrimeArchMoment 0 : ℂ) * hfour -
      (60 * (normalizedPrimeArchMoment 1 : ℂ) - 15 * (normalizedPrimeArchMoment 0 : ℂ) ^ 2) * htwo
  rw [hmain]
  field_simp [hzero]
  ring

/-- The normalized Xi sixth Taylor coefficient is its source moment formula. -/
theorem taylorCoeff_normalized_XiC_six :
    taylorCoeff (fun z : ℂ => XiC z / XiC 0) 6 =
      -(normalizedPrimeArchMoment 0 : ℂ) ^ 3 / 48 +
        (normalizedPrimeArchMoment 0 : ℂ) * (normalizedPrimeArchMoment 1 : ℂ) / 8 -
        (normalizedPrimeArchMoment 2 : ℂ) / 6 := by
  rw [taylorCoeff]
  have heq : (fun z : ℂ => XiC z / XiC 0) =
      fun z => (XiC 0)⁻¹ * XiC z := by
    funext z
    ring
  rw [heq, iteratedDeriv_const_mul_field]
  have hrewrite : (Nat.factorial 6 : ℂ)⁻¹ *
      ((XiC 0)⁻¹ * iteratedDeriv 6 XiC 0) =
      iteratedDeriv 6 XiC 0 / XiC 0 / 720 := by
    norm_num [Nat.factorial]
    ring
  rw [hrewrite, normalized_XiC_sixth_jet_eq_source_moments]

/-- A global normalized-Xi identity for the signed K-RVM determinant must
match the sixth source moment exactly. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_trace
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) =
      (normalizedPrimeArchMoment 2 : ℂ) := by
  have hcoeff := congrArg (fun f : ℂ → ℂ => taylorCoeff f 6) h
  rw [taylorCoeff_routeKQuarticallySignedReflectionEntireDet_six,
    taylorCoeff_normalized_XiC_six,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment] at hcoeff
  linear_combination -6 * hcoeff

/-- The sixth trace is the Hilbert--Schmidt energy of the cubic K-RVM
power, placing the sixth determinant obstruction in the all-order incidence
coordinate system. -/
theorem opTrace_routeKQuarticallyAdmittedOperator_six_eq_cube_hsNormSq :
    ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) =
      (ContinuousLinearMap.hsNormSq
        (routeKQuarticallyAdmittedOperator ^ 3) : ℂ) := by
  have hHS : (routeKQuarticallyAdmittedOperator ^ 3).IsHilbertSchmidt := by
    rw [show 3 = 2 + 1 by norm_num, pow_succ, ContinuousLinearMap.mul_def]
    exact routeKQuarticallyAdmittedOperator_isHilbertSchmidt.comp_left
      (routeKQuarticallyAdmittedOperator ^ 2)
  have hself : IsSelfAdjoint (routeKQuarticallyAdmittedOperator ^ 3) := by
    have hT := routeKQuarticallyAdmittedOperator_isSelfAdjoint
    change star routeKQuarticallyAdmittedOperator =
      routeKQuarticallyAdmittedOperator at hT
    change star (routeKQuarticallyAdmittedOperator ^ 3) =
      routeKQuarticallyAdmittedOperator ^ 3
    rw [star_pow, hT]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
  have hpow : routeKQuarticallyAdmittedOperator ^ 6 =
      (routeKQuarticallyAdmittedOperator ^ 3) ^ 2 := by
    noncomm_ring
  rw [hpow, HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hHS hself]

/-- A signed determinant identity forces the literal K-RVM carrier to match
its third reflected source-energy coordinate. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_energy
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * ContinuousLinearMap.hsNormSq (routeKQuarticallyAdmittedOperator ^ 3) =
      normalizedPrimeArchMoment 2 := by
  have htrace :=
    routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_trace h
  rw [opTrace_routeKQuarticallyAdmittedOperator_six_eq_cube_hsNormSq] at htrace
  exact_mod_cast htrace

/-- The literal self-adjoint K-RVM carrier has a sixth-energy ceiling fixed
by its fourth energy. -/
private theorem hsNormSq_routeKQuarticallyAdmittedOperator_cube_sq_le_sq_cube :
    ContinuousLinearMap.hsNormSq (routeKQuarticallyAdmittedOperator ^ 3) ^ 2 ≤
      ContinuousLinearMap.hsNormSq (routeKQuarticallyAdmittedOperator ^ 2) ^ 3 := by
  let T := routeKQuarticallyAdmittedOperator
  have hT : T.IsHilbertSchmidt :=
    routeKQuarticallyAdmittedOperator_isHilbertSchmidt
  have hself : IsSelfAdjoint T :=
    routeKQuarticallyAdmittedOperator_isSelfAdjoint
  have hT2 : (T ^ 2).IsHilbertSchmidt := by
    rw [show 2 = 1 + 1 by norm_num, pow_succ, ContinuousLinearMap.mul_def]
    exact hT.comp_left T
  have hcomp := HTGeometry.hsNormSq_comp_left_le_opNorm hT2 T
  have hcomp' : ContinuousLinearMap.hsNormSq (T ^ 3) ≤
      ‖T‖ ^ 2 * ContinuousLinearMap.hsNormSq (T ^ 2) := by
    rw [show T ^ 3 = T ∘L T ^ 2 by
      change T ^ 3 = T * T ^ 2
      noncomm_ring]
    exact hcomp
  have hnormId : ‖T‖ ^ 2 = ‖T ^ 2‖ := by
    rw [show ‖T‖ ^ 2 = ‖T‖ * ‖T‖ by ring,
      ← CStarRing.norm_star_mul_self, hself.star_eq]
    rfl
  have hnormSq : ‖T‖ ^ 4 ≤ ContinuousLinearMap.hsNormSq (T ^ 2) := by
    have hop := ContinuousLinearMap.opNorm_le_hsNorm hT2
    have hsquare : ‖T ^ 2‖ ^ 2 ≤ ContinuousLinearMap.hsNorm (T ^ 2) ^ 2 := by
      nlinarith [norm_nonneg (T ^ 2), ContinuousLinearMap.hsNorm_nonneg (T ^ 2)]
    calc
      ‖T‖ ^ 4 = (‖T‖ ^ 2) ^ 2 := by ring
      _ = ‖T ^ 2‖ ^ 2 := by rw [hnormId]
      _ ≤ ContinuousLinearMap.hsNorm (T ^ 2) ^ 2 := hsquare
      _ = ContinuousLinearMap.hsNormSq (T ^ 2) := by
        rw [ContinuousLinearMap.hsNorm,
          Real.sq_sqrt (ContinuousLinearMap.hsNormSq_nonneg _)]
  have hcompSq : ContinuousLinearMap.hsNormSq (T ^ 3) ^ 2 ≤
      (‖T‖ ^ 2 * ContinuousLinearMap.hsNormSq (T ^ 2)) ^ 2 := by
    nlinarith [ContinuousLinearMap.hsNormSq_nonneg (T ^ 3),
      mul_nonneg (sq_nonneg ‖T‖) (ContinuousLinearMap.hsNormSq_nonneg (T ^ 2))]
  change ContinuousLinearMap.hsNormSq (T ^ 3) ^ 2 ≤
    ContinuousLinearMap.hsNormSq (T ^ 2) ^ 3
  calc
    ContinuousLinearMap.hsNormSq (T ^ 3) ^ 2 ≤
        (‖T‖ ^ 2 * ContinuousLinearMap.hsNormSq (T ^ 2)) ^ 2 := hcompSq
    _ = ‖T‖ ^ 4 * ContinuousLinearMap.hsNormSq (T ^ 2) ^ 2 := by ring
    _ ≤ ContinuousLinearMap.hsNormSq (T ^ 2) *
        ContinuousLinearMap.hsNormSq (T ^ 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hnormSq
        (sq_nonneg (ContinuousLinearMap.hsNormSq (T ^ 2)))
    _ = ContinuousLinearMap.hsNormSq (T ^ 2) ^ 3 := by ring

/-- A global signed-determinant identity would force a sharp sixth-source
ceiling.  Thus the K-RVM extension is constrained by more than the first
Hankel minor: its source moments must be spectral power sums. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_ceiling
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * normalizedPrimeArchMoment 2 ^ 2 ≤ normalizedPrimeArchMoment 1 ^ 3 := by
  have henergy := hsNormSq_routeKQuarticallyAdmittedOperator_cube_sq_le_sq_cube
  have hfour := two_mul_hsNormSq_sq_routeKQuarticallyAdmittedOperator
  rw [routeKSourceFirstMoment_eq_normalizedPrimeArchMoment] at hfour
  have hsix := routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_energy h
  have hfour' : ContinuousLinearMap.hsNormSq
      (routeKQuarticallyAdmittedOperator ^ 2) =
      normalizedPrimeArchMoment 1 / 2 := by
    linarith
  have hsix' : ContinuousLinearMap.hsNormSq
      (routeKQuarticallyAdmittedOperator ^ 3) =
      normalizedPrimeArchMoment 2 / 2 := by
    linarith
  rw [hfour', hsix'] at henergy
  nlinarith

/-- The sixth K-RVM spectral ceiling becomes one exact theta-source inequality: the signed
third-cumulant product integral is controlled by the cube of the source quadratic functional.
This is the first analytic source law required by a global signed-determinant identity. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_productKernel_sixth_ceiling
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * (thetaCuspThirdCumulantProductIntegral /
        (120 * (∫ _ : ℝ, (1 : ℝ) ∂thetaCuspEvenMomentMeasure) ^ 3)) ^ 2 ≤
      (thetaCuspNormalizedEvenMoment 1 ^ 2 / 2 -
        thetaCuspNormalizedEvenMoment 2 / 6) ^ 3 := by
  rw [← normalizedPrimeArchMoment_two_eq_thirdCumulantProductRatio,
    ← normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
  exact routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_ceiling h

/-- The sixth K-RVM ceiling has a homogeneous raw-theta form.  All normalizing mass factors
cancel, so a source proof must establish this third-order inequality directly on the first four
raw theta moments. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_rawTheta_sixth_spectral_law
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    3 * (thetaCuspRawEvenMoment 0 ^ 2 * thetaCuspRawEvenMoment 3 -
      15 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
        thetaCuspRawEvenMoment 2 + 30 * thetaCuspRawEvenMoment 1 ^ 3) ^ 2 ≤
      100 * (3 * thetaCuspRawEvenMoment 1 ^ 2 -
        thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) ^ 3 := by
  let a := thetaCuspRawEvenMoment 0
  let b := thetaCuspRawEvenMoment 1
  let c := thetaCuspRawEvenMoment 2
  let d := thetaCuspRawEvenMoment 3
  let q := 3 * b ^ 2 - a * c
  let r := a ^ 2 * d - 15 * a * b * c + 30 * b ^ 3
  change 3 * r ^ 2 ≤ 100 * q ^ 3
  have ha : 0 < a := by
    exact thetaCuspRawEvenMoment_zero_pos
  have hfirst : normalizedPrimeArchMoment 1 = q / (6 * a ^ 2) := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [q, a, b, c, thetaCuspNormalizedEvenMoment]
    field_simp [ha.ne']
    ring
  have hsixth : normalizedPrimeArchMoment 2 = r / (120 * a ^ 3) := by
    rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [r, a, b, c, d, thetaCuspNormalizedEvenMoment]
    field_simp [ha.ne']
    ring
  have hceiling := routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_ceiling h
  rw [hfirst, hsixth] at hceiling
  have hscale : 0 ≤ 21600 * a ^ 6 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hceiling hscale
  have hleft :
      (21600 * a ^ 6) * (2 * (r / (120 * a ^ 3)) ^ 2) = 3 * r ^ 2 := by
    field_simp [ha.ne']
    ring
  have hright :
      (21600 * a ^ 6) * (q / (6 * a ^ 2)) ^ 3 = 100 * q ^ 3 := by
    field_simp [ha.ne']
    ring
  rw [hleft, hright] at hscaled
  exact hscaled


/-- The strict reciprocal-square sector forces the pointwise sixth spectral law. -/
theorem xiZeroCopyReciprocalSquare_cube_re_sq_le_sq_re_cube
    (q : XiZeroCopy) :
    ((xiZeroCopyReciprocalSquare q ^ 3).re) ^ 2 ≤
      ((xiZeroCopyReciprocalSquare q ^ 2).re) ^ 3 := by
  let z := xiZeroCopyReciprocalSquare q
  have hx : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hs : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have htwo : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hthree : (z ^ 3).re = z.re * (z.re ^ 2 - 3 * z.im ^ 2) := by
    simp [pow_succ, Complex.mul_re]
    ring
  rw [htwo, hthree]
  set u : ℝ := z.re ^ 2
  set v : ℝ := z.im ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have huv : v ≤ u / 84 := by
    dsimp only [u, v]
    convert hs using 1 <;> ring
  have hvu : v ≤ u := by nlinarith
  have hseven : 7 * v ≤ u := by nlinarith
  have huv_sq : v ^ 2 ≤ u * v := by
    calc
      v ^ 2 = v * v := by ring
      _ ≤ u * v := mul_le_mul_of_nonneg_right hvu hv
  have hseven_uv : 7 * u * v ≤ u ^ 2 := by
    calc
      7 * u * v = u * (7 * v) := by ring
      _ ≤ u * u := mul_le_mul_of_nonneg_left hseven hu
      _ = u ^ 2 := by ring
  have hcore : 0 ≤ 3 * u ^ 2 - 6 * u * v - v ^ 2 := by
    nlinarith
  have hdiff :
      0 ≤ (z.re ^ 2 - z.im ^ 2) ^ 3 -
        (z.re * (z.re ^ 2 - 3 * z.im ^ 2)) ^ 2 := by
    rw [show
      (z.re ^ 2 - z.im ^ 2) ^ 3 -
          (z.re * (z.re ^ 2 - 3 * z.im ^ 2)) ^ 2 =
        v * (3 * u ^ 2 - 6 * u * v - v ^ 2) by
      dsimp only [u, v]
      ring]
    exact mul_nonneg hv hcore
  linarith

/-- The strict reciprocal-square sector makes every second real trace atom positive. -/
theorem xiZeroCopyReciprocalSquare_sq_re_pos_of_thermal_sector (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hx : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hs : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have htwo : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [htwo]
  nlinarith [sq_pos_of_pos hx]

set_option maxHeartbeats 800000 in
/-- The actual Xi reciprocal-square divisor moments satisfy the sixth spectral ceiling
without RH: a free Schwarz pair supplies the factor two, and Hölder sums the atomwise sector law. -/
theorem normalizedPrimeArchMoment_sixth_spectral_ceiling :
    2 * normalizedPrimeArchMoment 2 ^ 2 ≤ normalizedPrimeArchMoment 1 ^ 3 := by
  let a : XiZeroCopy → ℝ := fun q => (xiZeroCopyReciprocalSquare q ^ 2).re
  let b : XiZeroCopy → ℝ := fun q => (xiZeroCopyReciprocalSquare q ^ 3).re
  have ha : ∀ q, 0 < a q := fun q => by
    exact xiZeroCopyReciprocalSquare_sq_re_pos_of_thermal_sector q
  have hb : ∀ q, 0 < b q := fun q => by
    exact xiZeroCopyReciprocalSquare_cube_re_pos q
  have hab : ∀ q, b q ^ 2 ≤ a q ^ 3 := fun q => by
    exact xiZeroCopyReciprocalSquare_cube_re_sq_le_sq_re_cube q
  have hsa : Summable a := by
    change Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q ^ 2).re)
    exact Complex.reCLM.summable (summable_xiZeroCopyReciprocalSquare_pow 1)
  have hsb : Summable b := by
    change Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q ^ 3).re)
    exact Complex.reCLM.summable (summable_xiZeroCopyReciprocalSquare_pow 2)
  have hsa2 : Summable (fun q => a q ^ 2) := by
    apply Summable.of_norm_bounded
      (summable_xiZeroCopyReciprocalSquare_pow 3).norm
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      a q ^ 2 ≤ ‖xiZeroCopyReciprocalSquare q ^ 2‖ ^ 2 := by
        exact (sq_le_sq₀ (ha q).le (norm_nonneg _)).mpr
          (Complex.re_le_norm _)
      _ = ‖xiZeroCopyReciprocalSquare q ^ 4‖ := by
        rw [norm_pow, norm_pow]
        ring
  have hainv : ∀ q, a (xiZeroCopyConjEquiv q) = a q := by
    intro q
    change (xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re
    rw [xiZeroCopyReciprocalSquare_conjEquiv]
    have hpow :
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q ^ 2) =
          ((starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)) ^ 2 :=
      map_pow (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) 2
    rw [← hpow, Complex.conj_re]
  have hpair : ∀ q, 2 * a q ≤ ∑' r, a r := by
    intro q
    exact two_mul_le_tsum_of_conj_invariant
      (fun r => (ha r).le) hsa hainv q
  let c : XiZeroCopy → ℝ := fun q => b q ^ 2 / a q
  have hc : ∀ q, 0 ≤ c q := fun q =>
    div_nonneg (sq_nonneg _) (ha q).le
  have hca2 : ∀ q, c q ≤ a q ^ 2 := by
    intro q
    dsimp only [c]
    apply (div_le_iff₀ (ha q)).2
    nlinarith [hab q]
  have hsc : Summable c :=
    Summable.of_nonneg_of_le hc hca2 hsa2
  have hsqrt : ∀ q, Real.sqrt (a q) * Real.sqrt (c q) = b q := by
    intro q
    have hsqa : Real.sqrt (a q) ^ 2 = a q :=
      Real.sq_sqrt (ha q).le
    have hsqc : Real.sqrt (c q) ^ 2 = c q :=
      Real.sq_sqrt (hc q)
    have hsq :
        (Real.sqrt (a q) * Real.sqrt (c q)) ^ 2 = (b q) ^ 2 := by
      rw [show (Real.sqrt (a q) * Real.sqrt (c q)) ^ 2 =
          Real.sqrt (a q) ^ 2 * Real.sqrt (c q) ^ 2 by ring,
        hsqa, hsqc]
      dsimp only [c]
      field_simp [(ha q).ne']
    exact (sq_eq_sq₀
      (mul_nonneg (Real.sqrt_nonneg (a q)) (Real.sqrt_nonneg (c q)))
      (hb q).le).mp hsq
  have hsqa : Summable (fun q => Real.sqrt (a q) ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, Real.sq_sqrt (ha _).le] using hsa
  have hsqc : Summable (fun q => Real.sqrt (c q) ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, Real.sq_sqrt (hc _)] using hsc
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
      (fun q => Real.sqrt_nonneg (a q))
      (fun q => Real.sqrt_nonneg (c q))
      hsqa hsqc
  have hsum_sqrt :
      (∑' q, b q) = ∑' q, Real.sqrt (a q) * Real.sqrt (c q) := by
    apply tsum_congr
    intro q
    exact (hsqrt q).symm
  have hsum_sq_a :
      (∑' q, Real.sqrt (a q) ^ 2) = ∑' q, a q := by
    apply tsum_congr
    intro q
    exact Real.sq_sqrt (ha q).le
  have hsum_sq_c :
      (∑' q, Real.sqrt (c q) ^ 2) = ∑' q, c q := by
    apply tsum_congr
    intro q
    exact Real.sq_sqrt (hc q)
  have hsum_sq_a_rpow :
      (∑' q, Real.sqrt (a q) ^ (2 : ℝ)) = ∑' q, a q := by
    simpa only [Real.rpow_two] using hsum_sq_a
  have hsum_sq_c_rpow :
      (∑' q, Real.sqrt (c q) ^ (2 : ℝ)) = ∑' q, c q := by
    simpa only [Real.rpow_two] using hsum_sq_c
  have hholderBound :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        (∑' i : XiZeroCopy, Real.sqrt (a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑' i : XiZeroCopy, Real.sqrt (c i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hholder.2
  have hholderReduced :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        (∑' i : XiZeroCopy, a i) ^ (1 / 2 : ℝ) *
          (∑' i : XiZeroCopy, c i) ^ (1 / 2 : ℝ) := by
    calc
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
          (∑' i : XiZeroCopy, Real.sqrt (a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∑' i : XiZeroCopy, Real.sqrt (c i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholderBound
      _ = (∑' i : XiZeroCopy, a i) ^ (1 / 2 : ℝ) *
            (∑' i : XiZeroCopy, c i) ^ (1 / 2 : ℝ) := by
        rw [hsum_sq_a_rpow, hsum_sq_c_rpow]
  have hholderBound' :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        Real.sqrt (∑' i : XiZeroCopy, a i) *
          Real.sqrt (∑' i : XiZeroCopy, c i) := by
    simpa only [Real.sqrt_eq_rpow] using hholderReduced
  have hBC :
      ∑' q, b q ≤ Real.sqrt (∑' q, a q) * Real.sqrt (∑' q, c q) := by
    rw [hsum_sqrt]
    exact hholderBound'
  have hA : 0 ≤ ∑' q, a q := tsum_nonneg fun q => (ha q).le
  have hB : 0 ≤ ∑' q, b q := tsum_nonneg fun q => (hb q).le
  have hC : 0 ≤ ∑' q, c q := tsum_nonneg hc
  have hBCsq :
      (∑' q, b q) ^ 2 ≤ (∑' q, a q) * ∑' q, c q := by
    have hsA : Real.sqrt (∑' q, a q) ^ 2 = ∑' q, a q :=
      Real.sq_sqrt hA
    have hsC : Real.sqrt (∑' q, c q) ^ 2 = ∑' q, c q :=
      Real.sq_sqrt hC
    nlinarith [Real.sqrt_nonneg (∑' q, a q), Real.sqrt_nonneg (∑' q, c q)]
  have hCsq : ∑' q, c q ≤ ∑' q, a q ^ 2 :=
    hsc.tsum_le_tsum hca2 hsa2
  have hsa2scale : Summable (fun q => 2 * a q ^ 2) :=
    (hsa2.hasSum.mul_left 2).summable
  have hsascale : Summable (fun q => (∑' r, a r) * a q) :=
    (hsa.hasSum.mul_left (∑' r, a r)).summable
  have hA2 :
      2 * ∑' q, a q ^ 2 ≤ (∑' q, a q) ^ 2 := by
    calc
      2 * ∑' q, a q ^ 2 = ∑' q, 2 * a q ^ 2 := by
        rw [hsa2.tsum_mul_left]
      _ ≤ ∑' q, (∑' r, a r) * a q := by
        exact hsa2scale.tsum_le_tsum
          (fun q => by
            convert mul_le_mul_of_nonneg_right (hpair q) (ha q).le using 1 <;> ring)
          hsascale
      _ = (∑' q, a q) ^ 2 := by
        rw [hsa.tsum_mul_left]
        ring
  have hmain :
      2 * (∑' q, b q) ^ 2 ≤ (∑' q, a q) ^ 3 := by
    calc
      2 * (∑' q, b q) ^ 2 ≤
          2 * ((∑' q, a q) * ∑' q, c q) :=
        mul_le_mul_of_nonneg_left hBCsq (by norm_num)
      _ ≤ 2 * ((∑' q, a q) * ∑' q, a q ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hCsq hA) (by norm_num)
      _ ≤ (∑' q, a q) ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hA2 hA]
  have hMone : normalizedPrimeArchMoment 1 = ∑' q, a q := by
    change normalizedPrimeArchMoment 1 =
      ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 2).re
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
      ← tsum_xiZeroCopyReciprocalSquare_pow 1,
      Complex.re_tsum (summable_xiZeroCopyReciprocalSquare_pow 1)]
  have hMtwo : normalizedPrimeArchMoment 2 = ∑' q, b q := by
    change normalizedPrimeArchMoment 2 =
      ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 3).re
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
      ← tsum_xiZeroCopyReciprocalSquare_pow 2,
      Complex.re_tsum (summable_xiZeroCopyReciprocalSquare_pow 2)]
  rw [hMone, hMtwo]
  exact hmain


/-- The raw theta source itself satisfies the sixth spectral law unconditionally.  The mass
normalization cancels, leaving a homogeneous inequality in its first four even moments. -/
theorem thetaCuspRawEvenMoment_sixth_spectral_law :
    3 * (thetaCuspRawEvenMoment 0 ^ 2 * thetaCuspRawEvenMoment 3 -
      15 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
        thetaCuspRawEvenMoment 2 + 30 * thetaCuspRawEvenMoment 1 ^ 3) ^ 2 ≤
      100 * (3 * thetaCuspRawEvenMoment 1 ^ 2 -
        thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) ^ 3 := by
  let a := thetaCuspRawEvenMoment 0
  let b := thetaCuspRawEvenMoment 1
  let c := thetaCuspRawEvenMoment 2
  let d := thetaCuspRawEvenMoment 3
  let q := 3 * b ^ 2 - a * c
  let r := a ^ 2 * d - 15 * a * b * c + 30 * b ^ 3
  change 3 * r ^ 2 ≤ 100 * q ^ 3
  have ha : 0 < a := by
    exact thetaCuspRawEvenMoment_zero_pos
  have hfirst : normalizedPrimeArchMoment 1 = q / (6 * a ^ 2) := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [q, a, b, c, thetaCuspNormalizedEvenMoment]
    field_simp [ha.ne']
    ring
  have hsixth : normalizedPrimeArchMoment 2 = r / (120 * a ^ 3) := by
    rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [r, a, b, c, d, thetaCuspNormalizedEvenMoment]
    field_simp [ha.ne']
    ring
  have hceiling := normalizedPrimeArchMoment_sixth_spectral_ceiling
  rw [hfirst, hsixth] at hceiling
  have hscale : 0 ≤ 21600 * a ^ 6 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hceiling hscale
  have hleft :
      (21600 * a ^ 6) * (2 * (r / (120 * a ^ 3)) ^ 2) = 3 * r ^ 2 := by
    field_simp [ha.ne']
    ring
  have hright :
      (21600 * a ^ 6) * (q / (6 * a ^ 2)) ^ 3 = 100 * q ^ 3 := by
    field_simp [ha.ne']
    ring
  rw [hleft, hright] at hscaled
  exact hscaled

/-- The literal K-RVM carrier has the required non-nuclear spectral boundary: its diagonal is
the nonsummable reciprocal RVM tail outside a finite source-correcting head. -/
theorem routeKQuarticallyAdmittedOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routeKQuarticallyAdmittedOperator := by
  intro htrace
  have hdiag := htrace.one_summable_norm_inner_diag_basis
    (HilbertSchmidt.lpBasis Nat.Primes)
  apply not_summable_routeKPrimeRVMReciprocal
  apply nthPrimeEquiv.summable_iff.mp
  have hdiagNat : Summable (fun n : ℕ =>
      ‖inner ℂ (HilbertSchmidt.lpBasis Nat.Primes (nthPrimeEquiv n))
        (routeKQuarticallyAdmittedOperator
          (HilbertSchmidt.lpBasis Nat.Primes (nthPrimeEquiv n)))‖) :=
    nthPrimeEquiv.summable_iff.mpr hdiag
  apply hdiagNat.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop routeKQuarticReserveParameters.N] with n hn
  rw [HilbertSchmidt.lpBasis_apply]
  change ‖inner ℂ (routeKPrimeBasis (nthPrimeEquiv n))
      (routeKQuarticallyAdmittedOperator (routeKPrimeBasis (nthPrimeEquiv n)))‖ =
    routeKPrimeRVMReciprocal (nthPrimeEquiv n)
  rw [routeKQuarticallyAdmittedOperator_diagonal_of_index_ge
      (by simpa using hn), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (routeKPrimeRVMReciprocal_pos _).le]

/-- The fifth Hilbert--Schmidt trace of the literal K-RVM kernel is the fifth ordinary operator
trace. -/
theorem routeKQuarticallyAdmittedKernel_fifth_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 4 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 5) := by
  rw [← HilbertSchmidt.hsComp_hsPow
    routeKQuarticallyAdmittedKernel_isHS 1 2]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 1)
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 2)]
  rw [HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 1,
    HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 2,
    routeKQuarticallyAdmittedKernel_toOperator]
  congr 1

private theorem opTrace_routeKQuarticallyAdmittedOperator_sq_eq_source :
    ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 2) =
      (routeKSourceZerothMoment : ℂ) / 2 := by
  have h := two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator
  linear_combination h / 2

private theorem opTrace_routeKQuarticallyAdmittedOperator_four_eq_source :
    ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 4) =
      (routeKSourceFirstMoment : ℂ) / 2 := by
  have h := two_mul_opTrace_four_routeKQuarticallyAdmittedOperator
  linear_combination h / 2

/-- The fifth literal determinant jet, retained only to show its cancellation in the signed
eighth reflection coefficient. -/
private theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_five :
    taylorCoeff routeKQuarticallyAdmittedEntireDet 5 =
      -ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 5) / 5 +
        (routeKSourceZerothMoment : ℂ) *
          ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 3) / 12 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    taylorCoeff_entireDet2_eq_detCoeff routeKQuarticallyAdmittedKernel_isHS,
    detCoeff_five_eq_trace routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_fifth_trace,
    routeKQuarticallyAdmittedKernel_square_trace,
    routeKQuarticallyAdmittedKernel_cube_trace,
    opTrace_routeKQuarticallyAdmittedOperator_sq_eq_source]
  ring

/-- The eighth literal determinant jet before the signed reflection cancels its odd trace
coordinates. -/
private theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_eight :
    taylorCoeff routeKQuarticallyAdmittedEntireDet 8 =
      -(∑' p : Nat.Primes,
        HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 7 (p, p)) / 8 +
        (routeKSourceZerothMoment : ℂ) *
          ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) / 24 +
        ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 3) *
          ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 5) / 15 +
        (routeKSourceFirstMoment : ℂ) ^ 2 / 128 -
        (routeKSourceZerothMoment : ℂ) ^ 2 *
          (routeKSourceFirstMoment : ℂ) / 256 -
        (routeKSourceZerothMoment : ℂ) *
          ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 3) ^ 2 / 72 +
        (routeKSourceZerothMoment : ℂ) ^ 4 / 6144 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    taylorCoeff_entireDet2_eq_detCoeff routeKQuarticallyAdmittedKernel_isHS,
    detCoeff_eight_eq_trace routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_sixth_trace,
    routeKQuarticallyAdmittedKernel_fifth_trace,
    routeKQuarticallyAdmittedKernel_square_trace,
    routeKQuarticallyAdmittedKernel_cube_trace,
    routeKQuarticallyAdmittedKernel_fourth_trace,
    opTrace_routeKQuarticallyAdmittedOperator_sq_eq_source,
    opTrace_routeKQuarticallyAdmittedOperator_four_eq_source]
  ring

/-- At degree eight the signed reflection removes every unpaired odd trace, leaving the literal
eighth and sixth spectral coordinates. -/
theorem taylorCoeff_routeKQuarticallySignedReflectionEntireDet_eight :
    taylorCoeff routeKQuarticallySignedReflectionEntireDet 8 =
      -(∑' p : Nat.Primes,
        HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 7 (p, p)) / 4 +
        (routeKSourceZerothMoment : ℂ) *
          ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) / 6 +
        (routeKSourceFirstMoment : ℂ) ^ 2 / 32 -
        (routeKSourceZerothMoment : ℂ) ^ 2 *
          (routeKSourceFirstMoment : ℂ) / 32 +
        (routeKSourceZerothMoment : ℂ) ^ 4 / 384 := by
  unfold routeKQuarticallySignedReflectionEntireDet
  rw [taylorCoeff_reflectionProduct_eight_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable'
    routeKQuarticallyAdmittedEntireDet_zero'
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one',
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_eight,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_three,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_four,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_five,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_six]
  ring

/-- The normalized eighth centered Xi jet is fixed by the first four normalized
prime--archimedean moments. -/
private theorem normalized_XiC_eighth_jet_eq_source_moments :
    iteratedDeriv 8 XiC 0 / XiC 0 / 40320 =
      -(normalizedPrimeArchMoment 3 : ℂ) / 8 +
        (normalizedPrimeArchMoment 0 : ℂ) * (normalizedPrimeArchMoment 2 : ℂ) / 12 +
        (normalizedPrimeArchMoment 1 : ℂ) ^ 2 / 32 -
        (normalizedPrimeArchMoment 0 : ℂ) ^ 2 * (normalizedPrimeArchMoment 1 : ℂ) / 32 +
        (normalizedPrimeArchMoment 0 : ℂ) ^ 4 / 384 := by
  have hm3 : normalizedPrimeArchMoment 3 =
      -thetaCuspNormalizedEvenMoment 4 / 5040 +
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 180 +
        thetaCuspNormalizedEvenMoment 2 ^ 2 / 144 -
        thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 / 12 +
        thetaCuspNormalizedEvenMoment 1 ^ 4 / 8 := by
    apply Complex.ofReal_injective
    push_cast
    have h := normalizedPrimeArchMoment_recursive 3
    norm_num [Finset.sum_range_succ, thetaCuspXiJet,
      thetaCuspPrimeArchProductJet, Nat.choose] at h
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment] at h
    simp only [thetaCuspNormalizedEvenMoment] at h ⊢
    push_cast at h ⊢
    field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at h ⊢
    ring_nf at h ⊢
    linear_combination 38880 * h
  have h0 : XiC 0 = (thetaCuspRawEvenMoment 0 : ℂ) := by
    simpa using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  have h8 : iteratedDeriv 8 XiC 0 = (thetaCuspRawEvenMoment 4 : ℂ) := by
    convert iteratedDeriv_XiC_zero_eq_rawEvenMoment 4 using 1 <;> norm_num
  rw [h0, h8]
  have hreal :
      thetaCuspRawEvenMoment 4 / thetaCuspRawEvenMoment 0 / 40320 =
        -normalizedPrimeArchMoment 3 / 8 +
          normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 / 12 +
          normalizedPrimeArchMoment 1 ^ 2 / 32 -
          normalizedPrimeArchMoment 0 ^ 2 * normalizedPrimeArchMoment 1 / 32 +
          normalizedPrimeArchMoment 0 ^ 4 / 384 := by
    rw [hm3,
      normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
    simp only [thetaCuspNormalizedEvenMoment]
    field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
    ring
  exact_mod_cast hreal

/-- The normalized Xi eighth Taylor coefficient is its fourth source-moment polynomial. -/
theorem taylorCoeff_normalized_XiC_eight :
    taylorCoeff (fun z : ℂ => XiC z / XiC 0) 8 =
      -(normalizedPrimeArchMoment 3 : ℂ) / 8 +
        (normalizedPrimeArchMoment 0 : ℂ) * (normalizedPrimeArchMoment 2 : ℂ) / 12 +
        (normalizedPrimeArchMoment 1 : ℂ) ^ 2 / 32 -
        (normalizedPrimeArchMoment 0 : ℂ) ^ 2 * (normalizedPrimeArchMoment 1 : ℂ) / 32 +
        (normalizedPrimeArchMoment 0 : ℂ) ^ 4 / 384 := by
  rw [taylorCoeff]
  have heq : (fun z : ℂ => XiC z / XiC 0) =
      fun z => (XiC 0)⁻¹ * XiC z := by
    funext z
    ring
  rw [heq, iteratedDeriv_const_mul_field]
  have hrewrite : (Nat.factorial 8 : ℂ)⁻¹ *
      ((XiC 0)⁻¹ * iteratedDeriv 8 XiC 0) =
      iteratedDeriv 8 XiC 0 / XiC 0 / 40320 := by
    norm_num [Nat.factorial]
    ring
  rw [hrewrite, normalized_XiC_eighth_jet_eq_source_moments]

/-- A global signed K-RVM determinant identity forces the literal eighth spectral trace to match
the fourth normalized prime--archimedean moment. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_eighth_trace
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 7 (p, p)) =
      (normalizedPrimeArchMoment 3 : ℂ) := by
  have hcoeff := congrArg (fun f : ℂ → ℂ => taylorCoeff f 8) h
  have hsix := routeKQuarticallySignedReflection_eq_normalized_XiC_imp_sixth_trace h
  have hsix' : ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 6) =
      (normalizedPrimeArchMoment 2 : ℂ) / 2 := by
    linear_combination hsix / 2
  rw [taylorCoeff_routeKQuarticallySignedReflectionEntireDet_eight,
    taylorCoeff_normalized_XiC_eight,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment,
    hsix'] at hcoeff
  linear_combination -8 * hcoeff

/-- The eighth Hilbert--Schmidt kernel trace is the eighth ordinary trace of the literal
self-adjoint K-RVM carrier. -/
theorem routeKQuarticallyAdmittedKernel_eighth_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 7 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 8) := by
  have hpow : routeKQuarticallyAdmittedOperator ^ 4 *
      routeKQuarticallyAdmittedOperator ^ 4 =
      routeKQuarticallyAdmittedOperator ^ 8 := by
    rw [← pow_add]
  have hpowComp :
      (routeKQuarticallyAdmittedOperator ^ (3 + 1)) ∘L
        (routeKQuarticallyAdmittedOperator ^ (3 + 1)) =
        routeKQuarticallyAdmittedOperator ^ 8 := by
    change routeKQuarticallyAdmittedOperator ^ (3 + 1) *
        routeKQuarticallyAdmittedOperator ^ (3 + 1) =
      routeKQuarticallyAdmittedOperator ^ 8
    norm_num
    exact hpow
  rw [← HilbertSchmidt.hsComp_hsPow
    routeKQuarticallyAdmittedKernel_isHS 3 3]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 3)
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 3)]
  rw [HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 3,
    routeKQuarticallyAdmittedKernel_toOperator, hpowComp]

/-- The eighth ordinary trace is the squared Hilbert--Schmidt energy of the fourth power. -/
theorem opTrace_routeKQuarticallyAdmittedOperator_eight_eq_fourth_hsNormSq :
    ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ 8) =
      (ContinuousLinearMap.hsNormSq
        (routeKQuarticallyAdmittedOperator ^ 4) : ℂ) := by
  have hT4 : (routeKQuarticallyAdmittedOperator ^ 4).IsHilbertSchmidt := by
    rw [show 4 = 3 + 1 by norm_num, pow_succ, ContinuousLinearMap.mul_def]
    exact routeKQuarticallyAdmittedOperator_isHilbertSchmidt.comp_left
      (routeKQuarticallyAdmittedOperator ^ 3)
  have hself : IsSelfAdjoint (routeKQuarticallyAdmittedOperator ^ 4) := by
    have hT := routeKQuarticallyAdmittedOperator_isSelfAdjoint
    change star routeKQuarticallyAdmittedOperator =
      routeKQuarticallyAdmittedOperator at hT
    change star (routeKQuarticallyAdmittedOperator ^ 4) =
      routeKQuarticallyAdmittedOperator ^ 4
    rw [star_pow, hT]
  have hpow : routeKQuarticallyAdmittedOperator ^ 8 =
      (routeKQuarticallyAdmittedOperator ^ 4) ^ 2 := by
    noncomm_ring
  rw [hpow]
  exact HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hT4
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp hself)

/-- The eighth signed-determinant constraint is exactly the fourth reflected energy incidence
condition of the literal K-RVM carrier. -/
theorem routeKQuarticallySignedReflection_eq_normalized_XiC_imp_eighth_energy
    (h : routeKQuarticallySignedReflectionEntireDet = fun z : ℂ => XiC z / XiC 0) :
    2 * ContinuousLinearMap.hsNormSq (routeKQuarticallyAdmittedOperator ^ 4) =
      normalizedPrimeArchMoment 3 := by
  have htrace := routeKQuarticallySignedReflection_eq_normalized_XiC_imp_eighth_trace h
  rw [routeKQuarticallyAdmittedKernel_eighth_trace,
    opTrace_routeKQuarticallyAdmittedOperator_eight_eq_fourth_hsNormSq] at htrace
  exact_mod_cast htrace

end

end RHTower
