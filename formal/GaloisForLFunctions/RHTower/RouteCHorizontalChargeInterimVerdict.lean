import GaloisForLFunctions.RHTower.EulerShiftPairIncidenceCurrent
import GaloisForLFunctions.HTGeometry.HardyLeakageRankOne
import GaloisForLFunctions.RHTower.InfinitesimalXiLeakageCauchyEnergy
import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration
import GaloisForLFunctions.RHTower.ShiftedEulerQuotientCocycleFlatness
import GaloisForLFunctions.RHTower.SelfDualQuartetShiftCurvature
import GaloisForLFunctions.RHTower.ShiftedEulerPrimeOrbitPF2
import GaloisForLFunctions.RHTower.SuzukiArchimedeanPrimitiveSignChange
import GaloisForLFunctions.RHTower.SuzukiEulerPoleArchimedeanMomentAnnihilation
import GaloisForLFunctions.RHTower.SuzukiTailSummatoryErrorTransform
import GaloisForLFunctions.RHTower.ShiftedEulerFloorMobiusTailCoupling

/-!
# Route C horizontal-charge interim verdict

This module packages every closed theorem used by the Route C verdict.  It includes the canonical
Xi Poincare--Lelong pair current and its exact thin slice, the static Hardy-leakage no-go, the
positive first-order Cauchy energy, all finite tangent support grades, flat full-shift cocycle,
self-dual quartet falsifier, one-prime PF2 failure, and the Suzuki source reductions.

The package deliberately contains no claimed absolute four-unit source bound: that is the separate
open arithmetic core, not a premise or hidden field of the theorem below.
-/

open Complex Filter Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra
open scoped BigOperators Topology

namespace RHTower

noncomputable section

open EulerShiftPairIncidenceCurrent

/-- Exact closed content of the Route C interim verdict.  Every field is supplied by a theorem;
no open source bound is encoded as an assumption. -/
structure RouteCHorizontalChargeInterimVerdictPackage : Prop where
  xiPoincareLelong : IsPoincareLelongOfSmooth xi
  sourceCurrentThinSlice : ∀ (T : ℝ) (k : Cutoff),
    Tendsto (xiSourceThinSliceMass T k) (nhdsWithin 0 (Ioi 0))
      (nhds (xiHorizontalCollisionCharge T : ℝ))
  currentCollisionConservation : ∀ T : ℝ,
    xiReducedRealShiftIncidenceCharge T =
      xiStripWindowHorizontalSquareSum T - xiStripWindowTotalOrder T
  localIntersectionProduct : ∀ m n : ℕ, localIntersectionMultiplicity m n = m * n
  quotientCancellation : ∀ m n : ℕ, quotientCancellationMultiplicity m n = min m n
  quotientCarrierMismatch :
    quotientCancellationMultiplicity 2 2 ≠ localIntersectionMultiplicity 2 2
  staticLeakageRankOne : ∀ {α β : ℂ}, ∀ (ha : ‖α‖ < 1) (hb : ‖β‖ < 1),
    blaschkeFactor α β ≠ 0 → ∀ f : HardyDisk,
      ‖f‖ ^ 2 -
          ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) (blaschkeMul ha f)‖ ^ 2 = 0 ↔
        (modelSpace hb).starProjection f = 0
  staticLeakageExactScale : ∀ {a omega : ℝ}, 0 < omega → omega < a →
    ‖blaschkeFactor (cayleyPoint (a + omega)) (cayleyPoint (a - omega))‖ = omega / a
  staticLeakageVanishes : ∀ a : ℝ,
    Tendsto (fun omega : ℝ => omega / a) (nhdsWithin 0 (Ioi 0)) (nhds 0)
  finiteDivisorFirstOrderClosure : ∀ D : FiniteXiRightDivisor,
      (∀ j, 0 < D.depth j ∧ D.depth j < (1 / 2 : ℝ)) ∧
      (∀ t : ℝ, D.profile t =
        2 * ∑ j, Complex.exp
          (-((D.depth j : ℝ) : ℂ) * t - Complex.I * (D.ordinate j : ℂ) * t)) ∧
      (∫ t in Ioi (0 : ℝ), ‖D.profile t‖ ^ 2 = D.energy) ∧
      ((D.curvatureKernel 0 0).re = D.energy) ∧
      (0 < D.card → (4 : ℝ) * D.card < D.energy) ∧
      (∀ W : ℂ, xiCent W ≠ 0 →
        HasDerivAt (fun omega : ℝ => xiShiftTheta omega W)
          (-2 * logDeriv xiCent W) 0)
  tangentPrimeSupportFiltration : ∀ (n k : ℕ), k < n.primeFactors.card →
    iteratedDeriv k (shiftedEulerCoeff n) 0 = 0
  firstEulerTangent : ∀ n : ℕ,
    iteratedDeriv 1 (shiftedEulerCoeff n) 0 =
      2 * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  secondEulerTangent : ∀ n : ℕ,
    iteratedDeriv 2 (shiftedEulerCoeff n) 0 =
      4 * (((ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)
  fullShiftCocycle : ∀ (F : ℂ → ℂ) (omega eta : ℝ) (s : ℂ),
    F (s + (omega : ℂ) - (eta : ℂ)) ≠ 0 →
    shiftedQuotient F (omega + eta) s =
      shiftedQuotient F omega (s - (eta : ℂ)) *
        shiftedQuotient F eta (s + (omega : ℂ))
  fullShiftFlatness : ∀ (F : ℂ → ℂ) (omega eta kappa : ℝ) (s : ℂ),
    F (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) ≠ 0 →
    F (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) ≠ 0 →
    shiftedQuotient F (omega + eta + kappa) s =
      shiftedQuotient F (omega + (eta + kappa)) s
  quartetSelfDual : ∀ a gamma : ℝ, ∀ s : ℂ,
    selfDualQuartet a gamma (1 - s) = selfDualQuartet a gamma s
  quartetSchwarz : ∀ a gamma : ℝ, ∀ s : ℂ,
    selfDualQuartet a gamma ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (selfDualQuartet a gamma s)
  quartetCurvatureCorner : ∀ {a : ℝ}, 0 < a → ∀ gamma : ℝ,
    finiteOfflineCauchyEnergy (selfDualQuartetOffsets a) (selfDualQuartetOrdinates gamma)
        selfDualQuartetMultiplicities =
      4 / a + 4 * a / (a ^ 2 + gamma ^ 2)
  quartetCurvatureUnbounded : ∀ gamma : ℝ,
    Tendsto (fun a : ℝ => 4 / a + 4 * a / (a ^ 2 + gamma ^ 2))
      (nhdsWithin 0 (Ioi 0)) atTop
  positiveEulerOrbitNotPF2 : ∀ {x : ℝ}, 1 < x →
    (∀ k : ℕ, 0 < shiftedEulerOrbitCoeff x k) ∧
      (shiftedEulerOrbitToeplitzTwo x).det < 0
  suzukiArchimedeanSignChange : ∀ {omega : ℝ}, 0 < omega → omega < 1 / 2 →
    ∃ x₁ ∈ Ioo (0 : ℝ) 1, ∃ x₂ ∈ Ioo (0 : ℝ) 1,
      suzukiRealSourceGOne omega x₁ < 0 ∧ 0 < suzukiRealSourceGOne omega x₂
  suzukiEulerPoleMomentAnnihilation : ∀ {omega : ℝ}, 0 < omega →
    HasMellin (suzukiCanonicalG omega) (suzukiEulerPolePoint omega) 0
  suzukiTailIsErrorTransform : ∀ {omega : ℝ}, 0 < omega → ∀ {x : ℝ}, 1 < x →
    suzukiSourceHOneFinite omega x =
      (x : ℂ)⁻¹ * suzukiCoupledErrorStieltjes omega x
        (fun t => suzukiSourceGOne omega (t / x))
  suzukiFloorMobiusTailSplit : ∀ {omega : ℝ}, 0 < omega → ∀ X : ℕ,
    suzukiCoupledError omega X =
      (∑ d ∈ Finset.Icc 1 X, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (d : ℝ) ^ (-omega) * powerSumRemainder omega ((X : ℝ) / (d : ℝ))) -
        (X : ℝ) ^ (1 + omega) / (1 + omega) * mobiusShiftTail omega X

/-- No-argument, unconditional synthesis of every proved Route C mechanism selected by the
interim verdict. -/
theorem routeCHorizontalChargeInterimVerdict_unconditional :
    RouteCHorizontalChargeInterimVerdictPackage := by
  refine {
    xiPoincareLelong := xi_isPoincareLelongOfSmooth
    sourceCurrentThinSlice := tendsto_xiSourceThinSliceMass
    currentCollisionConservation :=
      xiReducedRealShiftIncidenceCharge_eq_horizontalSquare_sub_total
    localIntersectionProduct := localIntersectionMultiplicity_eq_mul
    quotientCancellation := quotientCancellationMultiplicity_eq_min
    quotientCarrierMismatch := reducedQuotient_deletes_productMultiplicity.2.2
    staticLeakageRankOne := ?_
    staticLeakageExactScale := ?_
    staticLeakageVanishes := tendsto_cayleyLeakageNorm_zero
    finiteDivisorFirstOrderClosure := ?_
    tangentPrimeSupportFiltration := ?_
    firstEulerTangent := iteratedDeriv_one_shiftedEulerCoeff
    secondEulerTangent := iteratedDeriv_two_shiftedEulerCoeff
    fullShiftCocycle := ?_
    fullShiftFlatness := ?_
    quartetSelfDual := selfDualQuartet_functional_equation
    quartetSchwarz := selfDualQuartet_schwarz
    quartetCurvatureCorner := ?_
    quartetCurvatureUnbounded := tendsto_selfDualQuartetCornerEnergy_atTop
    positiveEulerOrbitNotPF2 := ?_
    suzukiArchimedeanSignChange := ?_
    suzukiEulerPoleMomentAnnihilation := ?_
    suzukiTailIsErrorTransform := ?_
    suzukiFloorMobiusTailSplit := ?_ }
  · intro α β ha hb hne f
    exact hardyLeakage_eq_zero_iff ha hb hne f
  · intro a omega h0 h1
    exact norm_blaschkeFactor_cayley h0 h1
  · intro D
    exact ⟨(finiteXiRightDivisor_capstone D).1,
      (finiteXiRightDivisor_capstone D).2.1,
      (finiteXiRightDivisor_capstone D).2.2.1,
      (finiteXiRightDivisor_capstone D).2.2.2.1,
      (finiteXiRightDivisor_capstone D).2.2.2.2.1,
      (finiteXiRightDivisor_capstone D).2.2.2.2.2.1⟩
  · intro n k hk
    exact iteratedDeriv_shiftedEulerCoeff_eq_zero n hk
  · intro F omega eta s hmid
    exact shiftedQuotient_cocycle F omega eta s hmid
  · intro F omega eta kappa s h1 h2
    exact shiftedQuotient_curvature_eq F omega eta kappa s h1 h2
  · intro a ha gamma
    exact selfDualQuartetCornerEnergy_eq ha gamma
  · intro x hx
    exact exists_positive_orbit_failing_pf2 hx
  · intro omega h0 hhalf
    exact suzukiRealSourceGOne_sign_change h0 hhalf
  · intro omega h0
    exact hasMellin_suzukiCanonicalG_at_eulerPole h0
  · intro omega h0 x hx
    exact suzukiSourceHOneFinite_eq_coupledErrorStieltjes h0 hx
  · intro omega h0 X
    exact suzukiCoupledError_eq h0 X

end
end RHTower
