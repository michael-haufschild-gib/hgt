import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ArithmeticCanonicalPathCalibration
import GaloisForLFunctions.TransHorizonIncidenceMechanics.IntegerJumpEnergyAndBeyondEnvelopeDefect
import GaloisForLFunctions.RHTower.PrimeArchFiniteOrderHausdorffPositivity
import GaloisForLFunctions.RHTower.XiHorizontalSliceLogConcaveCone
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex
import GaloisForLFunctions.RHTower.XiGaussianHeatRouteLadderCapstone
import GaloisForLFunctions.RHTower.PhotonicLosslessTemporalStackRealZeros

/-!
# Concrete finite arithmetic and spectral certificates

These instances use the golden Frobenius datum, the existing prime triangle
and packed prime graph, the horizon-five radical quotient, four Hausdorff
orders, four central-slice Jensen tests, four heat-Hankel ranks, and a
three-slab lossless stack. Every analytic
premise is discharged by the specified object; none asserts a cofinal sign.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SignedArithmeticEnergyIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BezoutValuationIncidence
open Zeta23 RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory
noncomputable section

/-- The two-dimensional golden Frobenius span has exactly one negative square. -/
theorem golden_two_span_certificate : hermNegIndex (goldenDatum.spanGram 2) = 1 :=
  goldenDatum_negIndex_spanGram (by norm_num)

/-- A concrete narrow smooth source realizes that same index on the first two tower levels. -/
theorem golden_two_tower_certificate :
    hermNegIndex (zeroGram (goldenDatum.curveConfig goldenDatum_strip)
      (fun k : Fin 2 => ArithmeticCastelnuovoSeveri.translate
        (((k : ℕ) : ℝ)*Real.log goldenDatum.q)
        (modScaledBump (Real.log goldenDatum.q/4) 0))) = 1 := by
  have hw : 0 < Real.log goldenDatum.q/4 := div_pos goldenDatum.log_q_pos (by norm_num)
  refine goldenDatum_tower_negIndex (g := modScaledBump (Real.log goldenDatum.q/4) 0)
    (A := Real.log goldenDatum.q/2) (n := 2)
    (contDiff_modScaledBump_two _ 0) ?_ ?_ (integral_norm_sq_modScaledBump_pos hw) (by norm_num)
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have h := modScaledBump_support hw 0 x hx
    obtain ⟨hl,hu⟩ := abs_le.mp h
    constructor <;> linarith only [hl,hu]
  · linarith only [goldenDatum.log_q_pos]

/-- Both source-faithful finite graphs have positive supersolutions and nonnegative energy. -/
theorem canonical_prime_path_certificates :
    (∀ i, 0 ≤ couplingAction
      (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget)
      primeTriangleGauge i) ∧
    (∀ f : Fin 3 → ℝ, 0 ≤ incidenceEnergy
      (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget) f) ∧
    (∀ i, 0 ≤ couplingAction
      (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget)
      packedPrimeGauge i) ∧
    (∀ f : Fin 4 → ℝ, 0 ≤ incidenceEnergy
      (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget) f) :=
  ⟨supersolution_primeTriangleCanonical, incidenceEnergy_oddFold_primeTriangleCanonical_nonneg,
    supersolution_packedPrimeCanonical, incidenceEnergy_oddFold_packedPrimeCanonical_nonneg⟩

/-- The actual triangle and packed graph carry their specified shared-path certificates. -/
theorem canonical_prime_path_packings :
    Nonempty (PathCertificate
      (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget)) ∧
    Nonempty (PathCertificate
      (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget)) :=
  ⟨⟨primeTriangleCanonicalPathCertificate⟩,⟨packedPrimeCanonicalPathCertificate⟩⟩

private theorem primorial_five : primorial 5 = 30 := by
  norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ]

/-- Horizon five has only the eight squarefree states dividing thirty. -/
theorem horizon_five_state_certificate (k : ℕ) :
    horizonRadicalState 5 k ∈ ({1,2,3,5,6,10,15,30} : Finset ℕ) := by
  have hd := horizonRadicalState_dvd_primorial 5 k
  rw [primorial_five] at hd
  have hlo := horizonRadicalState_pos 5 k
  have hhi := Nat.le_of_dvd (by norm_num : 0 < 30) hd
  interval_cases hr : horizonRadicalState 5 k <;> norm_num at hd <;> norm_num

/-- The radical-state certificate pays every horizon-five observation at half damping. -/
theorem horizon_five_half_damping_certificate (k : ℕ) :
    |sieveSeq 5 (pmPowerDampedRealWeight (1/2)) k| ≤ 2 := by
  have hd := Nat.le_of_dvd (primorial_pos 5) (horizonRadicalState_dvd_primorial 5 k)
  rw [primorial_five] at hd
  exact abs_sieveSeq_pmPowerDampedRealWeight_le_two_of_radical_lt_six_succ
    (by norm_num) (by omega)

/-- Orders zero through three of the literal prime–Gamma moments share a certified finite shift. -/
theorem four_hausdorff_rows_certificate (j : Fin 4) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment j (finiteOrderHausdorffShift 3) := by
  simpa only [add_zero] using scaledHausdorffMomentDifference_nonneg_finiteOrder 3 0 j

/-- The first four quadratic Jensen discriminants of the actual central slice are nonnegative. -/
theorem four_central_slice_jensen_certificates (k : Fin 4) :
    0 ≤ (2*(xiSliceCoeff 0 (2*((k : ℕ)+1))).re)^2 -
      4*(xiSliceCoeff 0 (2*((k : ℕ)+2))).re*(xiSliceCoeff 0 (2*(k : ℕ))).re := by
  have h := xiSliceCoeff_logConcave_of_cone
    (sqrt3Cone_of_abs_le (t := 0) (by norm_num)) (k : ℕ)
  nlinarith only [h]

/-- Five positive theta moments and their first four adjacent Hankel inequalities. -/
theorem finite_theta_moment_certificate :
    (∀ k : Fin 5, 0 < thetaCuspRawEvenMoment k) ∧
    (∀ k : Fin 4, thetaCuspRawEvenMoment ((k : ℕ)+1)^2 ≤
      thetaCuspRawEvenMoment k * thetaCuspRawEvenMoment ((k : ℕ)+2)) := by
  refine ⟨fun k => thetaCuspRawEvenMoment_pos k, fun k => ?_⟩
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using
    thetaCuspRawEvenMoment_sq_le_adjacent ((k : ℕ)+1) (by omega)

/-- A single explicit heat time certifies the first four leading determinants. -/
theorem four_heat_hankel_determinants_certificate (j : Fin 5) :
    0 < (leadingMatrix (heatMomentArray (routeUCompletedPrimeGammaAperture/4)) j).det := by
  have hk := routeUCompletedPrimeGammaAperture_pos
  apply heatMomentDet_pos_of_mul_le (by positivity : 0 < routeUCompletedPrimeGammaAperture/4)
  have hj : (j : ℝ) ≤ 4 := by exact_mod_cast (show (j : ℕ) ≤ 4 by omega)
  have hm := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ routeUCompletedPrimeGammaAperture/4)
  nlinarith only [hm]

/-- The four certified leading matrices have their exact full ranks. -/
theorem four_heat_hankel_ranks_certificate (j : Fin 5) :
    (leadingMatrix (heatMomentArray (routeUCompletedPrimeGammaAperture/4)) j).rank = j := by
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (four_heat_hankel_determinants_certificate j).ne')), Fintype.card_fin]

/-- Three specified positive impedances and durations. -/
def certifiedThreeSlabStack : List (ℝ × ℝ) := [(1,1),(2,1/2),(1,1)]

private theorem certifiedThreeSlabStack_pos :
    ∀ x ∈ certifiedThreeSlabStack, 0 < x.1 ∧ 0 < x.2 := by
  intro x hx
  simp only [certifiedThreeSlabStack, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> norm_num

/-- The finite lossless stack is entire, even, and has only real transfer zeros. -/
theorem three_slab_stack_certificate :
    Differentiable ℂ (ptrLosslessStackEntry certifiedThreeSlabStack) ∧
    (∀ k, ptrLosslessStackEntry certifiedThreeSlabStack (-k) =
      ptrLosslessStackEntry certifiedThreeSlabStack k) ∧
    (∀ k, ptrLosslessStackEntry certifiedThreeSlabStack k = 0 → k.im = 0) :=
  ⟨ptrLosslessStack_differentiable _ 0 0, ptrLosslessStackEntry_neg _,
    fun _ hk => ptrLosslessStackEntry_zero_im_eq_zero certifiedThreeSlabStack_pos hk⟩

end
end GaloisForLFunctions.ArithmeticOrientationTheory
