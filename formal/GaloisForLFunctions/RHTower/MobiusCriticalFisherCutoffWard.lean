import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.HTGeometry.RankTwoFisherCutoffWard
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift

/-!
# Squarefree-Mobius hard-cutoff Fisher Ward law

The critical squarefree clock is realized as a genuine orthogonal coordinate cutoff on the
completed signed source and Fisher tangent.  Its state mass is identified with the already
constructed clock CDF, the truncated overlap is proved real, and the complex rank-two cutoff law
therefore specializes without projection, adjoint, or phase hypotheses.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open ContinuousLinearMap

/-- Hard lower clock window on the squarefree critical carrier. -/
def squarefreeMobiusCriticalClockCut (sigma u : ℝ) : Set ℕ :=
  {n | squarefreeMobiusCriticalClock sigma n ≤ u}

/-- Orthogonal projection onto a hard lower clock window. -/
def squarefreeMobiusCriticalClockCutoff (sigma u : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpCoordinateProjection (squarefreeMobiusCriticalClockCut sigma u)

@[simp] theorem squarefreeMobiusCriticalClockCutoff_apply
    (sigma u : ℝ) (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    squarefreeMobiusCriticalClockCutoff sigma u x n =
      (squarefreeMobiusCriticalClockCut sigma u).indicator (fun j => x j) n := by
  rfl

/-- The hard clock cutoff discharges the idempotence interface. -/
theorem squarefreeMobiusCriticalClockCutoff_idempotent (sigma u : ℝ) :
    IsIdempotentElem (squarefreeMobiusCriticalClockCutoff sigma u) :=
  lpCoordinateProjection_idempotent _

/-- The hard clock cutoff discharges the self-adjointness interface. -/
theorem squarefreeMobiusCriticalClockCutoff_selfAdjoint (sigma u : ℝ) :
    ContinuousLinearMap.adjoint (squarefreeMobiusCriticalClockCutoff sigma u) =
      squarefreeMobiusCriticalClockCutoff sigma u :=
  lpCoordinateProjection_selfAdjoint _

/-- Probability mass below a hard squarefree critical-clock cutoff. -/
def squarefreeMobiusCriticalClockCutMass (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
    (squarefreeMobiusProbability sigma) n

/-- The hard Hilbert cutoff mass is exactly the measure-theoretic critical-clock CDF. -/
theorem squarefreeMobiusCriticalClockCutMass_eq_CDF
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalClockCutMass sigma u =
      squarefreeMobiusCriticalClockCDF sigma u := by
  rw [squarefreeMobiusCriticalClockCDF, ProbabilityTheory.cdf_eq_real,
    measureReal_def]
  unfold squarefreeMobiusCriticalClockProbabilityMeasure
    squarefreeMobiusCriticalIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
    measurableSet_Iic]
  rw [(squarefreeMobiusCriticalPMF sigma).toMeasure_apply
    MeasurableSet.of_discrete]
  rw [ENNReal.tsum_toReal_eq (fun n => by
    by_cases hn : n ∈ squarefreeMobiusCriticalClock sigma ⁻¹' Iic u
    · rw [indicator_of_mem hn]
      exact (squarefreeMobiusCriticalPMF sigma).apply_ne_top n
    · rw [indicator_of_notMem hn]
      exact ENNReal.zero_ne_top)]
  unfold squarefreeMobiusCriticalClockCutMass
  change (∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
      (squarefreeMobiusProbability sigma) n) =
    ∑' n : ℕ, ((squarefreeMobiusCriticalClockCut sigma u).indicator
      (squarefreeMobiusCriticalPMF sigma) n).toReal
  apply tsum_congr
  intro n
  by_cases hn : n ∈ squarefreeMobiusCriticalClockCut sigma u
  · rw [indicator_of_mem hn, indicator_of_mem]
    · exact (squarefreeMobiusCriticalPMF_toReal hsigma n).symm
    · exact hn
  · rw [indicator_of_notMem hn, indicator_of_notMem hn]
    exact ENNReal.toReal_zero.symm

/-- The hard-cutoff Hilbert mass inherits the exponential critical-clock profile. -/
theorem tendsto_squarefreeMobiusCriticalClockCutMass (u : ℝ) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusCriticalClockCutMass sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if 0 ≤ u then 1 - Real.exp (-u) else 0)) := by
  apply (tendsto_squarefreeMobiusCriticalClockCDF u).congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact (squarefreeMobiusCriticalClockCutMass_eq_CDF hsigma).symm

/-- Fisher-tangent energy below a hard squarefree critical-clock cutoff. -/
def squarefreeMobiusCriticalFisherCutEnergy (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
    (fun n => 4 * (sigma - 1) ^ 2 * squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ 2) n

/-- Real state--tangent overlap below a hard squarefree critical-clock cutoff. -/
def squarefreeMobiusCriticalFisherCutOverlap (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, (squarefreeMobiusCriticalClockCut sigma u).indicator
    (fun n => -2 * (sigma - 1) * squarefreeMobiusProbability sigma n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) n

/-- Exact state-mass value relation for the hard clock cutoff. -/
theorem norm_squarefreeMobiusCriticalClockCutoff_signed_sq
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    ‖squarefreeMobiusCriticalClockCutoff sigma u
      (infiniteMobiusSignedWeightLp sigma hsigma)‖ ^ 2 =
        squarefreeMobiusCriticalClockCutMass sigma u := by
  rw [squarefreeMobiusCriticalClockCutoff, norm_lpCoordinateProjection_sq]
  unfold squarefreeMobiusCriticalClockCutMass
  apply tsum_congr
  intro n
  by_cases hn : n ∈ squarefreeMobiusCriticalClockCut sigma u
  · rw [indicator_of_mem hn, indicator_of_mem hn]
    exact norm_infiniteMobiusSignedWeight_sq hsigma n
  · rw [indicator_of_notMem hn, indicator_of_notMem hn]

/-- The squared hard-cutoff state norm is the existing clock CDF. -/
theorem norm_squarefreeMobiusCriticalClockCutoff_signed_sq_eq_CDF
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    ‖squarefreeMobiusCriticalClockCutoff sigma u
      (infiniteMobiusSignedWeightLp sigma hsigma)‖ ^ 2 =
        squarefreeMobiusCriticalClockCDF sigma u := by
  rw [norm_squarefreeMobiusCriticalClockCutoff_signed_sq hsigma,
    squarefreeMobiusCriticalClockCutMass_eq_CDF hsigma]

private theorem norm_infiniteMobiusCriticalFisherTangentWeight_sq'
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2 =
      4 * (sigma - 1) ^ 2 * squarefreeMobiusProbability sigma n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma) ^ 2 := by
  rw [infiniteMobiusCriticalFisherTangentWeight, norm_mul, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

/-- Exact Fisher-energy value relation for the hard clock cutoff. -/
theorem norm_squarefreeMobiusCriticalClockCutoff_fisherTangent_sq
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    ‖squarefreeMobiusCriticalClockCutoff sigma u
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)‖ ^ 2 =
        squarefreeMobiusCriticalFisherCutEnergy sigma u := by
  rw [squarefreeMobiusCriticalClockCutoff, norm_lpCoordinateProjection_sq]
  unfold squarefreeMobiusCriticalFisherCutEnergy
  apply tsum_congr
  intro n
  by_cases hn : n ∈ squarefreeMobiusCriticalClockCut sigma u
  · rw [indicator_of_mem hn, indicator_of_mem hn]
    exact norm_infiniteMobiusCriticalFisherTangentWeight_sq' hsigma n
  · rw [indicator_of_notMem hn, indicator_of_notMem hn]

/-- Exact state--tangent overlap value relation for the hard clock cutoff. -/
theorem inner_squarefreeMobiusCriticalClockCutoff_fisherTangent_signed
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    inner ℂ
      (squarefreeMobiusCriticalClockCutoff sigma u
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
      (squarefreeMobiusCriticalClockCutoff sigma u
        (infiniteMobiusSignedWeightLp sigma hsigma)) =
      (squarefreeMobiusCriticalFisherCutOverlap sigma u : ℂ) := by
  rw [squarefreeMobiusCriticalClockCutoff, inner_lpCoordinateProjection]
  unfold squarefreeMobiusCriticalFisherCutOverlap
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ squarefreeMobiusCriticalClockCut sigma u
  · rw [indicator_of_mem hn, indicator_of_mem hn]
    simp only [infiniteMobiusCriticalFisherTangentLp, infiniteMobiusSignedWeightLp,
      RCLike.inner_apply, infiniteMobiusCriticalFisherTangentWeight, map_mul,
      Complex.conj_ofReal]
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_infiniteMobiusSignedWeight_sq hsigma]
    calc
      _ = ((-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
            (infiniteMobiusSignedWeight sigma n *
              (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
      _ = _ := by rw [hnorm]; push_cast; ring
  · rw [indicator_of_notMem hn, indicator_of_notMem hn]
    norm_num

/-- The squarefree carrier discharges the complex phase interface: its hard-cutoff overlap is
real at every `sigma > 1` and every window. -/
theorem inner_squarefreeMobiusCriticalClockCutoff_fisherTangent_signed_im_eq_zero
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    (inner ℂ
      (squarefreeMobiusCriticalClockCutoff sigma u
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
      (squarefreeMobiusCriticalClockCutoff sigma u
        (infiniteMobiusSignedWeightLp sigma hsigma))).im = 0 := by
  rw [inner_squarefreeMobiusCriticalClockCutoff_fisherTangent_signed hsigma]
  exact Complex.ofReal_im _

/-- Exact phase-free rank-two Ward law for the squarefree critical Fisher carrier. -/
theorem hsNormSq_squarefreeMobiusCriticalFisherCutoffCommutator
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    hsNormSq
      (cutoffCommutator (squarefreeMobiusCriticalClockCutoff sigma u)
        (pointedFisherConnection
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))) =
      (squarefreeMobiusCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalFisherCutEnergy sigma u) *
        squarefreeMobiusCriticalClockCutMass sigma u +
      (1 - squarefreeMobiusCriticalClockCutMass sigma u) *
        squarefreeMobiusCriticalFisherCutEnergy sigma u -
      2 * squarefreeMobiusCriticalFisherCutOverlap sigma u ^ 2 := by
  rw [hsNormSq_pointedFisherConnection_cutoffCommutator
      (squarefreeMobiusCriticalClockCutoff sigma u)
      (squarefreeMobiusCriticalClockCutoff_idempotent sigma u)
      (squarefreeMobiusCriticalClockCutoff_selfAdjoint sigma u)
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero hsigma),
    norm_infiniteMobiusCriticalFisherTangentLp_sq hsigma,
    norm_squarefreeMobiusCriticalClockCutoff_fisherTangent_sq hsigma,
    norm_infiniteMobiusSignedWeightLp_sq hsigma,
    norm_squarefreeMobiusCriticalClockCutoff_signed_sq hsigma,
    inner_squarefreeMobiusCriticalClockCutoff_fisherTangent_signed hsigma]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- CDF form of the squarefree rank-two Ward law, joining the Hilbert cutoff directly to the
existing critical-clock weak-convergence interface. -/
theorem hsNormSq_squarefreeMobiusCriticalFisherCutoffCommutator_eq_CDF
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    hsNormSq
      (cutoffCommutator (squarefreeMobiusCriticalClockCutoff sigma u)
        (pointedFisherConnection
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))) =
      (squarefreeMobiusCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalFisherCutEnergy sigma u) *
        squarefreeMobiusCriticalClockCDF sigma u +
      (1 - squarefreeMobiusCriticalClockCDF sigma u) *
        squarefreeMobiusCriticalFisherCutEnergy sigma u -
      2 * squarefreeMobiusCriticalFisherCutOverlap sigma u ^ 2 := by
  rw [hsNormSq_squarefreeMobiusCriticalFisherCutoffCommutator hsigma,
    squarefreeMobiusCriticalClockCutMass_eq_CDF hsigma]

end RHTower
