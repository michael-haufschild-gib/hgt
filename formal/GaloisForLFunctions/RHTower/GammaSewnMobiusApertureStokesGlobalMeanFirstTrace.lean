import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesGlobalMeanPolarization
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo
import GaloisForLFunctions.RHTower.NuclearRankOneTrace
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.HTGeometry.InfiniteHilbertDispersion
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# First trace of the global-mean physical Pluecker polarization

The nonlocal global-mean construction is an absolutely nuclear ordered double sum, but its
ordinary trace was not previously identified.  This file computes that trace exactly as the
pairwise packet-mean dispersion.  The correction is strictly positive: packets `(0, 0)` and
`(0, 1)` already differ on the physical cell `(0, 0)`.

Consequently the full global-mean trace is the old local covariance trace plus one explicit
positive arithmetic scalar.  Landing on completed Xi's first coefficient is now equivalent to
that scalar being exactly the already-positive first-trace gap.  This closes the first-trace
identification step without assuming RH or fitting any Xi coefficient.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- Every coordinate occurs with positive probability in a physical Pluecker packet. -/
theorem gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos
    (z : ℕ × ℕ) (i : Fin 4) :
    0 < gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i := by
  unfold gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean
  apply Finset.sum_pos'
  · intro s _
    have hsquare := fourRateSelectedSum_coordinateDelta_sq i s
    have hselected : 0 ≤
        RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s := by
      nlinarith [sq_nonneg
        (RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s)]
    exact mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z s).le
      hselected
  · fin_cases i
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
        RHTower.fourRatePairRight, fourRateCoordinateDelta] using
          gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z 0
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
        RHTower.fourRatePairRight, fourRateCoordinateDelta] using
          gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z 0
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      simpa [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
        RHTower.fourRatePairRight, fourRateCoordinateDelta] using
          gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z 1
    · refine ⟨2, Finset.mem_univ _, ?_⟩
      simpa [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
        RHTower.fourRatePairRight, fourRateCoordinateDelta] using
          gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z 2

/-- Two explicit adjacent packets have distinct physical mean vectors. -/
theorem gammaSewnCriticalPhysicalPluckerMeanDifference_zero_right_ne_zero :
    gammaSewnCriticalPhysicalPluckerMeanDifference (0, 0) (0, 1) ≠ 0 := by
  intro h
  have hcoord := congrArg
    (fun v : GammaSewnCriticalPhysicalPluckerHilbert => v (0, 0)) h
  have hnode : 0 < Real.sqrt
      (gammaSewnCriticalPrimeDepthPacket_node 0
        (gammaSewnCriticalAdjacentPrime_lower 0)
        (gammaSewnCriticalAdjacentPrime_upper 0) 0) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  have hmean : 0 < gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean (0, 0) 0 :=
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos _ _
  simp [gammaSewnCriticalPhysicalPluckerMeanDifference,
    gammaSewnCriticalPhysicalPluckerMeanVector,
    gammaSewnCriticalPhysicalPluckerBasis,
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel,
    Fin.sum_univ_four] at hcoord
  rcases hcoord with hcoord | hcoord
  · exact hnode.ne' hcoord
  · exact hmean.ne' hcoord

/-- Exact real nuclear mass of the nonlocal packet-mean dispersion. -/
def gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass : ℝ :=
  ∑' zw : (ℕ × ℕ) × (ℕ × ℕ),
    (1 / 2 : ℝ) *
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
      ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2

theorem summable_gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass :
    Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      (1 / 2 : ℝ) *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2) := by
  exact summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm.congr
    (fun zw => norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw)

/-- The nonlocal trace correction is genuinely present, not a null completion. -/
theorem gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_pos :
    0 < gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass := by
  refine summable_gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass.tsum_pos
    ?_ ((0, 0), (0, 1)) ?_
  · intro zw
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.1).le)
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.2).le)
      (sq_nonneg _)
  · have hdiff : 0 <
        ‖gammaSewnCriticalPhysicalPluckerMeanDifference (0, 0) (0, 1)‖ :=
      norm_pos_iff.mpr
        gammaSewnCriticalPhysicalPluckerMeanDifference_zero_right_ne_zero
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (0, 0)))
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (0, 1)))
      (sq_pos_of_pos hdiff)

theorem opTrace_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    ContinuousLinearMap.opTrace
        (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw) =
      (((1 / 2 : ℝ) *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm,
    RHTower.opTrace_smul_rankOne_self]
  push_cast
  rfl

/-- Canonical ordinary trace of the nonlocal packet-mean dispersion operator. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace : ℂ :=
  ContinuousLinearMap.opTrace
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator

/-- The ordinary trace is exactly the ordered pairwise packet-mean dispersion. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace_eq_nuclearTraceMass :
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace =
      (gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace,
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator,
    RHTower.opTrace_tsum_rankOneTerms_of_summable_norm
      gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
      gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_hasRankLE
      summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm]
  simp_rw [opTrace_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm]
  rw [gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass]
  exact (Complex.ofReal_tsum _).symm

/-- Ordinary trace of the complete local-plus-nonlocal positive polarization. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace : ℂ :=
  ContinuousLinearMap.opTrace
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator

/-- Exact real first-trace mass of the complete global-mean polarization. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass : ℝ :=
  gammaSewnCriticalPhysicalPluckerNuclearTraceMass +
    gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass

/-- Full first-trace law: local covariance plus strictly positive nonlocal dispersion. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace =
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_eq_add,
    RHTower.opTrace_add_of_memSchattenClass_one
      gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one
      gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator_memSchattenClass_one]
  change gammaSewnCriticalPhysicalPluckerSourceTrace +
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace = _
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace_eq_nuclearTraceMass]
  simp [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass]

/-- The nonlocal completion raises the local physical first trace strictly. -/
theorem gammaSewnCriticalPhysicalPluckerNuclearTraceMass_lt_globalMeanPolarized :
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass <
      gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass]
  linarith [gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_pos]

/-- The completed-Xi coefficient leaves a strictly positive gap above the local covariance. -/
theorem gammaSewnCriticalPhysicalPlucker_thetaFirstCoefficientGap_pos :
    0 < thetaCuspNormalizedEvenMoment 1 / 2 -
      gammaSewnCriticalPhysicalPluckerNuclearTraceMass := by
  linarith [gammaSewnCriticalPhysicalPluckerNuclearTraceMass_lt_thetaFirstCoefficient]

/-- Exact first-moment landing criterion for the new C1 global-mean polarization. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace =
        ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) ↔
      gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass =
        thetaCuspNormalizedEvenMoment 1 / 2 -
          gammaSewnCriticalPhysicalPluckerNuclearTraceMass := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass]
  norm_cast
  constructor <;> intro h <;> linarith

/-- Barycenter of the packet-mean vectors under the normalized arithmetic weights. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter :
    GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑' z : ℕ × ℕ,
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z •
      gammaSewnCriticalPhysicalPluckerMeanVector z

/-- Weighted second moment of the packet-mean vectors. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanSecondMoment : ℝ :=
  ∑' z : ℕ × ℕ,
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ^ 2

theorem summable_gammaSewnCriticalPhysicalPluckerBlockWeight_smul_meanVector :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z •
        gammaSewnCriticalPhysicalPluckerMeanVector z) := by
  let C : ℝ := 4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound
  refine Summable.of_norm_bounded
    (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right C) ?_
  intro z
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z)]
  exact mul_le_mul_of_nonneg_left
    (norm_gammaSewnCriticalPhysicalPluckerMeanVector_le z)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le

theorem summable_gammaSewnCriticalPhysicalPluckerBlockWeight_mul_meanVector_norm_sq :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ^ 2) := by
  let C : ℝ := (4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound) ^ 2
  refine Summable.of_nonneg_of_le
    (fun z => mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le (sq_nonneg _))
    (fun z => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (norm_gammaSewnCriticalPhysicalPluckerMeanVector_le z) 2)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le)
    (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right C)

/-- The ordered pairwise correction collapses to one weighted second moment minus the squared
norm of the arithmetic barycenter. -/
theorem gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_eq_secondMoment_sub_barycenter :
    gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass =
      gammaSewnCriticalPhysicalPluckerGlobalMeanSecondMoment -
        ‖gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter‖ ^ 2 := by
  have hpairSummable : Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2) := by
    refine
      (summable_gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass.mul_left 2).congr
        ?_
    intro zw
    ring
  have hpair := GaloisForLFunctions.HTGeometry.tsum_pairwise_hilbert_dispersion
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight
    gammaSewnCriticalPhysicalPluckerMeanVector
    summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight
    summable_gammaSewnCriticalPhysicalPluckerBlockWeight_mul_meanVector_norm_sq
    summable_gammaSewnCriticalPhysicalPluckerBlockWeight_smul_meanVector
    hpairSummable
  rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight] at hpair
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanSecondMoment,
    gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter]
  have hscale :
      (∑' zw : (ℕ × ℕ) × (ℕ × ℕ),
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
          gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
          ‖gammaSewnCriticalPhysicalPluckerMeanVector zw.1 -
            gammaSewnCriticalPhysicalPluckerMeanVector zw.2‖ ^ 2) =
        2 * gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass := by
    rw [gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass, ← tsum_mul_left]
    apply tsum_congr
    intro zw
    rw [gammaSewnCriticalPhysicalPluckerMeanDifference]
    ring
  rw [hscale] at hpair
  nlinarith

/-- Exact squared norm of one packet mean: physical labels are orthogonal within a packet. -/
theorem norm_gammaSewnCriticalPhysicalPluckerMeanVector_sq (z : ℕ × ℕ) :
    ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ^ 2 =
      ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  have hortho : Orthonormal ℂ (fun i : Fin 4 =>
      gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)) := by
    constructor
    · intro i
      exact norm_gammaSewnCriticalPhysicalPluckerBasis _
    · intro i j hij
      rw [inner_gammaSewnCriticalPhysicalPluckerBasis]
      simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z |>.ne hij]
  have hsquare := hortho.orthogonalFamily.norm_sum
    (fun i : Fin 4 =>
      ((Real.sqrt
          (gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ))
    Finset.univ
  calc
    ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ^ 2 =
        ∑ i : Fin 4,
          ‖((Real.sqrt
              (gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ)‖ ^ 2 := by
      simpa [gammaSewnCriticalPhysicalPluckerMeanVector,
        LinearIsometry.toSpanSingleton_apply] using hsquare
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
        Real.sq_sqrt
          (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i).le]

/-- Normalized uncentered first source moment before the global barycenter subtraction. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment : ℝ :=
  ∑' z : ℕ × ℕ,
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      (∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)

/-- Exact source collapse: local Bernoulli covariance plus between-packet dispersion is the
uncentered arithmetic first moment minus the squared global barycenter. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass =
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
        ‖gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter‖ ^ 2 := by
  let localTerm : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      (∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i *
            (1 - gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i))
  let secondTerm : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      (∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2)
  have hlocal : Summable localTerm := by
    have houter :=
      summable_gammaSewnCriticalPhysicalPluckerNuclearTraceMass_terms.prod
    refine houter.congr ?_
    intro z
    rw [tsum_fintype]
    change (∑ s : Fin 6,
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
          ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2) = localTerm z
    unfold localTerm
    calc
      _ = gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          (∑ s : Fin 6,
            gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
              ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by
        rw [gammaSewnCriticalPhysicalPlucker_localNuclearTraceMass_eq_spectralTrace,
          gammaSewnCriticalPhysicalPlucker_localTrace_eq_bernoulliTrace]
  have hsecond : Summable secondTerm := by
    refine
      summable_gammaSewnCriticalPhysicalPluckerBlockWeight_mul_meanVector_norm_sq.congr
        ?_
    intro z
    rw [norm_gammaSewnCriticalPhysicalPluckerMeanVector_sq]
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_eq_secondMoment_sub_barycenter,
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_bernoulliTrace,
    gammaSewnCriticalPhysicalPluckerGlobalMeanSecondMoment,
    gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment]
  simp_rw [norm_gammaSewnCriticalPhysicalPluckerMeanVector_sq]
  rw [← add_sub_assoc]
  change (∑' z, localTerm z) + (∑' z, secondTerm z) -
      ‖gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter‖ ^ 2 = _
  rw [← hlocal.tsum_add hsecond]
  congr 1
  apply tsum_congr
  intro z
  change gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * _ +
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * _ =
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Physical-cell incidence amplitude of all packet means meeting one shared lattice cell. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude
    (u : GammaSewnCriticalPhysicalPluckerIndex) : ℂ :=
  ∑' z : ℕ × ℕ,
    ∑ i : Fin 4,
      if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
        ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          Real.sqrt
            (gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ)
      else 0

/-- At most four adjacent packets can meet one physical prime-depth lattice cell. -/
def gammaSewnCriticalPhysicalPluckerIncidentPackets
    (u : GammaSewnCriticalPhysicalPluckerIndex) : Finset (ℕ × ℕ) :=
  {u, (u.1 - 1, u.2), (u.1, u.2 - 1), (u.1 - 1, u.2 - 1)}

theorem gammaSewnCriticalPhysicalPlucker_packet_mem_incident_of_label_eq
    {z : ℕ × ℕ} {u : GammaSewnCriticalPhysicalPluckerIndex} {i : Fin 4}
    (h : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u) :
    z ∈ gammaSewnCriticalPhysicalPluckerIncidentPackets u := by
  rcases z with ⟨e, n⟩
  rcases u with ⟨a, b⟩
  fin_cases i <;>
    simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel,
      gammaSewnCriticalPhysicalPluckerIncidentPackets] at h ⊢ <;> omega

/-- Cofinal incidence localizes exactly: each cell amplitude is a finite sum over at most four
neighboring packets, including the natural boundary degeneracies. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sum_incidentPackets
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u =
      ∑ z ∈ gammaSewnCriticalPhysicalPluckerIncidentPackets u,
        ∑ i : Fin 4,
          if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
            ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
              Real.sqrt
                (gammaSewnCriticalPrimeDepthPacket_node z.1
                  (gammaSewnCriticalAdjacentPrime_lower z.2)
                  (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ)
          else 0 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude, tsum_eq_sum]
  intro z hz
  apply Finset.sum_eq_zero
  intro i _
  have hne : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i ≠ u := by
    intro h
    exact hz
      (gammaSewnCriticalPhysicalPlucker_packet_mem_incident_of_label_eq h)
  simp [hne]

/-- Positive contribution of one packet coordinate to its physical-cell incidence amplitude. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm
    (z : ℕ × ℕ) (i : Fin 4) : ℂ :=
  ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
    Real.sqrt
      (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ)

/-- Interior physical cells receive exactly four source contributions, one from each neighboring
packet; the cofinal incidence sum has no hidden long-range tail at a fixed cell. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_interior
    {e n : ℕ} (he : 0 < e) (hn : 0 < n) :
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude (e, n) =
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (e, n) 0 +
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (e - 1, n) 1 +
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (e, n - 1) 2 +
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (e - 1, n - 1) 3 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sum_incidentPackets]
  have hA : (e, n) ∉
      ({(e - 1, n), (e, n - 1), (e - 1, n - 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hB : (e - 1, n) ∉
      ({(e, n - 1), (e - 1, n - 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hC : (e, n - 1) ∉
      ({(e - 1, n - 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hepred : e - 1 + 1 = e := Nat.sub_add_cancel (by omega)
  have hnpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have he_ne : e - 1 ≠ e := by omega
  have hn_ne : n - 1 ≠ n := by omega
  rw [show gammaSewnCriticalPhysicalPluckerIncidentPackets (e, n) =
      ({(e, n), (e - 1, n), (e, n - 1), (e - 1, n - 1)} :
        Finset (ℕ × ℕ)) by rfl,
    Finset.sum_insert hA, Finset.sum_insert hB, Finset.sum_insert hC]
  simp [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel,
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm,
    Fin.sum_univ_four, hepred, hnpred, he_ne, hn_ne]
  ring

/-- The boundary cell `(0,0)` has exactly one incident packet-coordinate contribution. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_zero_zero :
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude (0, 0) =
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (0, 0) 0 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sum_incidentPackets]
  simp [gammaSewnCriticalPhysicalPluckerIncidentPackets,
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel,
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm,
    Fin.sum_univ_four]

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm_zero_zero_re_pos :
    0 < (gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm (0, 0) 0).re := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm, Complex.ofReal_re]
  exact mul_pos
    (mul_pos
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (0, 0))
      (Real.sqrt_pos.2
        (gammaSewnCriticalPrimeDepthPacket_node_pos 0
          (gammaSewnCriticalAdjacentPrime_lower 0)
          (gammaSewnCriticalAdjacentPrime_upper 0) 0)))
    (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos (0, 0) 0)

theorem inner_basis_gammaSewnCriticalPhysicalPluckerMeanVector
    (z : ℕ × ℕ) (u : GammaSewnCriticalPhysicalPluckerIndex) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerBasis u)
        (gammaSewnCriticalPhysicalPluckerMeanVector z) =
      ∑ i : Fin 4,
        if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
          ((Real.sqrt
            (gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ)
        else 0 := by
  rw [gammaSewnCriticalPhysicalPluckerMeanVector, inner_sum]
  simp only [inner_smul_right, inner_gammaSewnCriticalPhysicalPluckerBasis]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all [eq_comm]

/-- The barycenter coordinate is exactly the accumulated amplitude from incident packets. -/
theorem inner_basis_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    inner ℂ (gammaSewnCriticalPhysicalPluckerBasis u)
        gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter =
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter,
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude]
  change (innerSL ℂ (gammaSewnCriticalPhysicalPluckerBasis u))
      (∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z •
          gammaSewnCriticalPhysicalPluckerMeanVector z) = _
  rw [(innerSL ℂ (gammaSewnCriticalPhysicalPluckerBasis u)).map_tsum
    summable_gammaSewnCriticalPhysicalPluckerBlockWeight_smul_meanVector]
  apply tsum_congr
  intro z
  rw [innerSL_apply_apply,
    ← IsScalarTower.algebraMap_smul ℂ
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z)
      (gammaSewnCriticalPhysicalPluckerMeanVector z),
    inner_smul_right, inner_basis_gammaSewnCriticalPhysicalPluckerMeanVector]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all
  ring

/-- The source barycenter cannot vanish: its boundary cell `(0,0)` is strictly positive. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_ne_zero :
    gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter ≠ 0 := by
  intro hzero
  have hcoord :=
    inner_basis_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter (0, 0)
  rw [hzero, inner_zero_right,
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_zero_zero] at hcoord
  have hpos :=
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceTerm_zero_zero_re_pos
  rw [← hcoord] at hpos
  norm_num at hpos

/-- Parseval exposes the barycenter penalty as an explicit physical-incidence square sum. -/
theorem norm_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_sq_eq_tsum_incidenceAmplitude :
    ‖gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter‖ ^ 2 =
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        ‖gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u‖ ^ 2 := by
  rw [GaloisForLFunctions.HTGeometry.lp_two_norm_sq_eq_tsum]
  apply tsum_congr
  intro u
  have hcoord : gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter u =
      gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u := by
    rw [← inner_basis_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter]
    simp [gammaSewnCriticalPhysicalPluckerBasis, lp.inner_single_left]
  rw [hcoord]

/-- Fully scalar source law: uncentered packet mass minus shared-cell incidence energy. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_incidenceAmplitude :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass =
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          ‖gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u‖ ^ 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter,
    norm_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_sq_eq_tsum_incidenceAmplitude]

/-- Shared-cell collisions remove a strictly positive amount from the uncentered source moment. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_lt_rawFirstMoment :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass <
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter]
  exact sub_lt_self _
    (sq_pos_of_pos
      (norm_pos_iff.mpr
        gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_ne_zero))

theorem gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_two_div_twentyFive
    (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) <
      (2 / 25 : ℝ) := by
  calc
    _ ≤ ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right
        (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).2
    _ < _ :=
      gammaSewnCriticalPhysicalPlucker_packetNode_sum_lt_two_div_twentyFive z

theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        (∑ i : Fin 4,
          gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)) := by
  refine Summable.of_nonneg_of_le ?_ ?_
    (summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right
      (2 / 25 : ℝ))
  · intro z
    exact mul_nonneg
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
      (Finset.sum_nonneg fun i _ => mul_nonneg
        (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).1)
  · intro z
    exact mul_le_mul_of_nonneg_left
      (gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_two_div_twentyFive z).le
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le

/-- The exact uncentered source moment stays below the packet-node ceiling. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment_lt_two_div_twentyFive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment < (2 / 25 : ℝ) := by
  let f : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      (∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)
  let g : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * (2 / 25 : ℝ)
  have hf : Summable f :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment
  have hg : Summable g :=
    summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right (2 / 25 : ℝ)
  have hle : f ≤ g := fun z => mul_le_mul_of_nonneg_left
    (gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_two_div_twentyFive z).le
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hstrict : f (0, 0) < g (0, 0) :=
    mul_lt_mul_of_pos_left
      (gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_two_div_twentyFive
        (0, 0))
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (0, 0))
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment]
  change ∑' z, f z < _
  calc
    ∑' z, f z < ∑' z, g z :=
      Summable.tsum_lt_tsum hle hstrict hf hg
    _ = (∑' z, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
        (2 / 25 : ℝ) := by rw [tsum_mul_right]
    _ = _ := by
      rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]
      norm_num

/-- Global-mean completion stays inside the strict universal packet-node ceiling. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_lt_two_div_twentyFive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass <
      (2 / 25 : ℝ) := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter]
  exact (sub_le_self _ (sq_nonneg _)).trans_lt
    gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment_lt_two_div_twentyFive

/-- Completed-Xi first-coefficient landing is now one explicit scalar identity, with no hidden
double sum or operator trace. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_rawFirstMoment :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace =
        ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) ↔
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
          ‖gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter‖ ^ 2 =
        thetaCuspNormalizedEvenMoment 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter]
  norm_cast

/-- Completed-Xi first-coefficient landing after expanding every shared physical-cell incidence. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_incidenceAmplitude :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace =
        ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) ↔
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
          ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
            ‖gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u‖ ^ 2 =
        thetaCuspNormalizedEvenMoment 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_incidenceAmplitude]
  norm_cast

end RHTower.HedenmalmThetaSource
