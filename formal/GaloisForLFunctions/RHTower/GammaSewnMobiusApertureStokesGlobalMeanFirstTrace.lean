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

/-- The reverse-incidence fibre has sharp uniform multiplicity at most four, including boundary
degeneracies where truncated predecessors coincide. -/
theorem gammaSewnCriticalPhysicalPluckerIncidentPackets_card_le_four
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    (gammaSewnCriticalPhysicalPluckerIncidentPackets u).card ≤ 4 := by
  unfold gammaSewnCriticalPhysicalPluckerIncidentPackets
  have h0 := Finset.card_insert_le u
    ({(u.1 - 1, u.2), (u.1, u.2 - 1), (u.1 - 1, u.2 - 1)} : Finset (ℕ × ℕ))
  have h1 := Finset.card_insert_le (u.1 - 1, u.2)
    ({(u.1, u.2 - 1), (u.1 - 1, u.2 - 1)} : Finset (ℕ × ℕ))
  have h2 := Finset.card_insert_le (u.1, u.2 - 1)
    ({(u.1 - 1, u.2 - 1)} : Finset (ℕ × ℕ))
  simp only [Finset.card_singleton] at h0 h1 h2 ⊢
  omega

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

/-- Every Pluecker state selects two coordinates, so the four packet marginals have exact
occupation number two. -/
theorem sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean (z : ℕ × ℕ) :
    ∑ i : Fin 4, gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i = 2 := by
  unfold gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean
  rw [Finset.sum_comm]
  calc
    ∑ s : Fin 6, ∑ i : Fin 4,
        gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s =
        ∑ s : Fin 6, gammaSewnCriticalAdjacentPrime_PluckerProbability z s * 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      congr 1
      fin_cases s <;>
        simp [Fin.sum_univ_four, RHTower.fourRateSelectedSum,
          RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
          fourRateCoordinateDelta] <;> norm_num
    _ = 2 := by
      have hsum := sum_gammaSewnCriticalAdjacentPrime_PluckerProbability z
      simpa [← Finset.sum_mul] using congrArg (fun x : ℝ => x * 2) hsum

private theorem squaredReciprocalGapNode_depth_lt_of_base_lt
    (p : Nat.Primes) (e : ℕ) {c : ℝ}
    (hc : RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, 0) < c) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, e) < c := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq]
  let B := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    (1 / 2) (p, 0)
  let d := ((e : ℝ) + 1) ^ 2
  have hB : 0 ≤ B :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) (p, 0)).le
  have hd1 : 1 ≤ d := by
    have he : (0 : ℝ) ≤ e := by positivity
    dsimp [d]
    nlinarith [sq_nonneg ((e : ℝ) + 1)]
  change B / d < c
  exact (div_le_self hB hd1).trans_lt hc

private theorem squaredReciprocalGapNode_succ_depth_lt_quarter_of_base_lt
    (p : Nat.Primes) (e : ℕ) {c : ℝ}
    (hc : RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, 0) < c) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
        (1 / 2) (p, e + 1) < c / 4 := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq]
  let B := RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    (1 / 2) (p, 0)
  let d := (((e + 1 : ℕ) : ℝ) + 1) ^ 2
  have hB : 0 ≤ B :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num) (p, 0)).le
  have hd4 : 4 ≤ d := by
    dsimp [d]
    push_cast
    have he : (0 : ℝ) ≤ e := by positivity
    nlinarith [sq_nonneg ((e : ℝ) + 2)]
  have hdiv : B / d ≤ B / 4 :=
    div_le_div_of_nonneg_left hB (by norm_num) hd4
  change B / d < c / 4
  exact hdiv.trans_lt (div_lt_div_of_pos_right hc (by norm_num))

private theorem adjacentPrime_lower_baseNode_lt_one_div_twentyFive (n : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
      (gammaSewnCriticalAdjacentPrime_lower n, 0) < (1 / 25 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have heq : gammaSewnCriticalAdjacentPrime_lower 0 =
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo := by
      apply Subtype.ext
      norm_num [gammaSewnCriticalAdjacentPrime_lower, RHTower.nthPrimeSubtype]
    rw [heq]
    exact RHTower.gammaSewnMobiusApertureStokesPrimeTwo_baseNode_lt_one_div_twentyFive
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    have hmono := RHTower.nthPrimeSubtype_strictMono hn0
    change (RHTower.nthPrimeSubtype 0 : ℕ) <
      (RHTower.nthPrimeSubtype n : ℕ) at hmono
    have hthree : 3 ≤ (gammaSewnCriticalAdjacentPrime_lower n : ℕ) := by
      norm_num [RHTower.nthPrimeSubtype] at hmono
      exact hmono
    exact (RHTower.gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
      (gammaSewnCriticalAdjacentPrime_lower n) hthree).trans (by norm_num)

private theorem adjacentPrime_upper_baseNode_lt_three_div_oneTwentyFive (n : ℕ) :
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
      (gammaSewnCriticalAdjacentPrime_upper n, 0) < (3 / 125 : ℝ) := by
  have hmono := RHTower.nthPrimeSubtype_strictMono (Nat.succ_pos n)
  change (RHTower.nthPrimeSubtype 0 : ℕ) <
    (RHTower.nthPrimeSubtype (n + 1) : ℕ) at hmono
  have hthree : 3 ≤ (gammaSewnCriticalAdjacentPrime_upper n : ℕ) := by
    norm_num [RHTower.nthPrimeSubtype] at hmono
    exact hmono
  exact RHTower.gammaSewnMobiusApertureStokes_baseNode_lt_three_div_oneTwentyFive_of_three_le
    (gammaSewnCriticalAdjacentPrime_upper n) hthree

/-- Ordered packet nodes admit coordinatewise rational ceilings.  Their two largest possible
ceilings are the two depth-zero prime cells. -/
theorem gammaSewnCriticalPhysicalPlucker_packetNode_coordinate_bounds (z : ℕ × ℕ) :
    gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) 0 < (1 / 25 : ℝ) ∧
    gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) 1 < (1 / 100 : ℝ) ∧
    gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) 2 < (3 / 125 : ℝ) ∧
    gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) 3 < (3 / 500 : ℝ) := by
  have hp := adjacentPrime_lower_baseNode_lt_one_div_twentyFive z.2
  have hq := adjacentPrime_upper_baseNode_lt_three_div_oneTwentyFive z.2
  constructor
  · simpa [gammaSewnCriticalPrimeDepthPacket_node,
      gammaSewnOrderedPrimeDepthPlucker_cell] using
      squaredReciprocalGapNode_depth_lt_of_base_lt
        (gammaSewnCriticalAdjacentPrime_lower z.2) z.1 hp
  constructor
  · have h := squaredReciprocalGapNode_succ_depth_lt_quarter_of_base_lt
      (gammaSewnCriticalAdjacentPrime_lower z.2) z.1 hp
    norm_num at h ⊢
    simpa [gammaSewnCriticalPrimeDepthPacket_node,
      gammaSewnOrderedPrimeDepthPlucker_cell] using h
  constructor
  · simpa [gammaSewnCriticalPrimeDepthPacket_node,
      gammaSewnOrderedPrimeDepthPlucker_cell] using
      squaredReciprocalGapNode_depth_lt_of_base_lt
        (gammaSewnCriticalAdjacentPrime_upper z.2) z.1 hq
  · have h := squaredReciprocalGapNode_succ_depth_lt_quarter_of_base_lt
      (gammaSewnCriticalAdjacentPrime_upper z.2) z.1 hq
    norm_num at h ⊢
    simpa [gammaSewnCriticalPrimeDepthPacket_node,
      gammaSewnOrderedPrimeDepthPlucker_cell] using h

/-- Rank-two occupation sharpens the naive sum-of-four-nodes packet ceiling from `2/25` to
`8/125`, the sum of the two largest coordinate ceilings. -/
theorem gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_eight_div_oneTwentyFive
    (z : ℕ × ℕ) :
    (∑ i : Fin 4,
      gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i) <
      (8 / 125 : ℝ) := by
  let node : Fin 4 → ℝ := fun i =>
    gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i
  let mean : Fin 4 → ℝ := fun i =>
    gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i
  have hn := gammaSewnCriticalPhysicalPlucker_packetNode_coordinate_bounds z
  have hm0 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z 0
  have hm1 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z 1
  have hm2 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z 2
  have hm3 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z 3
  have hp0 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos z 0
  have hp1 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos z 1
  have hp2 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos z 2
  have hp3 := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos z 3
  have hsum := sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z
  change ∑ i : Fin 4, node i * mean i < _
  change node 0 < (1 / 25 : ℝ) ∧ node 1 < (1 / 100 : ℝ) ∧
      node 2 < (3 / 125 : ℝ) ∧ node 3 < (3 / 500 : ℝ) at hn
  change mean 0 ∈ Set.Icc (0 : ℝ) 1 at hm0
  change mean 1 ∈ Set.Icc (0 : ℝ) 1 at hm1
  change mean 2 ∈ Set.Icc (0 : ℝ) 1 at hm2
  change mean 3 ∈ Set.Icc (0 : ℝ) 1 at hm3
  rcases hm0 with ⟨hm0l, hm0u⟩
  rcases hm1 with ⟨hm1l, hm1u⟩
  rcases hm2 with ⟨hm2l, hm2u⟩
  rcases hm3 with ⟨hm3l, hm3u⟩
  change 0 < mean 0 at hp0
  change 0 < mean 1 at hp1
  change 0 < mean 2 at hp2
  change 0 < mean 3 at hp3
  simp only [Fin.sum_univ_four] at hsum
  change mean 0 + mean 1 + mean 2 + mean 3 = 2 at hsum
  rw [Fin.sum_univ_four]
  have hterm0 : node 0 * mean 0 < (1 / 25 : ℝ) * mean 0 :=
    mul_lt_mul_of_pos_right hn.1 hp0
  have hterm1 : node 1 * mean 1 < (1 / 100 : ℝ) * mean 1 :=
    mul_lt_mul_of_pos_right hn.2.1 hp1
  have hterm2 : node 2 * mean 2 < (3 / 125 : ℝ) * mean 2 :=
    mul_lt_mul_of_pos_right hn.2.2.1 hp2
  have hterm3 : node 3 * mean 3 < (3 / 500 : ℝ) * mean 3 :=
    mul_lt_mul_of_pos_right hn.2.2.2 hp3
  linarith

/-- Node-free occupation amplitude at one physical cell.  It records marginal mass before the
reciprocal-gap square-root embedding. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude
    (u : GammaSewnCriticalPhysicalPluckerIndex) : ℝ :=
  ∑' z : ℕ × ℕ,
    ∑ i : Fin 4,
      if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i
      else 0

private def gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
    (zu : (ℕ × ℕ) × GammaSewnCriticalPhysicalPluckerIndex) : ℝ :=
  ∑ i : Fin 4,
    if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel zu.1 i = zu.2 then
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zu.1 *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean zu.1 i
    else 0

private theorem gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg :
    0 ≤ gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel := by
  intro zu
  exact Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact mul_nonneg
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zu.1).le
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem zu.1 i).1
    · exact le_rfl

private theorem tsum_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_right
    (z : ℕ × ℕ) :
    ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * 2 := by
  let term : Fin 4 → GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun i u =>
    if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i
    else 0
  have hterm (i : Fin 4) : Summable (term i) := by
    change Summable (fun u => if _ = u then _ else 0)
    simpa only [eq_comm] using
      (hasSum_ite_eq
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)).summable
  change ∑' u, ∑ i : Fin 4, term i u = _
  simp_rw [Fin.sum_univ_four]
  rw [Summable.tsum_add (((hterm 0).add (hterm 1)).add (hterm 2)) (hterm 3),
    Summable.tsum_add ((hterm 0).add (hterm 1)) (hterm 2),
    Summable.tsum_add (hterm 0) (hterm 1)]
  simp only [term, eq_comm, tsum_ite_eq]
  have hmean := sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z
  simp only [Fin.sum_univ_four] at hmean
  symm
  calc
    _ = gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 0 +
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 1 +
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 2 +
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 3) := by ring
    _ = _ := by rw [hmean]

private theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel :
    Summable gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel := by
  rw [summable_prod_of_nonneg
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg]
  constructor
  · intro z
    simp_rw [gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel,
      Fin.sum_univ_four]
    apply Summable.add
    · apply Summable.add
      · apply Summable.add
        · simpa only [eq_comm] using
            (hasSum_ite_eq
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 0)
              (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 0)).summable
        · simpa only [eq_comm] using
            (hasSum_ite_eq
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 1)
              (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 1)).summable
      · simpa only [eq_comm] using
          (hasSum_ite_eq
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 2)
            (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 2)).summable
    · simpa only [eq_comm] using
        (hasSum_ite_eq
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 3)
          (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z 3)).summable
  · simpa only
      [tsum_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_right] using
      summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right 2

theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude :
    Summable gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude := by
  change Summable (fun u => ∑' z,
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u))
  have hswap :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel.prod_symm
  change Summable (fun uz : GammaSewnCriticalPhysicalPluckerIndex × (ℕ × ℕ) =>
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
      (uz.2, uz.1)) at hswap
  have hnonneg : 0 ≤
      fun uz : GammaSewnCriticalPhysicalPluckerIndex × (ℕ × ℕ) =>
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (uz.2, uz.1) := by
    intro uz
    exact gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg
      (uz.2, uz.1)
  exact (summable_prod_of_nonneg hnonneg).mp hswap |>.2

/-- The global node-free occupation is a conserved rank-two mass. -/
theorem tsum_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude_eq_two :
    ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u = 2 := by
  let F : (ℕ × ℕ) → GammaSewnCriticalPhysicalPluckerIndex → ℝ :=
    fun z u =>
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)
  have hF : Summable (Function.uncurry F) := by
    change Summable
      (fun zu : (ℕ × ℕ) × GammaSewnCriticalPhysicalPluckerIndex =>
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (zu.1, zu.2))
    exact summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
  have hsum := hF.tsum_comm
  change (∑' u, ∑' z,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)) =
    ∑' z, ∑' u,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) at hsum
  change (∑' u, ∑' z,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)) = 2
  rw [hsum]
  simp_rw
    [tsum_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_right]
  rw [tsum_mul_right, tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]
  norm_num

/-- Reciprocal-gap node attached intrinsically to one physical prime-depth cell. -/
def gammaSewnCriticalPhysicalPluckerPhysicalNode
    (u : GammaSewnCriticalPhysicalPluckerIndex) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_node u.1
    (gammaSewnCriticalAdjacentPrime_lower u.2)
    (gammaSewnCriticalAdjacentPrime_upper u.2) 0

theorem gammaSewnCriticalPhysicalPlucker_packetNode_eq_physicalNode_label
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i =
      gammaSewnCriticalPhysicalPluckerPhysicalNode
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) := by
  fin_cases i <;> rfl

/-- Reciprocal-node resistance of one packet's four-cell physical window. -/
def gammaSewnCriticalPhysicalPlucker_packetResistance (z : ℕ × ℕ) : ℝ :=
  ∑ u ∈ Finset.univ.image
      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
    1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u

theorem gammaSewnCriticalPhysicalPlucker_packetResistance_pos (z : ℕ × ℕ) :
    0 < gammaSewnCriticalPhysicalPlucker_packetResistance z := by
  rw [gammaSewnCriticalPhysicalPlucker_packetResistance]
  apply Finset.sum_pos
  · intro u hu
    exact one_div_pos.mpr <| gammaSewnCriticalPrimeDepthPacket_node_pos u.1
      (gammaSewnCriticalAdjacentPrime_lower u.2)
      (gammaSewnCriticalAdjacentPrime_upper u.2) 0
  · exact ⟨gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z 0,
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- Closed resistance formula: depth contributes one explicit quadratic factor, while the two
prime cells contribute their base reciprocal nodes. -/
theorem gammaSewnCriticalPhysicalPlucker_packetResistance_eq (z : ℕ × ℕ) :
    gammaSewnCriticalPhysicalPlucker_packetResistance z =
      (((z.1 : ℝ) + 1) ^ 2 + ((z.1 : ℝ) + 2) ^ 2) *
        (1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) (gammaSewnCriticalAdjacentPrime_lower z.2, 0) +
          1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) (gammaSewnCriticalAdjacentPrime_upper z.2, 0)) := by
  rw [gammaSewnCriticalPhysicalPlucker_packetResistance,
    Finset.sum_image (fun i _ j _ hij =>
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z hij)]
  simp_rw [← gammaSewnCriticalPhysicalPlucker_packetNode_eq_physicalNode_label]
  simp only [Fin.sum_univ_four]
  simp [gammaSewnCriticalPrimeDepthPacket_node,
    gammaSewnOrderedPrimeDepthPlucker_cell]
  have hp0 :=
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq
      (gammaSewnCriticalAdjacentPrime_lower z.2) z.1
  have hp1 :=
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq
      (gammaSewnCriticalAdjacentPrime_lower z.2) (z.1 + 1)
  have hq0 :=
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq
      (gammaSewnCriticalAdjacentPrime_upper z.2) z.1
  have hq1 :=
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq
      (gammaSewnCriticalAdjacentPrime_upper z.2) (z.1 + 1)
  rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
  rw [hp0, hp1, hq0, hq1]
  have hp :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num : (0 : ℝ) < 1 / 2)
      (gammaSewnCriticalAdjacentPrime_lower z.2, 0)).ne'
  have hq :=
    (RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
      (by norm_num : (0 : ℝ) < 1 / 2)
      (gammaSewnCriticalAdjacentPrime_upper z.2, 0)).ne'
  field_simp [hp, hq]
  push_cast
  ring

/-- Square-root incidence factors into the physical node and the conserved node-free
occupation amplitude. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sqrt_physicalNode_mul_occupation
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u =
      ((Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) : ℝ) : ℂ) *
        (gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u : ℂ) := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude,
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude]
  calc
    _ = ∑' z : ℕ × ℕ,
        ((Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) : ℝ) : ℂ) *
          ((∑ i : Fin 4,
            if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
              gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i
            else 0 : ℝ) : ℂ) := by
      apply tsum_congr
      intro z
      rw [Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · have hnode :=
          gammaSewnCriticalPhysicalPlucker_packetNode_eq_physicalNode_label z i
        rw [h] at hnode
        simp only [Complex.ofReal_mul]
        rw [hnode]
        ring
      · norm_num
    _ = ((Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) : ℝ) : ℂ) *
        ∑' z : ℕ × ℕ,
          ((∑ i : Fin 4,
            if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
              gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
                gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i
            else 0 : ℝ) : ℂ) := tsum_mul_left
    _ = _ := by rw [← Complex.ofReal_tsum]

/-- Collision penalty is a weighted concentration energy of one nonnegative occupation law whose
total mass is exactly two. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanCollisionEnergy_eq_weighted_occupation_sq :
    (∑' u : GammaSewnCriticalPhysicalPluckerIndex,
      ‖gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u‖ ^ 2) =
    ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  apply tsum_congr
  intro u
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sqrt_physicalNode_mul_occupation]
  have hnode : 0 ≤ gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
    exact (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
      (gammaSewnCriticalAdjacentPrime_lower u.2)
      (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    mul_pow, Real.sq_sqrt hnode, sq_abs]

theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq :
    Summable (fun u : GammaSewnCriticalPhysicalPluckerIndex =>
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2) := by
  have hb := (lp.memℓp gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter).summable
    (by norm_num : 0 < (2 : ENNReal).toReal)
  have hincidence : Summable (fun u : GammaSewnCriticalPhysicalPluckerIndex =>
      ‖gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u‖ ^ 2) := by
    simpa using hb.congr (fun u => by
      have hcoord : gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter u =
          gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude u := by
        rw [← inner_basis_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter]
        simp [gammaSewnCriticalPhysicalPluckerBasis, lp.inner_single_left]
      rw [hcoord]
      norm_num)
  exact hincidence.congr fun u => by
    rw [gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_eq_sqrt_physicalNode_mul_occupation]
    have hnode : 0 ≤ gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
      exact (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
        (gammaSewnCriticalAdjacentPrime_lower u.2)
        (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      mul_pow, Real.sq_sqrt hnode, sq_abs]

/-- Local resistance-capacity inequality. Unlike the global certificate below, its energy term is
restricted to the same finite physical window, so bounded-overlap packet windows can be summed. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_local_cauchy
    (F : Finset GammaSewnCriticalPhysicalPluckerIndex) :
    (∑ u ∈ F,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u) ^ 2 ≤
      (∑ u ∈ F, 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        ∑ u ∈ F,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let a : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
  let b : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u)
  have hnode (u : GammaSewnCriticalPhysicalPluckerIndex) :
      0 < gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
    exact gammaSewnCriticalPrimeDepthPacket_node_pos u.1
      (gammaSewnCriticalAdjacentPrime_lower u.2)
      (gammaSewnCriticalAdjacentPrime_upper u.2) 0
  have hab (u : GammaSewnCriticalPhysicalPluckerIndex) :
      a u * b u =
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u := by
    have hsqrt : Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) = 1 := by
      rw [← Real.sqrt_mul (hnode u).le]
      field_simp [(hnode u).ne']
      norm_num
    dsimp [a, b]
    calc
      _ = (Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
          Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u)) *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u := by ring
      _ = _ := by rw [hsqrt, one_mul]
  have ha (u : GammaSewnCriticalPhysicalPluckerIndex) :
      a u ^ 2 = gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hnode u).le]
  have hb (u : GammaSewnCriticalPhysicalPluckerIndex) :
      b u ^ 2 = 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
    dsimp [b]
    rw [Real.sq_sqrt (div_nonneg (by norm_num) (hnode u).le)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F a b
  rw [Finset.sum_congr rfl (fun u _ => hab u),
    Finset.sum_congr rfl (fun u _ => ha u),
    Finset.sum_congr rfl (fun u _ => hb u)] at hcs
  nlinarith

/-- Finite resistance-capacity lower bound.  Any occupation mass captured by a finite physical
window forces a quantitative portion of the full collision penalty. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_cauchy
    (F : Finset GammaSewnCriticalPhysicalPluckerIndex) :
    (∑ u ∈ F,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u) ^ 2 ≤
      (∑ u ∈ F, 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let a : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
  let b : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u)
  have hnode (u : GammaSewnCriticalPhysicalPluckerIndex) :
      0 < gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
    exact gammaSewnCriticalPrimeDepthPacket_node_pos u.1
      (gammaSewnCriticalAdjacentPrime_lower u.2)
      (gammaSewnCriticalAdjacentPrime_upper u.2) 0
  have hab (u : GammaSewnCriticalPhysicalPluckerIndex) :
      a u * b u =
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u := by
    have hsqrt : Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) = 1 := by
      rw [← Real.sqrt_mul (hnode u).le]
      field_simp [(hnode u).ne']
      norm_num
    dsimp [a, b]
    calc
      _ = (Real.sqrt (gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
          Real.sqrt (1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u)) *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u := by ring
      _ = _ := by rw [hsqrt, one_mul]
  have ha (u : GammaSewnCriticalPhysicalPluckerIndex) :
      a u ^ 2 = gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hnode u).le]
  have hb (u : GammaSewnCriticalPhysicalPluckerIndex) :
      b u ^ 2 = 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u := by
    dsimp [b]
    rw [Real.sq_sqrt (div_nonneg (by norm_num) (hnode u).le)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F a b
  rw [Finset.sum_congr rfl (fun u _ => hab u),
    Finset.sum_congr rfl (fun u _ => ha u),
    Finset.sum_congr rfl (fun u _ => hb u)] at hcs
  have hfinite : (∑ u ∈ F,
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2) ≤
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq.sum_le_tsum F
      (fun u _ => mul_nonneg (hnode u).le (sq_nonneg _))
  have hresistance : 0 ≤
      ∑ u ∈ F, 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u :=
    Finset.sum_nonneg fun u _ => div_nonneg (by norm_num) (hnode u).le
  exact hcs.trans <| calc
    (∑ u ∈ F,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2) *
        (∑ u ∈ F, 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) =
      (∑ u ∈ F, 1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        (∑ u ∈ F,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2) := by
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinite hresistance

private theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_left
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)) := by
  have hswap :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel.prod_symm
  change Summable (fun uz : GammaSewnCriticalPhysicalPluckerIndex × (ℕ × ℕ) =>
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
      (uz.2, uz.1)) at hswap
  have hnonneg : 0 ≤
      fun uz : GammaSewnCriticalPhysicalPluckerIndex × (ℕ × ℕ) =>
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (uz.2, uz.1) := by
    intro uz
    exact gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg
      (uz.2, uz.1)
  exact (summable_prod_of_nonneg hnonneg).mp hswap |>.1 u

private theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_sq_left
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) := by
  let total := gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
  have hk :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_left u
  have hterm_le (z : ℕ × ℕ) :
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2 ≤
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) * total := by
    have hle :
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ≤
          total := by
      change gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ≤
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
      exact hk.le_tsum z (fun w _ =>
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg (w, u))
    simpa [pow_two] using mul_le_mul_of_nonneg_left hle
      (gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg (z, u))
  exact Summable.of_nonneg_of_le (fun z => sq_nonneg _)
    hterm_le (hk.mul_right total)

private theorem gammaSewnCriticalPhysicalPluckerGlobalMean_pointwiseSelfKernel_le
    (u : GammaSewnCriticalPhysicalPluckerIndex) :
    ∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2 ≤
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let total := gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
  have hk :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_left u
  have hterm_le (z : ℕ × ℕ) :
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2 ≤
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) * total := by
    have hle :
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ≤
          total := by
      change gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ≤
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u
      exact hk.le_tsum z (fun w _ =>
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg (w, u))
    simpa [pow_two] using mul_le_mul_of_nonneg_left hle
      (gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg (z, u))
  have hright : Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) * total) :=
    hk.mul_right total
  have hsquare :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_sq_left u
  have hsquare_le :
      (∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) ≤
          total ^ 2 := calc
    _ ≤ ∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) * total :=
      hsquare.tsum_le_tsum hterm_le hright
    _ = (∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)) * total :=
      tsum_mul_right
    _ = total ^ 2 := by
      rw [show (∑' z : ℕ × ℕ,
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u)) =
          total by rfl]
      ring
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hsquare_le <|
    (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
      (gammaSewnCriticalAdjacentPrime_lower u.2)
      (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le

private theorem summable_gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_double :
    Summable (fun uz : GammaSewnCriticalPhysicalPluckerIndex × (ℕ × ℕ) =>
      gammaSewnCriticalPhysicalPluckerPhysicalNode uz.1 *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (uz.2, uz.1) ^ 2) := by
  let self : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    ∑' z : ℕ × ℕ,
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2
  let energy : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    gammaSewnCriticalPhysicalPluckerPhysicalNode u *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2
  have hinner (u : GammaSewnCriticalPhysicalPluckerIndex) : Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) :=
    (summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_sq_left u).mul_left
      (gammaSewnCriticalPhysicalPluckerPhysicalNode u)
  have hself_nonneg (u : GammaSewnCriticalPhysicalPluckerIndex) : 0 ≤ self u := by
    exact tsum_nonneg fun z => mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
        (gammaSewnCriticalAdjacentPrime_lower u.2)
        (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le (sq_nonneg _)
  have hself_le (u : GammaSewnCriticalPhysicalPluckerIndex) : self u ≤ energy u :=
    gammaSewnCriticalPhysicalPluckerGlobalMean_pointwiseSelfKernel_le u
  have hself_summable : Summable self := Summable.of_nonneg_of_le hself_nonneg hself_le
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq
  rw [summable_prod_of_nonneg]
  · exact ⟨hinner, hself_summable⟩
  · intro uz
    exact mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos uz.1.1
        (gammaSewnCriticalAdjacentPrime_lower uz.1.2)
        (gammaSewnCriticalAdjacentPrime_upper uz.1.2) 0).le (sq_nonneg _)

private theorem gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_row_le_collision :
    ∑' u : GammaSewnCriticalPhysicalPluckerIndex, ∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2 ≤
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let self : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    ∑' z : ℕ × ℕ,
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2
  let energy : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    gammaSewnCriticalPhysicalPluckerPhysicalNode u *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2
  have hself_nonneg (u : GammaSewnCriticalPhysicalPluckerIndex) : 0 ≤ self u := by
    exact tsum_nonneg fun z => mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
        (gammaSewnCriticalAdjacentPrime_lower u.2)
        (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le (sq_nonneg _)
  have hself_le (u : GammaSewnCriticalPhysicalPluckerIndex) : self u ≤ energy u :=
    gammaSewnCriticalPhysicalPluckerGlobalMean_pointwiseSelfKernel_le u
  have hself_summable : Summable self := Summable.of_nonneg_of_le hself_nonneg hself_le
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq
  exact hself_summable.tsum_le_tsum hself_le
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq

private theorem gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_tsum_comm :
    (∑' z : ℕ × ℕ, ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) =
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex, ∑' z : ℕ × ℕ,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2 := by
  exact summable_gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_double.tsum_comm

private theorem gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_at_label
    (z : ℕ × ℕ) (i : Fin 4) :
    gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
        (z, gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i := by
  unfold gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j ≠
        gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i :=
      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z).ne hji
    simp [hne]
  · simp

/-- Exact self-collision of one packet before positive cross-packet interference. -/
theorem gammaSewnCriticalPhysicalPlucker_packetSelfKernel_eq (z : ℕ × ℕ) :
    (∑' u : GammaSewnCriticalPhysicalPluckerIndex,
      gammaSewnCriticalPhysicalPluckerPhysicalNode u *
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
        ∑ i : Fin 4,
          gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  rw [tsum_eq_sum]
  · rw [Finset.sum_image fun i _ j _ hij =>
      gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z hij]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_at_label,
      ← gammaSewnCriticalPhysicalPlucker_packetNode_eq_physicalNode_label]
    ring
  · intro u hu
    have hkernel :
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) = 0 := by
      unfold gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
      apply Finset.sum_eq_zero
      intro i _
      have hne : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i ≠ u := by
        intro h
        exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
      simp [hne]
    simp [hkernel]

/-- Rank-two coordinate mass and reciprocal-node Cauchy give the exact resistance relaxation of
one packet's self-collision. -/
theorem gammaSewnCriticalPhysicalPlucker_packetCoordinateResistanceCauchy
    (z : ℕ × ℕ) :
    4 ≤ gammaSewnCriticalPhysicalPlucker_packetResistance z *
      ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  let node : Fin 4 → ℝ := fun i =>
    gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i
  let mean : Fin 4 → ℝ := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z
  let a : Fin 4 → ℝ := fun i => Real.sqrt (node i) * mean i
  let b : Fin 4 → ℝ := fun i => Real.sqrt (1 / node i)
  have hnode (i : Fin 4) : 0 < node i :=
    gammaSewnCriticalPrimeDepthPacket_node_pos z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i
  have hab (i : Fin 4) : a i * b i = mean i := by
    have hsqrt : Real.sqrt (node i) * Real.sqrt (1 / node i) = 1 := by
      rw [← Real.sqrt_mul (hnode i).le]
      field_simp [(hnode i).ne']
      norm_num
    dsimp [a, b]
    calc
      _ = (Real.sqrt (node i) * Real.sqrt (1 / node i)) * mean i := by ring
      _ = _ := by rw [hsqrt, one_mul]
  have ha (i : Fin 4) : a i ^ 2 = node i * mean i ^ 2 := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hnode i).le]
  have hb (i : Fin 4) : b i ^ 2 = 1 / node i := by
    dsimp [b]
    rw [Real.sq_sqrt (div_nonneg (by norm_num) (hnode i).le)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [Finset.sum_congr rfl (fun i _ => hab i),
    Finset.sum_congr rfl (fun i _ => ha i),
    Finset.sum_congr rfl (fun i _ => hb i)] at hcs
  have hmean : ∑ i, mean i = 2 :=
    sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z
  have hres : (∑ i, 1 / node i) =
      gammaSewnCriticalPhysicalPlucker_packetResistance z := by
    rw [gammaSewnCriticalPhysicalPlucker_packetResistance,
      Finset.sum_image fun i _ j _ hij =>
        gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z hij]
    apply Finset.sum_congr rfl
    intro i _
    rw [← gammaSewnCriticalPhysicalPlucker_packetNode_eq_physicalNode_label]
  change 4 ≤ gammaSewnCriticalPhysicalPlucker_packetResistance z *
    ∑ i, node i * mean i ^ 2
  rw [← hres]
  nlinarith

theorem gammaSewnCriticalPhysicalPlucker_packetSelfCollisionCapacity
    (z : ℕ × ℕ) :
    4 * (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
      gammaSewnCriticalPhysicalPlucker_packetResistance z) ≤
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
        ∑ i : Fin 4,
          gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  have hdiv : 4 / gammaSewnCriticalPhysicalPlucker_packetResistance z ≤
      ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 :=
    (div_le_iff₀ (gammaSewnCriticalPhysicalPlucker_packetResistance_pos z)).2 <| by
      simpa [mul_comm] using
        gammaSewnCriticalPhysicalPlucker_packetCoordinateResistanceCauchy z
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (sq_nonneg (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z))
  calc
    4 * (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
        gammaSewnCriticalPhysicalPlucker_packetResistance z) =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
        (4 / gammaSewnCriticalPhysicalPlucker_packetResistance z) := by ring
    _ ≤ _ := hmul

theorem summable_gammaSewnCriticalPhysicalPlucker_packetSelfCollision :
    Summable (fun z : ℕ × ℕ =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
        ∑ i : Fin 4,
          gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2) := by
  have hsymm :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_double.prod_symm
  have hnonneg : 0 ≤
      fun zu : (ℕ × ℕ) × GammaSewnCriticalPhysicalPluckerIndex =>
        gammaSewnCriticalPhysicalPluckerPhysicalNode zu.2 *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
            (zu.1, zu.2) ^ 2 := by
    intro zu
    exact mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos zu.2.1
        (gammaSewnCriticalAdjacentPrime_lower zu.2.2)
        (gammaSewnCriticalAdjacentPrime_upper zu.2.2) 0).le (sq_nonneg _)
  have houter := (summable_prod_of_nonneg hnonneg).mp hsymm |>.2
  exact houter.congr fun z =>
    gammaSewnCriticalPhysicalPlucker_packetSelfKernel_eq z

/-- Positive overlap creates only constructive interference: full collision dominates the
simultaneous sum of all exact packet self-collisions, with no multiplicity loss. -/
theorem gammaSewnCriticalPhysicalPlucker_globalPacketSelfCollision_le :
    ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
          ∑ i : Fin 4,
            gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 ≤
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  have h :
      (∑' z : ℕ × ℕ, ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel (z, u) ^ 2) ≤
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
    rw [gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_tsum_comm]
    exact gammaSewnCriticalPhysicalPluckerGlobalMean_selfKernel_row_le_collision
  simpa only [gammaSewnCriticalPhysicalPlucker_packetSelfKernel_eq] using h

/-- The exact packet self-collision sum dominates its reciprocal-resistance relaxation by factor
four, so the constructive-interference trace bound is genuinely stronger. -/
theorem gammaSewnCriticalPhysicalPlucker_globalAdditiveCapacity_le_packetSelfCollision :
    ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
          gammaSewnCriticalPhysicalPlucker_packetResistance z ≤
      ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
          ∑ i : Fin 4,
            gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  let capacity : (ℕ × ℕ) → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
      gammaSewnCriticalPhysicalPlucker_packetResistance z
  let self : (ℕ × ℕ) → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
      ∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2
  have hcapacity_nonneg (z : ℕ × ℕ) : 0 ≤ capacity z :=
    div_nonneg (sq_nonneg _)
      (gammaSewnCriticalPhysicalPlucker_packetResistance_pos z).le
  have hcapacity_le (z : ℕ × ℕ) : capacity z ≤ self z := by
    have hscaled := gammaSewnCriticalPhysicalPlucker_packetSelfCollisionCapacity z
    change 4 * capacity z ≤ self z at hscaled
    have hself_nonneg : 0 ≤ self z := by
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg
          (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
          (sq_nonneg _))
    linarith
  have hself_summable : Summable self :=
    summable_gammaSewnCriticalPhysicalPlucker_packetSelfCollision
  have hcapacity_summable : Summable capacity :=
    Summable.of_nonneg_of_le hcapacity_nonneg hcapacity_le hself_summable
  exact hcapacity_summable.tsum_le_tsum hcapacity_le hself_summable

/-- One packet deposits its full rank-two occupation mass into its four physical labels; all
other packets add nonnegative mass there. -/
theorem gammaSewnCriticalPhysicalPlucker_packetOccupationMass_le
    (z : ℕ × ℕ) :
    2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ≤
      ∑ u ∈ Finset.univ.image
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u := by
  have hpoint (i : Fin 4) :
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ≤
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) := by
    have hterm :
        gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (z, gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) =
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i := by
      unfold gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        have hne : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z j ≠
            gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i :=
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z).ne hj
        simp [hne]
      · simp
    calc
      _ = gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
          (z, gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) := hterm.symm
      _ ≤ ∑' w,
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel
            (w, gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) :=
        (summable_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_left
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)).le_tsum z
            (fun w _ =>
              gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceKernel_nonneg
                (w, gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))
      _ = _ := rfl
  rw [Finset.sum_image (fun i _ j _ hij =>
    gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_injective z hij)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpoint i
  calc
    2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z =
        ∑ i : Fin 4, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i := by
      rw [← Finset.mul_sum, sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean]
      ring
    _ ≤ _ := hsum

/-- Local packet capacity with energy restricted to its own four-cell window. The rank-two mass
square supplies factor four, ready to cancel the reverse-incidence overlap multiplicity. -/
theorem gammaSewnCriticalPhysicalPlucker_packetLocalScaledCollisionCapacity
    (z : ℕ × ℕ) :
    4 * (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
      gammaSewnCriticalPhysicalPlucker_packetResistance z) ≤
      ∑ u ∈ Finset.univ.image
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let F := Finset.univ.image
    (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z)
  have hmass := gammaSewnCriticalPhysicalPlucker_packetOccupationMass_le z
  have hnonneg : 0 ≤ 2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z :=
    mul_nonneg (by norm_num)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hsum_nonneg : 0 ≤ ∑ u ∈ F,
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u :=
    hnonneg.trans hmass
  have hsq := (sq_le_sq₀ hnonneg hsum_nonneg).2 hmass
  have hlocal :=
    gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_local_cauchy F
  have hcap : (2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ^ 2 ≤
      gammaSewnCriticalPhysicalPlucker_packetResistance z *
        ∑ u ∈ F,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
    exact hsq.trans <| by
      simpa [F, gammaSewnCriticalPhysicalPlucker_packetResistance] using hlocal
  have hdiv :
      (2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ^ 2 /
          gammaSewnCriticalPhysicalPlucker_packetResistance z ≤
        ∑ u ∈ F,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 :=
    (div_le_iff₀ (gammaSewnCriticalPhysicalPlucker_packetResistance_pos z)).2 <| by
      simpa [mul_comm] using hcap
  calc
    4 * (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
        gammaSewnCriticalPhysicalPlucker_packetResistance z) =
      (2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ^ 2 /
        gammaSewnCriticalPhysicalPlucker_packetResistance z := by ring
    _ ≤ _ := by simpa [F] using hdiv

/-- Summed local collision energies lose at most the exact reverse-incidence multiplicity four. -/
theorem gammaSewnCriticalPhysicalPlucker_finitePacketWindowEnergy_le_four_collision
    (S : Finset (ℕ × ℕ)) :
    ∑ z ∈ S,
        ∑ u ∈ Finset.univ.image
            (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 ≤
      4 * ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let window : (ℕ × ℕ) → Finset GammaSewnCriticalPhysicalPluckerIndex := fun z =>
    Finset.univ.image (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z)
  let energy : GammaSewnCriticalPhysicalPluckerIndex → ℝ := fun u =>
    gammaSewnCriticalPhysicalPluckerPhysicalNode u *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2
  let U : Finset GammaSewnCriticalPhysicalPluckerIndex := S.biUnion window
  have henergy_nonneg (u : GammaSewnCriticalPhysicalPluckerIndex) : 0 ≤ energy u := by
    exact mul_nonneg
      (gammaSewnCriticalPrimeDepthPacket_node_pos u.1
        (gammaSewnCriticalAdjacentPrime_lower u.2)
        (gammaSewnCriticalAdjacentPrime_upper u.2) 0).le
      (sq_nonneg _)
  have hwindow_subset (z : ℕ × ℕ) (hz : z ∈ S) : window z ⊆ U := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨z, hz, hu⟩
  have hcard (u : GammaSewnCriticalPhysicalPluckerIndex) :
      (S.filter fun z => u ∈ window z).card ≤ 4 := by
    have hsubset : (S.filter fun z => u ∈ window z) ⊆
        gammaSewnCriticalPhysicalPluckerIncidentPackets u := by
      intro z hz
      have hzwindow := (Finset.mem_filter.mp hz).2
      rcases Finset.mem_image.mp hzwindow with ⟨i, -, hi⟩
      exact gammaSewnCriticalPhysicalPlucker_packet_mem_incident_of_label_eq hi
    exact (Finset.card_le_card hsubset).trans
      (gammaSewnCriticalPhysicalPluckerIncidentPackets_card_le_four u)
  have hfixed (u : GammaSewnCriticalPhysicalPluckerIndex) :
      (∑ z ∈ S, if u ∈ window z then energy u else 0) ≤ 4 * energy u := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u) (henergy_nonneg u)
  calc
    ∑ z ∈ S, ∑ u ∈ Finset.univ.image
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 =
        ∑ z ∈ S, ∑ u ∈ U, if u ∈ window z then energy u else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          change (∑ u ∈ window z, energy u) = _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          ext u
          simp [hwindow_subset z hz]
          intro u hu
          rfl
    _ = ∑ u ∈ U, ∑ z ∈ S, if u ∈ window z then energy u else 0 :=
      Finset.sum_comm
    _ ≤ ∑ u ∈ U, 4 * energy u := Finset.sum_le_sum fun u _ => hfixed u
    _ = 4 * ∑ u ∈ U, energy u := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑' u, energy u := by
      exact mul_le_mul_of_nonneg_left
        (summable_gammaSewnCriticalPhysicalPluckerGlobalMeanWeightedOccupationSq.sum_le_tsum U
          (fun u _ => henergy_nonneg u)) (by norm_num)
    _ = _ := rfl

/-- Every single packet supplies a four-cell capacity certificate for the full collision penalty. -/
theorem gammaSewnCriticalPhysicalPlucker_packetCollisionCapacity
    (z : ℕ × ℕ) :
    (2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ^ 2 ≤
      (∑ u ∈ Finset.univ.image
          (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
          1 / gammaSewnCriticalPhysicalPluckerPhysicalNode u) *
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  have hmass := gammaSewnCriticalPhysicalPlucker_packetOccupationMass_le z
  have hnonneg : 0 ≤ 2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z :=
    mul_nonneg (by norm_num)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hsum_nonneg : 0 ≤ ∑ u ∈ Finset.univ.image
      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u :=
    hnonneg.trans hmass
  have hsq := (sq_le_sq₀ hnonneg hsum_nonneg).2 hmass
  exact hsq.trans
    (gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_cauchy
      (Finset.univ.image
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z)))

/-- Closed prime/depth form of the packet collision-capacity certificate. -/
theorem gammaSewnCriticalPhysicalPlucker_packetCollisionCapacity_closed
    (z : ℕ × ℕ) :
    (2 * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) ^ 2 ≤
      ((((z.1 : ℝ) + 1) ^ 2 + ((z.1 : ℝ) + 2) ^ 2) *
        (1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) (gammaSewnCriticalAdjacentPrime_lower z.2, 0) +
          1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
            (1 / 2) (gammaSewnCriticalAdjacentPrime_upper z.2, 0))) *
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  rw [← gammaSewnCriticalPhysicalPlucker_packetResistance_eq]
  simpa [gammaSewnCriticalPhysicalPlucker_packetResistance] using
    gammaSewnCriticalPhysicalPlucker_packetCollisionCapacity z

/-- Global additive collision capacity. Every packet contributes simultaneously: rank-two mass
cancels the four-fold window overlap, leaving the sum of squared normalized block weights divided
by exact packet resistance below the full collision penalty. -/
theorem gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity :
    ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
          gammaSewnCriticalPhysicalPlucker_packetResistance z ≤
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  let capacity : (ℕ × ℕ) → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
      gammaSewnCriticalPhysicalPlucker_packetResistance z
  let collision : ℝ := ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
    gammaSewnCriticalPhysicalPluckerPhysicalNode u *
      gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2
  have hcapacity_nonneg : 0 ≤ capacity := by
    intro z
    exact div_nonneg (sq_nonneg _)
      (gammaSewnCriticalPhysicalPlucker_packetResistance_pos z).le
  have hfinite (S : Finset (ℕ × ℕ)) : ∑ z ∈ S, capacity z ≤ collision := by
    have hscaled : 4 * ∑ z ∈ S, capacity z ≤ 4 * collision := calc
      4 * ∑ z ∈ S, capacity z = ∑ z ∈ S, 4 * capacity z := by
        rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ S,
          ∑ u ∈ Finset.univ.image
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z),
            gammaSewnCriticalPhysicalPluckerPhysicalNode u *
              gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
        exact Finset.sum_le_sum fun z _ =>
          gammaSewnCriticalPhysicalPlucker_packetLocalScaledCollisionCapacity z
      _ ≤ 4 * collision :=
        gammaSewnCriticalPhysicalPlucker_finitePacketWindowEnergy_le_four_collision S
    linarith
  have hsummable : Summable capacity := summable_of_sum_le hcapacity_nonneg hfinite
  exact hsummable.tsum_le_of_sum_le hfinite

/-- Closed arithmetic form of the global additive capacity lower bound. -/
theorem gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity_closed :
    ∑' z : ℕ × ℕ,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
          ((((z.1 : ℝ) + 1) ^ 2 + ((z.1 : ℝ) + 2) ^ 2) *
            (1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
                (1 / 2) (gammaSewnCriticalAdjacentPrime_lower z.2, 0) +
              1 / RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
                (1 / 2) (gammaSewnCriticalAdjacentPrime_upper z.2, 0))) ≤
      ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
        gammaSewnCriticalPhysicalPluckerPhysicalNode u *
          gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  simpa only [gammaSewnCriticalPhysicalPlucker_packetResistance_eq] using
    gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity

/-- Fully scalar conserved-occupation source law. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_weighted_occupation_sq :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass =
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
        ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
          gammaSewnCriticalPhysicalPluckerPhysicalNode u *
            gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_incidenceAmplitude,
    gammaSewnCriticalPhysicalPluckerGlobalMeanCollisionEnergy_eq_weighted_occupation_sq]

/-- Constructive-interference upper bound: subtract every exact packet self-collision from the raw
first moment. Cross-packet overlap can only lower the completed trace further. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_le_rawFirstMoment_sub_packetSelfCollision :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass ≤
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
        ∑' z : ℕ × ℕ,
          gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 *
            ∑ i : Fin 4,
              gammaSewnCriticalPrimeDepthPacket_node z.1
                  (gammaSewnCriticalAdjacentPrime_lower z.2)
                  (gammaSewnCriticalAdjacentPrime_upper z.2) i *
                gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ^ 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_weighted_occupation_sq]
  linarith [gammaSewnCriticalPhysicalPlucker_globalPacketSelfCollision_le]

/-- Resistance-relaxed arithmetic upper bound for the completed first trace. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_le_rawFirstMoment_sub_additiveCapacity :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass ≤
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
        ∑' z : ℕ × ℕ,
          gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z ^ 2 /
            gammaSewnCriticalPhysicalPlucker_packetResistance z := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_weighted_occupation_sq]
  linarith [gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity]

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

/-- The exact rank-two occupation law propagates the sharpened packet ceiling through the
normalized cofinal block weights. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment_lt_eight_div_oneTwentyFive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment < (8 / 125 : ℝ) := by
  let f : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
      (∑ i : Fin 4,
        gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i)
  let g : ℕ × ℕ → ℝ := fun z =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z * (8 / 125 : ℝ)
  have hf : Summable f :=
    summable_gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment
  have hg : Summable g :=
    summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.mul_right (8 / 125 : ℝ)
  have hle : f ≤ g := fun z => mul_le_mul_of_nonneg_left
    (gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_eight_div_oneTwentyFive z).le
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
  have hstrict : f (0, 0) < g (0, 0) :=
    mul_lt_mul_of_pos_left
      (gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_eight_div_oneTwentyFive
        (0, 0))
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos (0, 0))
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment]
  change ∑' z, f z < _
  calc
    ∑' z, f z < ∑' z, g z :=
      Summable.tsum_lt_tsum hle hstrict hf hg
    _ = (∑' z, gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
        (8 / 125 : ℝ) := by rw [tsum_mul_right]
    _ = _ := by
      rw [tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight]
      norm_num

/-- Global-mean completion obeys the strict rank-two Ky--Fan ceiling `8/125`. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_lt_eight_div_oneTwentyFive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass <
      (8 / 125 : ℝ) := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter]
  exact (sub_le_self _ (sq_nonneg _)).trans_lt
    gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment_lt_eight_div_oneTwentyFive

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

/-- Final first-coefficient landing criterion as concentration energy of a nonnegative conserved
mass-two occupation law on the physical prime-depth node grid. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_weighted_occupation_sq :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace =
        ((thetaCuspNormalizedEvenMoment 1 / 2 : ℝ) : ℂ) ↔
      gammaSewnCriticalPhysicalPluckerGlobalMeanRawFirstMoment -
          ∑' u : GammaSewnCriticalPhysicalPluckerIndex,
            gammaSewnCriticalPhysicalPluckerPhysicalNode u *
              gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude u ^ 2 =
        thetaCuspNormalizedEvenMoment 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_weighted_occupation_sq]
  norm_cast

end RHTower.HedenmalmThetaSource
