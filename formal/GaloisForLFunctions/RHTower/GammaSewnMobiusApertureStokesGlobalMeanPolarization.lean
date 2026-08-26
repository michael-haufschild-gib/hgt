import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerSpectralOperator

/-!
# Global mean polarization of the physical Pluecker source

Packetwise centering leaves one reciprocal-node common mode in every four-cell Pluecker block.
A positive block completion cannot couple directly through such a null direction.  The source-safe
order is instead to restore each packet's uncentered mean mass and only then remove the global
polar mean.

This file constructs the resulting between-packet term without choosing a global mean vector:

`(1 / 2) * sum_{z,w} weight z * weight w * |mean z - mean w><mean z - mean w|`.

The double series is absolutely nuclear.  Hence the correction is positive, Schatten-one, and
compact, while retaining every cross-packet coefficient interference.  Adding it to the literal
physical-overlap Pluecker operator gives an unconditional positive trace-class nonlocal source
polarization.  No Xi zero, target moment, fitted coefficient, or extra axiom enters.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower.HedenmalmThetaSource

/-- Node-weighted mean of one physical four-cell Pluecker packet. -/
def gammaSewnCriticalPhysicalPluckerMeanVector
    (z : ℕ × ℕ) : GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑ i : Fin 4,
    ((Real.sqrt
        (gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ) •
      gammaSewnCriticalPhysicalPluckerBasis
        (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)

theorem norm_gammaSewnCriticalPhysicalPluckerMeanVector_le
    (z : ℕ × ℕ) :
    ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ≤
      4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
  calc
    ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ ≤
        ∑ i : Fin 4,
          ‖(((Real.sqrt
              (gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
              gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i : ℝ) : ℂ) •
            gammaSewnCriticalPhysicalPluckerBasis
              (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))‖ := by
      exact norm_sum_le _ _
    _ = ∑ i : Fin 4,
        Real.sqrt
            (gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
          gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        norm_gammaSewnCriticalPhysicalPluckerBasis, mul_one,
        abs_of_nonneg]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).1
    _ ≤ ∑ _i : Fin 4, Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
      apply Finset.sum_le_sum
      intro i _
      have hnode :
          gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i ≤
            gammaSewnCriticalPlucker_nodeBound := by
        exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
          (by norm_num) (by norm_num) _
      have hsqrt := Real.sqrt_le_sqrt hnode
      have hmean :=
        (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).2
      exact calc
        Real.sqrt
              (gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i) *
            gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i ≤
          Real.sqrt
              (gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i) * 1 := by
            exact mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg _)
        _ = Real.sqrt
              (gammaSewnCriticalPrimeDepthPacket_node z.1
                (gammaSewnCriticalAdjacentPrime_lower z.2)
                (gammaSewnCriticalAdjacentPrime_upper z.2) i) := mul_one _
        _ ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound := hsqrt
    _ = 4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by simp

/-- Difference of two packet means.  This is the nonlocal polar channel. -/
def gammaSewnCriticalPhysicalPluckerMeanDifference
    (z w : ℕ × ℕ) : GammaSewnCriticalPhysicalPluckerHilbert :=
  gammaSewnCriticalPhysicalPluckerMeanVector z -
    gammaSewnCriticalPhysicalPluckerMeanVector w

theorem norm_gammaSewnCriticalPhysicalPluckerMeanDifference_le
    (z w : ℕ × ℕ) :
    ‖gammaSewnCriticalPhysicalPluckerMeanDifference z w‖ ≤
      8 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by
  calc
    ‖gammaSewnCriticalPhysicalPluckerMeanDifference z w‖ ≤
        ‖gammaSewnCriticalPhysicalPluckerMeanVector z‖ +
          ‖gammaSewnCriticalPhysicalPluckerMeanVector w‖ := by
      exact norm_sub_le _ _
    _ ≤ 4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound +
          4 * Real.sqrt gammaSewnCriticalPlucker_nodeBound :=
      add_le_add
        (norm_gammaSewnCriticalPhysicalPluckerMeanVector_le z)
        (norm_gammaSewnCriticalPhysicalPluckerMeanVector_le w)
    _ = 8 * Real.sqrt gammaSewnCriticalPlucker_nodeBound := by ring

/-- One ordered pairwise mean-dispersion term.  The factor `1/2` makes the ordered double
sum equal the usual between-packet covariance. -/
def gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  (((1 / 2 : ℝ) *
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 : ℝ) : ℂ) •
    InnerProductSpace.rankOne ℂ
      (gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2)
      (gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2)

theorem gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_hasRankLE
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    HasRankLE
      (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw) 1 := by
  apply hasRankLE_smul
  simpa [gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm] using
    hasRankLE_sum_range_rankOne
      (fun _ : ℕ => gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2)
      (fun _ : ℕ => gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2) 1

theorem gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_isPositive
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw).IsPositive := by
  apply (InnerProductSpace.isPositive_rankOne_self
    (𝕜 := ℂ) (gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2)).smul_of_nonneg
  exact (RCLike.ofReal_nonneg (K := ℂ)).2 <| mul_nonneg
    (mul_nonneg (by norm_num)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.1).le)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.2).le

theorem norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    ‖gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw‖ =
      (1 / 2 : ℝ) *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2 := by
  rw [gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.1),
    abs_of_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.2)]
  ring

theorem norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_le
    (zw : (ℕ × ℕ) × (ℕ × ℕ)) :
    ‖gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw‖ ≤
      (1 / 2 : ℝ) *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        (64 * gammaSewnCriticalPlucker_nodeBound) := by
  have hnorm := norm_gammaSewnCriticalPhysicalPluckerMeanDifference_le zw.1 zw.2
  have hnorm0 := norm_nonneg
    (gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2)
  have hsqrt0 : 0 ≤ Real.sqrt gammaSewnCriticalPlucker_nodeBound :=
    Real.sqrt_nonneg _
  have hsq :
      ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2‖ ^ 2 ≤
        64 * gammaSewnCriticalPlucker_nodeBound := by
    have hmul := mul_le_mul hnorm hnorm hnorm0
      (mul_nonneg (by norm_num) hsqrt0)
    rw [← pow_two, ← pow_two] at hmul
    nlinarith [Real.sq_sqrt gammaSewnCriticalPlucker_nodeBound_pos.le]
  rw [norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm]
  exact mul_le_mul_of_nonneg_left hsq <| mul_nonneg
    (mul_nonneg (by norm_num)
      (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.1).le)
    (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.2).le

theorem summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm :
    Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      ‖gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw‖) := by
  let C : ℝ := (1 / 2 : ℝ) * (64 * gammaSewnCriticalPlucker_nodeBound)
  have hmajor : Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 * C) := by
    have hprod : Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
          gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2) :=
      summable_mul_of_summable_norm
        summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.norm
        summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.norm
    exact hprod.mul_right C
  exact Summable.of_nonneg_of_le
    (fun zw => norm_nonneg _)
    (fun zw => by
      simpa [C, mul_assoc, mul_comm, mul_left_comm] using
        norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_le zw)
    hmajor

/-- Infinite nonlocal between-packet covariance. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑' zw : (ℕ × ℕ) × (ℕ × ℕ),
    gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator_memSchattenClass_one :
    MemSchattenClass 1
      gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator := by
  exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
    gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_hasRankLE
    summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator_isPositive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator.IsPositive := by
  apply isPositive_tsum_of_summable
  · exact Summable.of_norm
      summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
  · exact gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_isPositive

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator_isCompact :
    IsCompactOperator gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator :=
  gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator_memSchattenClass_one.isCompactOperator
    (by norm_num)

/-- One nuclear term of the combined packet-covariance/global-mean source. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm :
    ((ℕ × ℕ) × Fin 6) ⊕ ((ℕ × ℕ) × (ℕ × ℕ)) →
      GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
        GammaSewnCriticalPhysicalPluckerHilbert
  | Sum.inl idx => gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx
  | Sum.inr zw => gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm_hasRankLE
    (idx : ((ℕ × ℕ) × Fin 6) ⊕ ((ℕ × ℕ) × (ℕ × ℕ))) :
    HasRankLE
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm idx) 1 := by
  cases idx with
  | inl idx =>
      exact gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_hasRankLE idx
  | inr zw =>
      exact gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_hasRankLE zw

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm_isPositive
    (idx : ((ℕ × ℕ) × Fin 6) ⊕ ((ℕ × ℕ) × (ℕ × ℕ))) :
    (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm idx).IsPositive := by
  cases idx with
  | inl idx =>
      exact gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm_isPositive idx
  | inr zw =>
      exact gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_isPositive zw

theorem summable_norm_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm :
    Summable (fun idx : ((ℕ × ℕ) × Fin 6) ⊕ ((ℕ × ℕ) × (ℕ × ℕ)) =>
      ‖gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm idx‖) := by
  apply Summable.sum
  · change Summable (fun idx : (ℕ × ℕ) × Fin 6 =>
      ‖gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖)
    exact summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
  · change Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      ‖gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw‖)
    exact summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm

/-- Packet covariance plus global mean dispersion: source-defined nonlocal polar completion. -/
def gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert :=
  ∑' idx : ((ℕ × ℕ) × Fin 6) ⊕ ((ℕ × ℕ) × (ℕ × ℕ)),
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm idx

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_eq_add :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator =
      gammaSewnCriticalPhysicalPluckerSpectralOperator +
        gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator := by
  have hleft : HasSum
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm ∘ Sum.inl)
      gammaSewnCriticalPhysicalPluckerSpectralOperator := by
    change HasSum gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
      gammaSewnCriticalPhysicalPluckerSpectralOperator
    simpa [gammaSewnCriticalPhysicalPluckerSpectralOperator] using
      (Summable.of_norm
        summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm).hasSum
  have hright : HasSum
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm ∘ Sum.inr)
      gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator := by
    change HasSum gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm
      gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator
    simpa [gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator] using
      (Summable.of_norm
        summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm).hasSum
  exact (hleft.sum hright).tsum_eq

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isPositive :
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator.IsPositive := by
  apply isPositive_tsum_of_summable
  · exact Summable.of_norm
      summable_norm_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm
  · exact gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm_isPositive

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_memSchattenClass_one :
    MemSchattenClass 1 gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator := by
  exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm_hasRankLE
    summable_norm_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedRankOneTerm

theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isCompact :
    IsCompactOperator gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator :=
  gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_memSchattenClass_one.isCompactOperator
    (by norm_num)

/-- Closed construction certificate: arbitrary cross-packet coefficient interference is retained
inside positive rank-one mean differences, and the infinite completion is trace class. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarization_certificate :
    (∀ zw, HasRankLE
      (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw) 1) ∧
    (∀ zw,
      (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw).IsPositive) ∧
    Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      ‖gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw‖) ∧
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator.IsPositive ∧
    MemSchattenClass 1 gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator ∧
    IsCompactOperator gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator := by
  exact ⟨gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_hasRankLE,
    gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm_isPositive,
    summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isPositive,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_memSchattenClass_one,
    gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isCompact⟩

end RHTower.HedenmalmThetaSource
