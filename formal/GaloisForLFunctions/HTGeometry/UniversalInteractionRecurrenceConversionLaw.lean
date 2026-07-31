import GaloisForLFunctions.HTGeometry.SeparableInteractionTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrenceCapstoneLaw

/-!
# Universal interaction conversion of recurrence constraints into time

Finite projective phase capacity has two complementary parts: operational
temporal dimension and exact recurrence-constraint rank. Their sum is fixed.
Consequently every increase of temporal dimension is exactly a loss of
recurrence constraints.

For two arbitrary nonempty finite spectra, one arbitrarily weak separable
diagonal interaction can complete this conversion. It erases every balanced
spectral relation, converts the entire uncoupled relation space into temporal
directions, and therefore creates at least the full rectangle-sector rank.
The same witness stays close on every fixed-time Heisenberg probe and
attains the permutation floor of every positive full-support replica
collision moment.
-/

open Set Filter MeasureTheory NormedSpace
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Universal phase-law constraint conversion.** On a fixed finite phase
carrier, every increase of operational temporal dimension is exactly the
decrease of almost-sure rational constraint rank. -/
theorem phaseLawTemporalDimension_sub_eq_constraintRank_sub
    {I : Type*} [Fintype I]
    (μ ν : ProbabilityMeasure (UnitAddTorus I))
    (hmono : phaseLawTemporalDimension μ ≤
      phaseLawTemporalDimension ν) :
    phaseLawTemporalDimension ν -
        phaseLawTemporalDimension μ =
      Module.finrank ℚ (phaseLawConstraintRationalSpace μ) -
        Module.finrank ℚ (phaseLawConstraintRationalSpace ν) := by
  have hμ := phaseLawTemporalDimension_add_constraintRank μ
  have hν := phaseLawTemporalDimension_add_constraintRank ν
  omega

/-- Spectral form of universal constraint conversion: on a fixed finite
energy carrier, temporal-rank gain equals exact balanced-relation-rank
loss. -/
theorem projectiveTemporalRank_sub_eq_relationRank_sub
    {d : ℕ}
    (energy₀ energy₁ : Fin (d + 1) → ℝ)
    (hmono : projectiveTemporalRank energy₀ ≤
      projectiveTemporalRank energy₁) :
    projectiveTemporalRank energy₁ -
        projectiveTemporalRank energy₀ =
      Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace energy₀) -
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace energy₁) := by
  have h₀ := projectiveTemporalRank_add_relationRank energy₀
  have h₁ := projectiveTemporalRank_add_relationRank energy₁
  omega

/-- A maximally projective target converts the complete initial relation
rank into temporal rank. -/
theorem
    projectiveTemporalRank_gain_eq_relationRank_of_maximallyProjective
    {d : ℕ}
    (energy₀ energy₁ : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy₁) :
    projectiveTemporalRank energy₁ -
        projectiveTemporalRank energy₀ =
      Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace energy₀) := by
  have h₁ : projectiveTemporalRank energy₁ = d :=
    projectiveTemporalRank_eq hmax
  have h₀ := projectiveTemporalRank_add_relationRank energy₀
  omega

/-- Maximal projective energy arithmetic is equivalent to zero rational
projective relation rank in the direction needed by the interaction law. -/
theorem projectiveRelationRank_eq_zero_of_maximallyProjective
    {d : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) :
    Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace energy) = 0 := by
  have hτ : projectiveTemporalRank energy = d :=
    projectiveTemporalRank_eq hmax
  have hconservation :=
    projectiveTemporalRank_add_relationRank energy
  omega

/-- **Weak separable interaction converts recurrence constraints into
time.** For every pair of nonempty finite spectra and every positive
operator-norm budget, a single separable diagonal interaction:

* erases the complete post-coupling balanced relation space;
* converts the entire uncoupled relation rank into temporal dimension;
* converts at least `m * n` rectangle-sector constraints;
* remains within the requested Hamiltonian norm budget;
* obeys the dimension-free fixed-time Heisenberg bound; and
* attains every positive full-support replica collision floor.

No arithmetic, simplicity, nondegeneracy, or genericity premise is imposed
on either uncoupled spectrum. -/
theorem exists_smallSeparableInteraction_fullConstraintConversion
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Fin (m + 1) ⊕ Fin (n + 1) → ℝ,
      MaximallyProjectiveEnergy
        (reindexedSeparableInteractionEnergy left right p) ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian
            (reindexedSeparableInteractionEnergy left right p) -
          RHTower.finiteIndexDiagonalHamiltonian
            (reindexedBipartiteProductEnergy left right)‖ ≤ δ ∧
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (reindexedSeparableInteractionEnergy left right p)) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (reindexedBipartiteProductEnergy left right)) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (reindexedBipartiteProductEnergy left right)) ∧
      Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (reindexedSeparableInteractionEnergy left right p)) = 0 ∧
      m * n ≤
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (reindexedBipartiteProductEnergy left right)) ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)))
          (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedSeparableInteractionEnergy
                  left right p))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedSeparableInteractionEnergy
                    left right p)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedBipartiteProductEnergy left right))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedBipartiteProductEnergy left right))))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : Fin (m * n + m + n + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (reindexedSeparableInteractionEnergy left right p) r =
            fidelityReplicaPermutationFloor weight r) := by
  obtain ⟨p, hmax, hnorm, hbase, hcoupled, hgain,
      hfinite, hcollision⟩ :=
    exists_smallSeparableInteraction_temporalDimensionMultiplication
      left right δ hδ
  have hexact :=
    projectiveTemporalRank_gain_eq_relationRank_of_maximallyProjective
      (reindexedBipartiteProductEnergy left right)
      (reindexedSeparableInteractionEnergy left right p)
      hmax
  have hzero :=
    projectiveRelationRank_eq_zero_of_maximallyProjective
      (reindexedSeparableInteractionEnergy left right p)
      hmax
  have hcapacity :=
    projectiveTemporalRank_add_relationRank
      (reindexedBipartiteProductEnergy left right)
  have hbaseRelations :
      m * n ≤
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (reindexedBipartiteProductEnergy left right)) := by
    omega
  have hphaseCoupled :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (reindexedSeparableInteractionEnergy left right p)
  have hphaseBase :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (reindexedBipartiteProductEnergy left right)
  have hconversion :
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (reindexedSeparableInteractionEnergy left right p)) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (reindexedBipartiteProductEnergy left right)) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (reindexedBipartiteProductEnergy left right)) := by
    rw [hphaseCoupled, hphaseBase]
    exact hexact
  exact ⟨p, hmax, hnorm, hconversion, hzero, hbaseRelations,
    hfinite, hcollision⟩

end

end GaloisForLFunctions.HTGeometry
