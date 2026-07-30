import GaloisForLFunctions.HTGeometry.ObserverActionReplicaRecurrenceLaw
import GaloisForLFunctions.HTGeometry.RecurrenceSwapInteractionReconstructionLaw
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw

/-!
# Resolved recurrence is complete spectral-relation tomography

For a finite spectrum, a balanced integer spectral relation has an exact
replica height: the total positive coefficient mass. This file joins that
arithmetic height law to the completed-time phase kernel. It proves that
replica order `n` detects exactly the annihilating projective characters of
height at most `n`, and that the complete resolved recurrence hierarchy
reconstructs the entire projective spectral relation lattice.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every character realized by equal positive and negative replica counts
is projectively balanced. -/
theorem spectralCharacterBalanced_of_replicaRealizes
    {I : Type*} [Fintype I]
    {n : ℕ} {k : I → ℤ}
    (h : SpectralCharacterReplicaRealizes n k) :
    SpectralCharacterBalanced k := by
  rcases h with ⟨p, q, hp, hq, hk⟩
  unfold SpectralCharacterBalanced
  calc
    (∑ i, k i) =
        ∑ i, ((p i : ℤ) - (q i : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hk i
    _ = ((∑ i, p i : ℕ) : ℤ) -
        ((∑ i, q i : ℕ) : ℤ) := by
          rw [Finset.sum_sub_distrib]
          norm_cast
    _ = (n : ℤ) - (n : ℤ) := by rw [hp, hq]
    _ = 0 := sub_self _

/-- All integer spectral relations, including the global-phase direction. -/
def spectralRelationLattice
    {I : Type*} [Fintype I]
    (energy : I → ℝ) : AddSubgroup (I → ℤ) where
  carrier := {k | finiteTorusCharacterDetuning k energy = 0}
  zero_mem' := by simp [finiteTorusCharacterDetuning]
  add_mem' := by
    intro k l hk hl
    unfold finiteTorusCharacterDetuning at hk hl ⊢
    change
      (∑ i, (((k i + l i : ℤ) : ℤ) : ℝ) * energy i) = 0
    push_cast
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    rw [hk, hl, add_zero]
  neg_mem' := by
    intro k hk
    unfold finiteTorusCharacterDetuning at hk ⊢
    change (∑ i, ((-k i : ℤ) : ℝ) * energy i) = 0
    push_cast
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib, hk, neg_zero]

@[simp]
theorem mem_spectralRelationLattice_iff
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : I → ℤ) :
    k ∈ spectralRelationLattice energy ↔
      finiteTorusCharacterDetuning k energy = 0 :=
  Iff.rfl

/-- Boolean Fourier signature of the complete integer relation lattice. -/
def spectralRelationIndicator
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : I → ℤ) : ℂ :=
  by
    classical
    exact if k ∈ spectralRelationLattice energy then 1 else 0

/-- Every Fourier coordinate of the sampled phase orbit converges to the
indicator of the corresponding exact integer relation. -/
theorem finiteTorusPhase_mFourier_tendsto_relationIndicator
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : I → ℤ) :
    Tendsto
      (fun A =>
        ∫ x, UnitAddTorus.mFourier k x
          ∂(finiteTorusPhaseProbabilityMeasure energy A :
            MeasureTheory.Measure (UnitAddTorus I)))
      atTop
      (𝓝 (spectralRelationIndicator energy k)) := by
  classical
  have ht :=
    symmetricPhaseAverage_tendsto_resonanceIndicator
      (finiteTorusCharacterDetuning k energy)
  have hevent :
      (fun A =>
        symmetricPhaseAverage A
          (finiteTorusCharacterDetuning k energy)) =ᶠ[atTop]
        (fun A =>
          ∫ x, UnitAddTorus.mFourier k x
            ∂(finiteTorusPhaseProbabilityMeasure energy A :
              MeasureTheory.Measure (UnitAddTorus I))) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with A hA
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      symmetricPhaseAverage_eq_sinc A
        (finiteTorusCharacterDetuning k energy) hA]
  simpa [spectralRelationIndicator] using ht.congr' hevent

/-- **Universal finite recurrence ensemble.** Every finite real spectrum
has a unique completed-time phase ensemble. Its Fourier transform is exactly
the indicator of the spectrum's integer relation lattice. -/
theorem existsUnique_spectralRelationPhaseEnsemble
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    ∃! μ : MeasureTheory.ProbabilityMeasure (UnitAddTorus I),
      Tendsto
        (finiteTorusPhaseProbabilityMeasure energy)
        atTop (𝓝 μ) ∧
      ∀ k : I → ℤ,
        (∫ x, UnitAddTorus.mFourier k x
          ∂(μ : MeasureTheory.Measure (UnitAddTorus I))) =
            spectralRelationIndicator energy k := by
  exact
    existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
      (finiteTorusPhaseProbabilityMeasure energy)
      (spectralRelationIndicator energy)
      (finiteTorusPhase_mFourier_tendsto_relationIndicator energy)

/-- Canonical completed-time phase ensemble selected by the relation
lattice. -/
def spectralRelationPhaseEnsemble
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    MeasureTheory.ProbabilityMeasure (UnitAddTorus I) :=
  Classical.choose
    (existsUnique_spectralRelationPhaseEnsemble energy)

/-- Uniform centered-time sampling converges weakly to the canonical
relation-lattice phase ensemble. -/
theorem finiteTorusPhaseProbabilityMeasure_tendsto_relationPhaseEnsemble
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    Tendsto
      (finiteTorusPhaseProbabilityMeasure energy)
      atTop
      (𝓝 (spectralRelationPhaseEnsemble energy)) :=
  (Classical.choose_spec
    (existsUnique_spectralRelationPhaseEnsemble energy)).1.1

/-- Fourier transform of the canonical ensemble. -/
theorem spectralRelationPhaseEnsemble_mFourier_integral
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : I → ℤ) :
    (∫ x, UnitAddTorus.mFourier k x
      ∂(spectralRelationPhaseEnsemble energy :
        MeasureTheory.Measure (UnitAddTorus I))) =
      spectralRelationIndicator energy k :=
  (Classical.choose_spec
    (existsUnique_spectralRelationPhaseEnsemble energy)).1.2 k

/-- The completed phase ensemble and the complete integer relation lattice
are equivalent invariants of a finite spectrum. -/
theorem spectralRelationLattice_eq_iff_phaseEnsemble_eq
    {I : Type*} [Fintype I]
    (energy₁ energy₂ : I → ℝ) :
    spectralRelationLattice energy₁ =
        spectralRelationLattice energy₂ ↔
      spectralRelationPhaseEnsemble energy₁ =
        spectralRelationPhaseEnsemble energy₂ := by
  constructor
  · intro hlattice
    apply probabilityMeasure_ext_of_mFourier_integral_eq
    intro k
    rw [spectralRelationPhaseEnsemble_mFourier_integral,
      spectralRelationPhaseEnsemble_mFourier_integral]
    have hkiff :
        k ∈ spectralRelationLattice energy₁ ↔
          k ∈ spectralRelationLattice energy₂ := by
      rw [hlattice]
    by_cases hk : k ∈ spectralRelationLattice energy₁
    · rw [spectralRelationIndicator, if_pos hk,
        spectralRelationIndicator, if_pos (hkiff.mp hk)]
    · rw [spectralRelationIndicator, if_neg hk,
        spectralRelationIndicator,
        if_neg (fun h => hk (hkiff.mpr h))]
  · intro hensemble
    apply AddSubgroup.ext
    intro k
    have hindicator :
        spectralRelationIndicator energy₁ k =
          spectralRelationIndicator energy₂ k := by
      rw [← spectralRelationPhaseEnsemble_mFourier_integral,
        ← spectralRelationPhaseEnsemble_mFourier_integral,
        hensemble]
    unfold spectralRelationIndicator at hindicator
    constructor
    · intro hk
      by_contra hnot
      rw [if_pos hk, if_neg hnot] at hindicator
      exact one_ne_zero hindicator
    · intro hk
      by_contra hnot
      rw [if_neg hnot, if_pos hk] at hindicator
      exact zero_ne_one hindicator

/-- The additive lattice of all balanced integer characters whose energy
detuning vanishes. It is the complete projective arithmetic constraint
object of a finite spectrum. -/
def projectiveSpectralRelationLattice
    {I : Type*} [Fintype I]
    (energy : I → ℝ) : AddSubgroup (I → ℤ) where
  carrier := {k |
    SpectralCharacterBalanced k ∧
      finiteTorusCharacterDetuning k energy = 0}
  zero_mem' := by
    constructor
    · simp [SpectralCharacterBalanced]
    · simp [finiteTorusCharacterDetuning]
  add_mem' := by
    rintro k l ⟨hkBalanced, hkEnergy⟩
      ⟨hlBalanced, hlEnergy⟩
    constructor
    · unfold SpectralCharacterBalanced at hkBalanced hlBalanced ⊢
      simp only [Pi.add_apply, Finset.sum_add_distrib,
        hkBalanced, hlBalanced, add_zero]
    · unfold finiteTorusCharacterDetuning at hkEnergy hlEnergy ⊢
      simp only [Pi.add_apply, Int.cast_add, add_mul,
        Finset.sum_add_distrib]
      rw [hkEnergy, hlEnergy, add_zero]
  neg_mem' := by
    rintro k ⟨hkBalanced, hkEnergy⟩
    constructor
    · unfold SpectralCharacterBalanced at hkBalanced ⊢
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, hkBalanced,
        neg_zero]
    · unfold finiteTorusCharacterDetuning at hkEnergy ⊢
      simp only [Pi.neg_apply, Int.cast_neg, neg_mul,
        Finset.sum_neg_distrib, hkEnergy, neg_zero]

@[simp]
theorem mem_projectiveSpectralRelationLattice_iff
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : I → ℤ) :
    k ∈ projectiveSpectralRelationLattice energy ↔
      SpectralCharacterBalanced k ∧
        finiteTorusCharacterDetuning k energy = 0 :=
  Iff.rfl

/-- A resolved `n`-replica recurrence detector sees a character exactly
when the character occurs at order `n` and has zero spectral detuning. -/
def ResolvedReplicaDetects
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (n : ℕ) (k : I → ℤ) : Prop :=
  SpectralCharacterReplicaRealizes n k ∧
    finiteTorusCharacterDetuning k energy = 0

/-- **Exact replica filtration law.** Replica order `n` detects precisely
the projective spectral relations whose positive coefficient mass is at
most `n`. -/
theorem resolvedReplicaDetects_iff_relation_and_height_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (n : ℕ) (k : I → ℤ) :
    ResolvedReplicaDetects energy n k ↔
      k ∈ projectiveSpectralRelationLattice energy ∧
        spectralCharacterPositiveMass k ≤ n := by
  constructor
  · rintro ⟨hrealizes, henergy⟩
    exact
      ⟨⟨spectralCharacterBalanced_of_replicaRealizes hrealizes,
          henergy⟩,
        spectralCharacterPositiveMass_le_of_replicaRealizes
          hrealizes⟩
  · rintro ⟨⟨hbalanced, henergy⟩, hheight⟩
    exact
      ⟨spectralCharacterReplicaRealizes_of_balanced_of_positiveMass_le
          hbalanced hheight,
        henergy⟩

/-- Every projective spectral relation is first detected exactly at its
positive coefficient mass. -/
theorem relation_iff_detected_at_exact_replicaHeight
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (k : I → ℤ) :
    k ∈ projectiveSpectralRelationLattice energy ↔
      ResolvedReplicaDetects energy
        (spectralCharacterPositiveMass k) k := by
  rw [resolvedReplicaDetects_iff_relation_and_height_le]
  simp

/-- A symmetric completed-time phase reporter converges to one exactly at
zero detuning. -/
theorem symmetricPhaseAverage_tendsto_one_iff
    (detuning : ℝ) :
    Tendsto (fun T => symmetricPhaseAverage T detuning)
      atTop (𝓝 (1 : ℂ)) ↔ detuning = 0 := by
  constructor
  · intro hone
    have hindicator :=
      symmetricPhaseAverage_tendsto_resonanceIndicator detuning
    have hlimit :
        (if detuning = 0 then (1 : ℂ) else 0) = 1 :=
      tendsto_nhds_unique hindicator hone
    by_contra hne
    simp only [hne, if_false] at hlimit
    exact zero_ne_one hlimit
  · intro hzero
    subst detuning
    simpa using
      symmetricPhaseAverage_tendsto_resonanceIndicator 0

/-- The arithmetic detector predicate is exactly the operational statement
that the character occurs in the chosen replica layer and its pair-resolved
phase kernel converges to one. -/
theorem resolvedReplicaDetects_iff_realizes_and_phaseAverage
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (n : ℕ) (k : I → ℤ) :
    ResolvedReplicaDetects energy n k ↔
      SpectralCharacterReplicaRealizes n k ∧
        Tendsto
          (fun T => symmetricPhaseAverage T
            (finiteTorusCharacterDetuning k energy))
          atTop (𝓝 (1 : ℂ)) := by
  unfold ResolvedReplicaDetects
  rw [symmetricPhaseAverage_tendsto_one_iff]

/-- With full-support weights, exact detector occurrence is visible as a
strictly positive character coefficient in the actual survival-fidelity
replica polynomial. -/
theorem resolvedReplicaDetects_iff_positiveCoefficient_and_phaseAverage
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (energy : I → ℝ) (n : ℕ) (k : I → ℤ) :
    ResolvedReplicaDetects energy n k ↔
      0 < fidelityReplicaCharacterCoefficient weight n k ∧
        Tendsto
          (fun T => symmetricPhaseAverage T
            (finiteTorusCharacterDetuning k energy))
          atTop (𝓝 (1 : ℂ)) := by
  rw [resolvedReplicaDetects_iff_realizes_and_phaseAverage,
    fidelityReplicaCharacterCoefficient_pos_iff_realizes hweight]

/-- **Complete resolved-recurrence tomography.** Two finite spectra have
the same projective spectral relation lattice exactly when every character
is detected at every replica order for one spectrum iff it is detected for
the other. -/
theorem relationLattice_eq_iff_all_resolvedReplicaDetectors_eq
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy₁ energy₂ : I → ℝ) :
    projectiveSpectralRelationLattice energy₁ =
        projectiveSpectralRelationLattice energy₂ ↔
      ∀ n k,
        (ResolvedReplicaDetects energy₁ n k ↔
          ResolvedReplicaDetects energy₂ n k) := by
  constructor
  · intro hlattice n k
    rw [resolvedReplicaDetects_iff_relation_and_height_le,
      resolvedReplicaDetects_iff_relation_and_height_le,
      hlattice]
  · intro hdetectors
    ext k
    rw [relation_iff_detected_at_exact_replicaHeight,
      relation_iff_detected_at_exact_replicaHeight]
    exact hdetectors (spectralCharacterPositiveMass k) k

/-- Detection is monotone in replica order: once a relation is visible, it
remains visible at every higher layer. -/
theorem ResolvedReplicaDetects.mono
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} {m n : ℕ} {k : I → ℤ}
    (hdetect : ResolvedReplicaDetects energy m k)
    (hmn : m ≤ n) :
    ResolvedReplicaDetects energy n k := by
  rw [resolvedReplicaDetects_iff_relation_and_height_le] at hdetect ⊢
  exact ⟨hdetect.1, hdetect.2.trans hmn⟩

/-! ## Arbitrarily delayed relations in three energy levels -/

/-- A balanced three-level relation whose exact replica height is `m`. -/
def delayedThreeLevelRelation (m : ℕ) : Fin 3 → ℤ :=
  ![(m : ℤ) - 1, 1, -(m : ℤ)]

/-- Three real energy levels on which the delayed relation vanishes. -/
def delayedThreeLevelSpectrum (m : ℕ) : Fin 3 → ℝ :=
  ![0, (m : ℝ), 1]

/-- The delayed three-level character is projectively balanced. -/
theorem delayedThreeLevelRelation_balanced (m : ℕ) :
    SpectralCharacterBalanced (delayedThreeLevelRelation m) := by
  simp [SpectralCharacterBalanced, delayedThreeLevelRelation,
    Fin.sum_univ_three]

/-- The delayed relation has exact arithmetic height `m` whenever
`m` is positive. -/
theorem delayedThreeLevelRelation_positiveMass
    (m : ℕ) (hm : 0 < m) :
    spectralCharacterPositiveMass (delayedThreeLevelRelation m) = m := by
  have hmz : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
  simp [spectralCharacterPositiveMass, delayedThreeLevelRelation,
    Fin.sum_univ_three, Int.toNat_of_nonneg hmz,
    Int.toNat_of_nonpos]

/-- The delayed character is an exact relation of its three-level
spectrum. -/
theorem delayedThreeLevelRelation_mem_relationLattice (m : ℕ) :
    delayedThreeLevelRelation m ∈
      projectiveSpectralRelationLattice
        (delayedThreeLevelSpectrum m) := by
  constructor
  · exact delayedThreeLevelRelation_balanced m
  · simp [finiteTorusCharacterDetuning, delayedThreeLevelRelation,
      delayedThreeLevelSpectrum, Fin.sum_univ_three]

/-- **Unbounded detector-depth law in three levels.** For every positive
`m`, one explicit relation in a three-level spectrum is detected by replica
order `n` exactly when `m ≤ n`. Thus recurrence constraints can first appear
at arbitrarily high correlation order without increasing spectral size. -/
theorem delayedThreeLevelRelation_detected_iff
    (m n : ℕ) (hm : 0 < m) :
    ResolvedReplicaDetects
        (delayedThreeLevelSpectrum m) n
        (delayedThreeLevelRelation m) ↔
      m ≤ n := by
  rw [resolvedReplicaDetects_iff_relation_and_height_le,
    delayedThreeLevelRelation_positiveMass m hm]
  exact and_iff_right
    (delayedThreeLevelRelation_mem_relationLattice m)

/-- The delayed relation is invisible at every smaller replica order. -/
theorem not_delayedThreeLevelRelation_detected_of_lt
    (m n : ℕ) (hm : 0 < m) (hnm : n < m) :
    ¬ ResolvedReplicaDetects
        (delayedThreeLevelSpectrum m) n
        (delayedThreeLevelRelation m) := by
  rw [delayedThreeLevelRelation_detected_iff m n hm]
  omega

end

end GaloisForLFunctions.HTGeometry
