import GaloisForLFunctions.HTGeometry.LinearSpectrumAffineEscape
import GaloisForLFunctions.HTGeometry.ChainVwaSphereNull
import GaloisForLFunctions.HTGeometry.SpectralRecurrenceExponentLaw
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import GaloisForLFunctions.HTGeometry.QuditPathChainRecurrenceExponent

/-!
# One local qubit path simultaneously saturates recurrence and collision laws

The numbered Pauli basis is exactly the full real space of traceless onsite and nearest-neighbour
two-qubit Hamiltonians on an open path.  Homogeneous relation escape upgrades to affine escape in
this linear family.  On one common simple-spectrum chart, almost every coefficient vector then has
maximal projective rank, the sharp full-gap and clock-normalized first-return exponents, and every
positive-weight replica moment at its unavoidable permutation floor.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Lowest sorted spectral level. -/
def qubitPathRecurrenceAnchor (k : ℕ) : Fin (2 ^ (k + 3)) :=
  ⟨0, Nat.two_pow_pos _⟩

/-- Second sorted spectral level, used as the winding clock. -/
def qubitPathRecurrenceClock (k : ℕ) : Fin (2 ^ (k + 3)) :=
  ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩

/-- Every sorted spectral level beyond the anchor. -/
def qubitPathRecurrenceIndex (k : ℕ) :
    Fin (2 ^ (k + 3) - 1) → Fin (2 ^ (k + 3)) :=
  fun j => ⟨j.1 + 1, by omega⟩

/-- Every sorted spectral level beyond the anchor and clock. -/
def qubitPathWindingIndex (k : ℕ) :
    Fin (2 ^ (k + 3) - 2) → Fin (2 ^ (k + 3)) :=
  fun j => ⟨j.1 + 2, by omega⟩

theorem qubitPathRecurrenceIndex_injective (k : ℕ) :
    Function.Injective (qubitPathRecurrenceIndex k) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [qubitPathRecurrenceIndex] at h
  omega

theorem qubitPathWindingIndex_injective (k : ℕ) :
    Function.Injective (qubitPathWindingIndex k) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [qubitPathWindingIndex] at h
  omega

theorem qubitPathRecurrenceIndex_ne_anchor (k : ℕ) (j : Fin (2 ^ (k + 3) - 1)) :
    qubitPathRecurrenceIndex k j ≠ qubitPathRecurrenceAnchor k := by
  intro h
  have hv := congrArg Fin.val h
  simp [qubitPathRecurrenceIndex, qubitPathRecurrenceAnchor] at hv

theorem qubitPathWindingIndex_ne_anchor (k : ℕ) (j : Fin (2 ^ (k + 3) - 2)) :
    qubitPathWindingIndex k j ≠ qubitPathRecurrenceAnchor k := by
  intro h
  have hv := congrArg Fin.val h
  simp [qubitPathWindingIndex, qubitPathRecurrenceAnchor] at hv

theorem qubitPathWindingIndex_ne_clock (k : ℕ) (j : Fin (2 ^ (k + 3) - 2)) :
    qubitPathWindingIndex k j ≠ qubitPathRecurrenceClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [qubitPathWindingIndex, qubitPathRecurrenceClock] at hv

theorem qubitPathRecurrenceAnchor_ne_clock (k : ℕ) :
    qubitPathRecurrenceAnchor k ≠ qubitPathRecurrenceClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [qubitPathRecurrenceAnchor, qubitPathRecurrenceClock] at hv

/-- Canonically enumerated energy spectrum of one path Hamiltonian. -/
def qubitPathEnergy (k : ℕ)
    (θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3)) → ℝ :=
  (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues

/-- Increasing enumeration of the same spectrum. -/
def qubitPathSortedEnergy (k : ℕ)
    (θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3)) → ℝ :=
  sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3)) θ

/-- All anchored gaps in turns per unit stroboscopic time. -/
def qubitPathDiscreteFrequency (k : ℕ)
    (θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3) - 1) → ℝ :=
  anchoredGapMap (2 * Real.pi) (qubitPathSortedEnergy k θ)
    (qubitPathRecurrenceAnchor k) (qubitPathRecurrenceIndex k)

/-- All remaining gaps divided by the first positive gap. -/
def qubitPathWindingFrequency (k : ℕ)
    (θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :
    Fin (2 ^ (k + 3) - 2) → ℝ :=
  anchoredGapRatioMap (qubitPathSortedEnergy k θ)
    (qubitPathRecurrenceAnchor k) (qubitPathRecurrenceClock k)
    (qubitPathWindingIndex k)

/-- The exact nearest-neighbour Pauli path family escapes every prescribed affine spectral
relation, not only its zero level. -/
theorem chainPauliFin_spectrumEscapesAffineRelations (k : ℕ) :
    SpectrumEscapesAffineRelations
      (Set.range (spectralEnsembleMatrix (chainPauliFin (k + 3)))) :=
  (chainPauliFin_spectrumEscapesRealRelations k).linearFamily_toAffine _

/-- **Every-chart same-Hamiltonian recurrence--collision law.**  On every nonempty preconnected
open chart in the simple-spectrum locus of the full traceless onsite-plus-nearest-neighbour Pauli
coefficient space, almost every one fixed Hamiltonian simultaneously has maximal projective rank,
the sharp full-gap and clock-normalized first-return exponents, and every positive-weight replica
moment at its permutation floor. -/
theorem qubitPath_everyChart_sameDraw_recurrenceCollisionLaw (k : ℕ)
    {U : Set (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ)}
    (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus (chainPauliFin_isHermitian (k + 3))) :
    ∀ᵐ θ ∂volume, θ ∈ U →
      MaximallyProjectiveEnergy (qubitPathEnergy k θ) ∧
      Tendsto
        (fun r : ℝ =>
          Real.log (firstHit (qubitPathDiscreteFrequency k θ) r) /
            Real.log (1 / r))
        (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 1 : ℕ) : ℝ))) ∧
      Tendsto
        (fun r : ℝ =>
          Real.log (firstHit (qubitPathWindingFrequency k θ) r) /
            Real.log (1 / r))
        (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 2 : ℕ) : ℝ))) ∧
      ∀ weight : Fin (2 ^ (k + 3)) → ℝ, (∀ i, 0 < weight i) →
        (∀ m : ℕ,
          fidelityReplicaCollisionMass weight (qubitPathEnergy k θ) m =
            fidelityReplicaPermutationFloor weight m) ∧
        ∀ m : ℕ,
          Tendsto
            (finiteSpectralSurvivalFidelityMean weight (qubitPathEnergy k θ) m)
            atTop (𝓝 (fidelityReplicaPermutationFloor weight m : ℂ)) := by
  letI : NeZero (Fintype.card (ChainLabel (k + 3))) :=
    instNeZeroCardChainLabel k
  have hD4 : 4 ≤ 2 ^ (k + 3) := by
    calc
      4 = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hDiscrete := ae_tendsto_log_firstHit_sortedGap
    (n := 2 ^ (k + 3) - 1)
    (anchor := qubitPathRecurrenceAnchor k)
    (ι := qubitPathRecurrenceIndex k) (scale := 2 * Real.pi)
    (by omega) (chainPauliFin_isHermitian (k + 3))
    (chainPauliFin_spectrumEscapesAffineRelations k)
    (qubitPathRecurrenceIndex_injective k)
    (qubitPathRecurrenceIndex_ne_anchor k)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    hUopen hUconn hUne hUsimple
  have hWinding := ae_tendsto_log_firstHit_sortedGapRatio
    (n := 2 ^ (k + 3) - 2)
    (anchor := qubitPathRecurrenceAnchor k)
    (clock := qubitPathRecurrenceClock k)
    (ι := qubitPathWindingIndex k) (by omega)
    (chainPauliFin_isHermitian (k + 3))
    (chainPauliFin_spectrumEscapesRealRelations k)
    (qubitPathWindingIndex_injective k)
    (qubitPathWindingIndex_ne_anchor k)
    (qubitPathWindingIndex_ne_clock k)
    (qubitPathRecurrenceAnchor_ne_clock k)
    hUopen hUconn hUne hUsimple
  have hmaxAE : ∀ᵐ θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ ∂volume,
      MaximallyProjectiveEnergy (qubitPathEnergy k θ) := by
    rw [ae_iff]
    simpa [qubitPathEnergy] using volume_notMaximallyProjective_chain_eq_zero k
  filter_upwards [hmaxAE, hDiscrete, hWinding] with θ hmax hdisc hwind hθU
  refine ⟨hmax, ?_, ?_, ?_⟩
  · simpa [qubitPathDiscreteFrequency, qubitPathSortedEnergy] using hdisc hθU
  · simpa [qubitPathWindingFrequency, qubitPathSortedEnergy] using hwind hθU
  · intro weight hweight
    exact ⟨
      (all_fidelityReplicaCollisionMass_eq_floor_iff hweight
        (qubitPathEnergy k θ)).2 hmax,
      (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff hweight
        (qubitPathEnergy k θ)).2 hmax⟩

/-- **Same-Hamiltonian local recurrence--collision law.**  On a nonempty simple-spectrum chart of
the full traceless onsite-plus-nearest-neighbour Pauli coefficient space, almost every one fixed
Hamiltonian simultaneously has maximal projective rank, full-gap first-return exponent
`2^(k+3)-1`, winding first-return exponent `2^(k+3)-2`, every replica collision mass at its
permutation floor, and every long-time survival-fidelity moment converging to that floor. -/
theorem qubitPath_sameDraw_recurrenceCollisionLaw (k : ℕ) :
    ∃ U : Set (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧
      U ⊆ simpleEnsembleLocus (chainPauliFin_isHermitian (k + 3)) ∧
      ∀ᵐ θ ∂volume, θ ∈ U →
        MaximallyProjectiveEnergy (qubitPathEnergy k θ) ∧
        Tendsto
          (fun r : ℝ =>
            Real.log (firstHit (qubitPathDiscreteFrequency k θ) r) /
              Real.log (1 / r))
          (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 1 : ℕ) : ℝ))) ∧
        Tendsto
          (fun r : ℝ =>
            Real.log (firstHit (qubitPathWindingFrequency k θ) r) /
              Real.log (1 / r))
          (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 2 : ℕ) : ℝ))) ∧
        ∀ weight : Fin (2 ^ (k + 3)) → ℝ, (∀ i, 0 < weight i) →
          (∀ m : ℕ,
            fidelityReplicaCollisionMass weight (qubitPathEnergy k θ) m =
              fidelityReplicaPermutationFloor weight m) ∧
          ∀ m : ℕ,
            Tendsto
              (finiteSpectralSurvivalFidelityMean weight (qubitPathEnergy k θ) m)
              atTop (𝓝 (fidelityReplicaPermutationFloor weight m : ℂ)) := by
  letI : NeZero (Fintype.card (ChainLabel (k + 3))) :=
    instNeZeroCardChainLabel k
  have hD4 : 4 ≤ 2 ^ (k + 3) := by
    calc
      4 = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  let hP := chainPauliFin_isHermitian (k + 3)
  have hAffine := chainPauliFin_spectrumEscapesAffineRelations k
  obtain ⟨U, hUopen, hUconn, hUne, hUsimple⟩ :=
    exists_chart_of_spectrumEscapes (by omega) hP hAffine
  have hDiscrete := ae_tendsto_log_firstHit_sortedGap
    (n := 2 ^ (k + 3) - 1)
    (anchor := qubitPathRecurrenceAnchor k)
    (ι := qubitPathRecurrenceIndex k) (scale := 2 * Real.pi)
    (by omega) hP hAffine
    (qubitPathRecurrenceIndex_injective k)
    (qubitPathRecurrenceIndex_ne_anchor k)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    hUopen hUconn hUne hUsimple
  have hWinding := ae_tendsto_log_firstHit_sortedGapRatio
    (n := 2 ^ (k + 3) - 2)
    (anchor := qubitPathRecurrenceAnchor k)
    (clock := qubitPathRecurrenceClock k)
    (ι := qubitPathWindingIndex k) (by omega) hP
    (chainPauliFin_spectrumEscapesRealRelations k)
    (qubitPathWindingIndex_injective k)
    (qubitPathWindingIndex_ne_anchor k)
    (qubitPathWindingIndex_ne_clock k)
    (qubitPathRecurrenceAnchor_ne_clock k)
    hUopen hUconn hUne hUsimple
  have hmaxAE : ∀ᵐ θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ ∂volume,
      MaximallyProjectiveEnergy (qubitPathEnergy k θ) := by
    rw [ae_iff]
    simpa [qubitPathEnergy] using volume_notMaximallyProjective_chain_eq_zero k
  refine ⟨U, hUopen, hUconn, hUne, hUsimple, ?_⟩
  filter_upwards [hmaxAE, hDiscrete, hWinding] with θ hmax hdisc hwind hθU
  refine ⟨hmax, ?_, ?_, ?_⟩
  · simpa [qubitPathDiscreteFrequency, qubitPathSortedEnergy] using hdisc hθU
  · simpa [qubitPathWindingFrequency, qubitPathSortedEnergy] using hwind hθU
  · intro weight hweight
    exact ⟨
      (all_fidelityReplicaCollisionMass_eq_floor_iff hweight
        (qubitPathEnergy k θ)).2 hmax,
      (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff hweight
        (qubitPathEnergy k θ)).2 hmax⟩

end

end GaloisForLFunctions.HTGeometry
