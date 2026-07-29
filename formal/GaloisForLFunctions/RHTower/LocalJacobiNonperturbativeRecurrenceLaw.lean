import GaloisForLFunctions.RHTower.NonperturbativeQuantumRecurrenceSeparationLaw
import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# Local Jacobi form of nonperturbative recurrence separation

This file closes the algebraic locality gap for the compact-spectrum
nonperturbative recurrence law.  Every compactly carried atomless probability
spectrum and every flat atomic completion at finite coupling have strictly
positive moment forms.  Their cyclic energy-multiplication laws therefore
admit exact connected Jacobi coordinates: multiplication by energy is
tridiagonal in the orthogonal-polynomial modes, and every lower
nearest-neighbour coefficient is strictly positive.

The construction is universal in the base spectrum, the compact carrier, and
the selected completion energy.  Combined with
`NonperturbativeQuantumRecurrenceSeparationLaw`, it shows that recurrence
separation beyond every perturbative order persists inside connected
nearest-neighbour cyclic Hamiltonian data.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- Real moment sequence of a spectral measure. -/
def spectralMomentSequence (mu : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ x, x ^ n ∂mu

theorem spectralMomentSequence_eq_integral
    (mu : Measure ℝ) (n : ℕ) :
    spectralMomentSequence mu n = ∫ x, x ^ n ∂mu :=
  rfl

/-- An atomless probability measure charges the complement of every finite
set. -/
theorem atomlessProbability_compl_finset_pos
    (mu : ProbabilityMeasure ℝ)
    [NoAtoms (mu : Measure ℝ)] (F : Finset ℝ) :
    0 < (mu : Measure ℝ) {x : ℝ | x ∉ F} := by
  have hF : (mu : Measure ℝ) (F : Set ℝ) = 0 := by
    induction F using Finset.induction_on with
    | empty =>
        simp
    | @insert a F ha ih =>
        rw [Finset.coe_insert, Set.insert_eq]
        rw [measure_union]
        · rw [measure_singleton, ih, add_zero]
        · simp [ha]
        · exact F.measurableSet
  have hmeas : MeasurableSet (F : Set ℝ) :=
    F.measurableSet
  rw [show {x : ℝ | x ∉ F} = (F : Set ℝ)ᶜ by
    ext x
    simp]
  rw [measure_compl hmeas (by simp), hF]
  simp

/-- Every continuous power is integrable against a finite measure carried by
a compact set. -/
theorem integrable_pow_of_compact_carried
    (mu : ProbabilityMeasure ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hcarried : (mu : Measure ℝ) Kᶜ = 0)
    (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (mu : Measure ℝ) := by
  have hOn :
      IntegrableOn (fun x : ℝ => x ^ n) K (mu : Measure ℝ) :=
    (continuous_id.pow n).continuousOn.integrableOn_compact hK
  have hae : ∀ᵐ x ∂(mu : Measure ℝ), x ∈ K := by
    rw [ae_iff]
    exact hcarried
  change Integrable (fun x : ℝ => x ^ n)
    ((mu : Measure ℝ).restrict K) at hOn
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hOn

/-- Compactly carried atomless probability spectra generate strictly positive
moment forms. -/
theorem positiveMomentForm_spectralMomentSequence_of_compact_atomless
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    {K : Set ℝ} (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0) :
    HTGeometry.PositiveMomentForm
      (spectralMomentSequence (base : Measure ℝ)) := by
  exact HTGeometry.positiveMomentForm_of_infiniteSupport
    (spectralMomentSequence (base : Measure ℝ))
    (spectralMomentSequence_eq_integral (base : Measure ℝ))
    (integrable_pow_of_compact_carried base hK hbase)
    (atomlessProbability_compl_finset_pos base)

/-- At every finite coupling, the atomic completion retains infinite support from
every atomless base spectrum. -/
theorem nonperturbativeAtomicCompletion_compl_finset_pos
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy : ℝ)
    (g : ℝ) (F : Finset ℝ) :
    0 <
      (nonperturbativeAtomicCompletion
        base energy g : Measure ℝ) {x : ℝ | x ∉ F} := by
  rw [nonperturbativeAtomicCompletion,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  have hbase :
      0 < (base : Measure ℝ) {x : ℝ | x ∉ F} :=
    atomlessProbability_compl_finset_pos base F
  have hcoef :
      0 < 1 - nonperturbativeCouplingWeight g :=
    tsub_pos_iff_lt.mpr (nonperturbativeCouplingWeight_lt_one g)
  have hproduct :
      0 <
        (1 - nonperturbativeCouplingWeight g) *
          (base : Measure ℝ) {x : ℝ | x ∉ F} :=
    ENNReal.mul_pos hcoef.ne' hbase.ne'
  exact lt_of_lt_of_le hproduct (le_add_left le_rfl)

/-- Every flat atomic completion of a compact atomless spectrum has a
strictly positive moment form. -/
theorem positiveMomentForm_nonperturbativeAtomicCompletion
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    (energy : ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K)
    (g : ℝ) :
    HTGeometry.PositiveMomentForm
      (spectralMomentSequence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ)) := by
  exact HTGeometry.positiveMomentForm_of_infiniteSupport
    (spectralMomentSequence
      (nonperturbativeAtomicCompletion
        base energy g : Measure ℝ))
    (spectralMomentSequence_eq_integral
      (nonperturbativeAtomicCompletion
        base energy g : Measure ℝ))
    (integrable_pow_of_compact_carried
      (nonperturbativeAtomicCompletion base energy g)
      hK
      (nonperturbativeAtomicCompletion_carried
        base energy g hK.measurableSet hbase henergy))
    (nonperturbativeAtomicCompletion_compl_finset_pos
      base energy g)

/-- Exact nearest-neighbour locality of energy multiplication for every
compact atomless base spectrum. -/
theorem atomlessCompactSpectrum_energyMultiplication_remote_zero
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    {K : Set ℝ} (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    {n k : ℕ} (hk : k + 1 < n) :
    HTGeometry.momentInner
        (spectralMomentSequence (base : Measure ℝ))
        (Polynomial.X *
          HTGeometry.monicOrtho
            (spectralMomentSequence (base : Measure ℝ)) n)
        (HTGeometry.monicOrtho
          (spectralMomentSequence (base : Measure ℝ)) k) = 0 := by
  exact HTGeometry.monicOrtho_X_mul_inner_eq_zero
    (positiveMomentForm_spectralMomentSequence_of_compact_atomless
      base hK hbase) hk

/-- Exact nearest-neighbour locality survives every
nonperturbative atomic completion. -/
theorem atomicCompletion_energyMultiplication_remote_zero
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    (energy : ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K)
    (g : ℝ)
    {n k : ℕ} (hk : k + 1 < n) :
    let s :=
      spectralMomentSequence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ)
    HTGeometry.momentInner s
        (Polynomial.X * HTGeometry.monicOrtho s n)
        (HTGeometry.monicOrtho s k) = 0 := by
  dsimp only
  exact HTGeometry.monicOrtho_X_mul_inner_eq_zero
    (positiveMomentForm_nonperturbativeAtomicCompletion
      base energy hK hbase henergy g) hk

/-- Every lower Jacobi coefficient of the completed cyclic energy law is
strictly positive, so its nearest-neighbour chain is connected rather than a
direct sum with a decoupled recurrent site. -/
theorem atomicCompletion_Jacobi_lowerCoefficient_pos
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    (energy : ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K)
    (g : ℝ)
    (n : ℕ) :
    let s :=
      spectralMomentSequence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ)
    0 <
      HTGeometry.momentInner s
          (HTGeometry.monicOrtho s (n + 1))
          (HTGeometry.monicOrtho s (n + 1)) /
        HTGeometry.momentInner s
          (HTGeometry.monicOrtho s n)
          (HTGeometry.monicOrtho s n) := by
  dsimp only
  have h :=
    positiveMomentForm_nonperturbativeAtomicCompletion
      base energy hK hbase henergy g
  exact div_pos
    (HTGeometry.monicOrtho_inner_self_pos h (n + 1))
    (HTGeometry.monicOrtho_inner_self_pos h n)

/-- Exact connected three-term Jacobi law for the completed spectrum. -/
theorem atomicCompletion_energyMultiplication_threeTerm
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    (energy : ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K)
    (g : ℝ)
    (n : ℕ) :
    let s :=
      spectralMomentSequence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ)
    Polynomial.X * HTGeometry.monicOrtho s (n + 1) =
      HTGeometry.monicOrtho s (n + 2)
        + (HTGeometry.momentInner s
              (Polynomial.X * HTGeometry.monicOrtho s (n + 1))
              (HTGeometry.monicOrtho s (n + 1)) /
            HTGeometry.momentInner s
              (HTGeometry.monicOrtho s (n + 1))
              (HTGeometry.monicOrtho s (n + 1))) •
            HTGeometry.monicOrtho s (n + 1)
        + (HTGeometry.momentInner s
              (HTGeometry.monicOrtho s (n + 1))
              (HTGeometry.monicOrtho s (n + 1)) /
            HTGeometry.momentInner s
              (HTGeometry.monicOrtho s n)
              (HTGeometry.monicOrtho s n)) •
            HTGeometry.monicOrtho s n := by
  dsimp only
  exact HTGeometry.monicOrtho_three_term
    (positiveMomentForm_nonperturbativeAtomicCompletion
      base energy hK hbase henergy g) n

/-- Universal local nonperturbative recurrence separation law.  The complete
perturbative bounded-observable theory is unchanged, the exact completed
system recurs at every positive coupling while the atomless base does
not, and the completed cyclic energy law is a connected nearest-neighbour
Jacobi chain. -/
theorem every_compact_atomlessSpectrum_has_local_perturbativelyInvisible_recurrence
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)]
    (energy : ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K)
    {g : ℝ} (hg0 : 0 < g) :
    perturbativeBoundedSpectralObservableJet
        (nonperturbativeAtomicCompletion base energy) =
        perturbativeBoundedSpectralObservableJet
          (constantSpectrumFamily base) ∧
      HasPersistentMeanRecurrence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ) ∧
      recurrencePlateau
        (constantSpectrumFamily base g : Measure ℝ) = 0 ∧
      (∀ n : ℕ,
        let s :=
          spectralMomentSequence
            (nonperturbativeAtomicCompletion
              base energy g : Measure ℝ)
        0 <
          HTGeometry.momentInner s
              (HTGeometry.monicOrtho s (n + 1))
              (HTGeometry.monicOrtho s (n + 1)) /
            HTGeometry.momentInner s
              (HTGeometry.monicOrtho s n)
              (HTGeometry.monicOrtho s n)) := by
  refine ⟨
    perturbativeBoundedSpectralObservableJet_atomicCompletion_eq
      base energy,
    nonperturbativeAtomicCompletion_plateau_pos
      base energy hg0,
    constantSpectrumFamily_plateau_zero base g,
    ?_⟩
  intro n
  exact atomicCompletion_Jacobi_lowerCoefficient_pos
    base energy hK hbase henergy g n

end RHTower
