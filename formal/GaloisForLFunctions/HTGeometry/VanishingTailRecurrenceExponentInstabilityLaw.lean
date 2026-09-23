import GaloisForLFunctions.HTGeometry.AllStateSpectralSupportRecurrenceLaw
import GaloisForLFunctions.HTGeometry.ShellPlateauAssembly

/-!
# Vanishing-tail recurrence-exponent instability

This module proves a state-preparation instability law for unmeasured quantum recurrence.
An arbitrarily small positive population on every eigenlevel remains uniformly invisible in
survival fidelity above its population scale for all times, yet it activates the full spectral
support and therefore the maximal asymptotic first-return exponent.  The final theorem packages
the phenomenon on every open simple-spectrum chart of the full static nearest-neighbour qudit
path family and closes all dimension, locality, chart-existence, and genericity obligations.
-/

open Filter Topology MeasureTheory Set
open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

/-- Probability weights obtained by retaining mass `1 - η` on one anchor and distributing
the remaining mass uniformly over all `D` energy levels. -/
def anchorDopedWeights [NeZero D] (a : Fin D) (η : ℝ) : Fin D → ℝ :=
  fun j => (1 - η) * (if j = a then 1 else 0) + η * ((D : ℝ))⁻¹

theorem sum_anchorDopedWeights [NeZero D] (a : Fin D) (η : ℝ) :
    ∑ j, anchorDopedWeights a η j = 1 := by
  classical
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  simp [anchorDopedWeights, Finset.sum_add_distrib]
  field_simp
  ring

theorem anchorDopedWeights_pos [NeZero D] (a j : Fin D) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    0 < anchorDopedWeights a η j := by
  classical
  by_cases hja : j = a
  · simp [anchorDopedWeights, hja]
    have hD : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
    positivity
  · simp [anchorDopedWeights, hja]
    have hD : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
    positivity

theorem spectralWeightSupport_anchorDopedWeights [NeZero D] (a : Fin D) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    spectralWeightSupport (anchorDopedWeights a η) = Finset.univ := by
  ext j
  simp [mem_spectralWeightSupport_iff,
    (anchorDopedWeights_pos a j hη hη1).ne']

theorem norm_spectralReturnAmplitude_le_one (E p : Fin D → ℝ)
    (hpnn : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (t : ℝ) :
    ‖spectralReturnAmplitude E p t‖ ≤ 1 := by
  unfold spectralReturnAmplitude
  calc
    ‖∑ j, (p j : ℂ) * Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ j, ‖(p j : ℂ) * Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ j, p j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpnn j),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    _ = 1 := hp1

theorem spectralReturnAmplitude_anchorDopedWeights [NeZero D]
    (E : Fin D → ℝ) (a : Fin D) (η t : ℝ) :
    spectralReturnAmplitude E (anchorDopedWeights a η) t =
      (1 - η) * Complex.exp (((-(t * E a) : ℝ) : ℂ) * Complex.I) +
        η * spectralReturnAmplitude E (fun _ => ((D : ℝ))⁻¹) t := by
  classical
  unfold spectralReturnAmplitude anchorDopedWeights
  simp_rw [Complex.ofReal_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [hba]
    · simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

/-- A full-support tail of total weight `η` changes survival-fidelity deficit by at most `4η`,
uniformly over the entire real time axis. -/
theorem spectralReturnDeficit_anchorDopedWeights_le [NeZero D]
    (E : Fin D → ℝ) (a : Fin D) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (t : ℝ) :
    spectralReturnDeficit E (anchorDopedWeights a η) t ≤ 4 * η := by
  let z : ℂ := Complex.exp (((-(t * E a) : ℝ) : ℂ) * Complex.I)
  let U : ℂ := spectralReturnAmplitude E (fun _ => ((D : ℝ))⁻¹) t
  have huSum : ∑ _j : Fin D, ((D : ℝ))⁻¹ = 1 := by
    simp
  have hUnorm : ‖U‖ ≤ 1 := by
    apply norm_spectralReturnAmplitude_le_one (D := D) E (fun _ => ((D : ℝ))⁻¹)
    · intro j
      positivity
    · exact huSum
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hA : spectralReturnAmplitude E (anchorDopedWeights a η) t = (1 - η) * z + η * U := by
    simpa [z, U] using spectralReturnAmplitude_anchorDopedWeights E a η t
  have hAnorm : ‖spectralReturnAmplitude E (anchorDopedWeights a η) t‖ ≤ 1 := by
    apply norm_spectralReturnAmplitude_le_one (D := D) E (anchorDopedWeights a η)
    · exact fun j => (anchorDopedWeights_pos a j hη hη1).le
    · exact sum_anchorDopedWeights a η
  have hdiff : ‖spectralReturnAmplitude E (anchorDopedWeights a η) t - z‖ ≤ 2 * η := by
    rw [hA]
    have heq : (1 - η) * z + η * U - z = η * (U - z) := by
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη.le]
    calc
      η * ‖U - z‖ ≤ η * (‖U‖ + ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le U z) hη.le
      _ ≤ η * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add hUnorm hz.le) hη.le
      _ = 2 * η := by ring
  rw [spectralReturnDeficit]
  have hrev : 1 - ‖spectralReturnAmplitude E (anchorDopedWeights a η) t‖ ≤ 2 * η := by
    calc
      1 - ‖spectralReturnAmplitude E (anchorDopedWeights a η) t‖
          = ‖z‖ - ‖spectralReturnAmplitude E (anchorDopedWeights a η) t‖ := by rw [hz]
      _ ≤ ‖spectralReturnAmplitude E (anchorDopedWeights a η) t - z‖ := by
        simpa [norm_sub_rev] using norm_sub_norm_le z
          (spectralReturnAmplitude E (anchorDopedWeights a η) t)
      _ ≤ 2 * η := hdiff
  nlinarith [norm_nonneg (spectralReturnAmplitude E (anchorDopedWeights a η) t)]

/-- Above the tail scale, every time after the cutoff already lies in the return window. -/
theorem fidelityReturnTime_anchorDopedWeights_eq_cutoff [NeZero D]
    (E : Fin D → ℝ) (a : Fin D) {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hδ : 4 * η < δ) (t₀ : ℝ) :
    fidelityReturnTime E (anchorDopedWeights a η) t₀ δ = t₀ := by
  have hset : fidelityReturnSet E (anchorDopedWeights a η) t₀ δ = Set.Ici t₀ := by
    ext t
    simp only [fidelityReturnSet, Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · exact fun ht => ht.1
    · intro ht
      exact ⟨ht, lt_of_le_of_lt
        (spectralReturnDeficit_anchorDopedWeights_le E a hη hη1 t) hδ⟩
  rw [fidelityReturnTime, hset, csInf_Ici]

/-- At exact resolution, every positive full-support tail activates maximal first-return exponent. -/
theorem tendsto_log_fidelityReturnTime_anchorDopedWeights [NeZero D]
    (E : Fin D → ℝ) (hE : StrictMono E)
    (hgood : ∀ (S : Finset (Fin D)) (hS : 3 ≤ S.card),
      ¬ KleinbockMargulis.VWA (supportGapRatio E S hS))
    (a : Fin D) {η t₀ : ℝ} (hη : 0 < η) (hη1 : η < 1) (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log
          (fidelityReturnTime E (anchorDopedWeights a η) t₀ δ) /
        Real.log (1 / δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((D - 2 : ℕ) : ℝ) / 2)) := by
  have hmain := tendsto_log_fidelityReturnTime_supportCard E
    (anchorDopedWeights a η) (sum_anchorDopedWeights a η)
    (fun j => (anchorDopedWeights_pos a j hη hη1).le) hE hgood ht₀
  rw [spectralWeightSupport_anchorDopedWeights a hη hη1] at hmain
  simpa using hmain

/-! ## Pure-state realization -/

def spectralStateOfWeights (e : Fin D → Fin D → ℂ) (p : Fin D → ℝ) : Fin D → ℂ :=
  ∑ j, ((Real.sqrt (p j) : ℝ) : ℂ) • e j

theorem eigenCoords_spectralStateOfWeights {H : Matrix (Fin D) (Fin D) ℂ}
    {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ} (heb : IsOrthoEigenBasis H e E)
    (p : Fin D → ℝ) (j : Fin D) :
    eigenCoords e (spectralStateOfWeights e p) j = Real.sqrt (p j) := by
  exact eigenCoords_sum_smul heb (fun k => ((Real.sqrt (p k) : ℝ) : ℂ)) j

theorem spectralWeights_spectralStateOfWeights {H : Matrix (Fin D) (Fin D) ℂ}
    {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ} (heb : IsOrthoEigenBasis H e E)
    (p : Fin D → ℝ) (hpnn : ∀ j, 0 ≤ p j) :
    spectralWeights e (spectralStateOfWeights e p) = p := by
  funext j
  rw [spectralWeights, show finiteComplexInner (e j) (spectralStateOfWeights e p) =
      Real.sqrt (p j) from eigenCoords_spectralStateOfWeights heb p j]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hpnn j)]

theorem finiteComplexInner_spectralStateOfWeights_self {H : Matrix (Fin D) (Fin D) ℂ}
    {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ} (heb : IsOrthoEigenBasis H e E)
    (p : Fin D → ℝ) (hpnn : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) :
    finiteComplexInner (spectralStateOfWeights e p) (spectralStateOfWeights e p) = 1 := by
  rw [← finiteComplexInner_eigenCoords heb, finiteComplexInner]
  simp_rw [eigenCoords_spectralStateOfWeights heb p]
  calc
    ∑ j, (starRingEnd ℂ) (Real.sqrt (p j) : ℂ) * (Real.sqrt (p j) : ℂ)
        = ∑ j, (p j : ℂ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Complex.conj_ofReal]
          norm_cast
          simpa [pow_two] using Real.sq_sqrt (hpnn j)
    _ = ((∑ j, p j : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = 1 := by rw [hp1]; norm_num

theorem finitePureStateFidelity_eigen_spectralStateOfWeights
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (p : Fin D → ℝ) (hpnn : ∀ j, 0 ≤ p j)
    (a : Fin D) :
    finitePureStateFidelity (e a) (spectralStateOfWeights e p) = p a := by
  rw [finitePureStateFidelity,
    show finiteComplexInner (e a) (spectralStateOfWeights e p) = Real.sqrt (p a) from
      eigenCoords_spectralStateOfWeights heb p a]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hpnn a)]

theorem finitePureStateFidelity_anchorDopedState [NeZero D]
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (a : Fin D) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    1 - η ≤ finitePureStateFidelity (e a)
      (spectralStateOfWeights e (anchorDopedWeights a η)) := by
  rw [finitePureStateFidelity_eigen_spectralStateOfWeights heb
    (anchorDopedWeights a η) (fun j => (anchorDopedWeights_pos a j hη hη1).le) a]
  simp [anchorDopedWeights]
  positivity

theorem orbitFidelityReturnTime_spectralStateOfWeights_eq
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (p : Fin D → ℝ) (hpnn : ∀ j, 0 ≤ p j)
    (t₀ δ : ℝ) :
    orbitFidelityReturnTime H (spectralStateOfWeights e p) t₀ δ =
      fidelityReturnTime E p t₀ δ := by
  have h := orbitFidelityReturnTime_eq (Equiv.refl (Fin D)) heb
    (spectralStateOfWeights e p) t₀ δ
  rw [spectralWeights_spectralStateOfWeights heb p hpnn] at h
  simpa using h

theorem orbitFidelityDeficit_anchorDopedState_le [NeZero D]
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (a : Fin D) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (t : ℝ) :
    1 - ‖finiteComplexInner (spectralStateOfWeights e (anchorDopedWeights a η))
        (unitaryEvolution H t *ᵥ spectralStateOfWeights e (anchorDopedWeights a η))‖ ^ (2 : ℕ)
      ≤ 4 * η := by
  have hbridge := spectralReturnDeficit_eq_orbit_deficit (Equiv.refl (Fin D)) heb
    (spectralStateOfWeights e (anchorDopedWeights a η)) t
  rw [spectralWeights_spectralStateOfWeights heb (anchorDopedWeights a η)
    (fun j => (anchorDopedWeights_pos a j hη hη1).le)] at hbridge
  rw [← hbridge]
  exact spectralReturnDeficit_anchorDopedWeights_le E a hη hη1 t

theorem orbitFidelityReturnTime_anchorDopedState_eq_cutoff [NeZero D]
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (a : Fin D) {η δ : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hδ : 4 * η < δ) (t₀ : ℝ) :
    orbitFidelityReturnTime H (spectralStateOfWeights e (anchorDopedWeights a η)) t₀ δ = t₀ := by
  rw [orbitFidelityReturnTime_spectralStateOfWeights_eq heb
    (anchorDopedWeights a η) (fun j => (anchorDopedWeights_pos a j hη hη1).le)]
  exact fidelityReturnTime_anchorDopedWeights_eq_cutoff E a hη hη1 hδ t₀

theorem tendsto_log_orbitFidelityReturnTime_anchorDopedState [NeZero D]
    {H : Matrix (Fin D) (Fin D) ℂ} {e : Fin D → Fin D → ℂ} {E : Fin D → ℝ}
    (heb : IsOrthoEigenBasis H e E) (hE : StrictMono E)
    (hgood : ∀ (S : Finset (Fin D)) (hS : 3 ≤ S.card),
      ¬ KleinbockMargulis.VWA (supportGapRatio E S hS))
    (a : Fin D) {η t₀ : ℝ} (hη : 0 < η) (hη1 : η < 1) (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log
          (orbitFidelityReturnTime H
            (spectralStateOfWeights e (anchorDopedWeights a η)) t₀ δ) /
        Real.log (1 / δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((D - 2 : ℕ) : ℝ) / 2)) := by
  have hmain := tendsto_log_fidelityReturnTime_anchorDopedWeights E hE hgood a hη hη1 ht₀
  refine hmain.congr' ?_
  filter_upwards with δ
  rw [orbitFidelityReturnTime_spectralStateOfWeights_eq heb
    (anchorDopedWeights a η) (fun j => (anchorDopedWeights_pos a j hη hη1).le)]

variable {N : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem sortedStateSpectralWeights_eq_sortedEigenBasis
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) (Ω : Fin D → ℂ) :
    sortedStateSpectralWeights hP θ Ω = spectralWeights (sortedEigenBasis hP θ) Ω := by
  rfl

/-- Almost every Hamiltonian on one simple-spectrum chart exhibits the full preparation
instability simultaneously for every anchor and every positive tail weight. -/
theorem ae_vanishingTailPreparationInstability_sortedSpectrum [NeZero N] [NeZero D]
    (hP : ∀ a, (P a).IsHermitian)
    (hEsc : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ θ, θ ∈ U →
      ∀ (a : Fin D) (η : ℝ), 0 < η → η < 1 →
        let e := sortedEigenBasis hP θ
        let p := anchorDopedWeights a η
        let Ω := spectralStateOfWeights e p
        finiteComplexInner Ω Ω = 1 ∧
        1 - η ≤ finitePureStateFidelity (e a) Ω ∧
        (∀ t : ℝ,
          1 - ‖finiteComplexInner Ω
            (unitaryEvolution (spectralEnsembleMatrix P θ) t *ᵥ Ω)‖ ^ (2 : ℕ) ≤ 4 * η) ∧
        (∀ (t₀ δ : ℝ), 4 * η < δ →
          orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ = t₀) ∧
        (∀ {t₀ : ℝ}, 0 < t₀ →
          Tendsto
            (fun δ : ℝ => Real.log
                (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
              Real.log (1 / δ))
            (𝓝[>] (0 : ℝ))
            (𝓝 (((D - 2 : ℕ) : ℝ) / 2))) := by
  have hall := ae_tendsto_log_orbitFidelityReturnTime_supportCard_sortedSpectrum
    hP hEsc hU hUc hUne hUsimple
  filter_upwards [hall] with θ hθ hθU
  intro a η hη hη1
  let e := sortedEigenBasis hP θ
  let p := anchorDopedWeights a η
  let Ω := spectralStateOfWeights e p
  let heb : IsOrthoEigenBasis (spectralEnsembleMatrix P θ) e (spectralTuple hP θ) :=
    isOrthoEigenBasis_sortedEigenBasis hP θ
  have hpnn : ∀ j, 0 ≤ p j := fun j => (anchorDopedWeights_pos a j hη hη1).le
  have hΩ : finiteComplexInner Ω Ω = 1 :=
    finiteComplexInner_spectralStateOfWeights_self heb p hpnn (sum_anchorDopedWeights a η)
  refine ⟨hΩ, finitePureStateFidelity_anchorDopedState heb a hη hη1, ?_, ?_, ?_⟩
  · intro t
    exact orbitFidelityDeficit_anchorDopedState_le heb a hη hη1 t
  · intro t₀ δ hδ
    exact orbitFidelityReturnTime_anchorDopedState_eq_cutoff heb a hη hη1 hδ t₀
  · intro t₀ ht₀
    have hmain := hθ hθU Ω hΩ ht₀
    have hp : sortedStateSpectralWeights hP θ Ω = p := by
      rw [sortedStateSpectralWeights_eq_sortedEigenBasis]
      exact spectralWeights_spectralStateOfWeights heb p hpnn
    rw [hp, spectralWeightSupport_anchorDopedWeights a hη hη1] at hmain
    simpa using hmain

/-- One spectral ensemble obeys horizon-free vanishing-tail preparation instability on a chart. -/
def VanishingTailPreparationInstabilityOnChart [NeZero D]
    (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (hP : ∀ a, (P a).IsHermitian)
    (U : Set (Fin N → ℝ)) : Prop :=
  ∀ᵐ θ, θ ∈ U →
    ∀ (a : Fin D) (η : ℝ), 0 < η → η < 1 →
      let e := sortedEigenBasis hP θ
      let p := anchorDopedWeights a η
      let Ω := spectralStateOfWeights e p
      finiteComplexInner Ω Ω = 1 ∧
      1 - η ≤ finitePureStateFidelity (e a) Ω ∧
      (∀ t : ℝ,
        1 - ‖finiteComplexInner Ω
          (unitaryEvolution (spectralEnsembleMatrix P θ) t *ᵥ Ω)‖ ^ (2 : ℕ) ≤ 4 * η) ∧
      (∀ (t₀ δ : ℝ), 4 * η < δ →
        orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ = t₀) ∧
      (∀ {t₀ : ℝ}, 0 < t₀ →
        Tendsto
          (fun δ : ℝ => Real.log
              (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
            Real.log (1 / δ))
          (𝓝[>] (0 : ℝ))
          (𝓝 (((D - 2 : ℕ) : ℝ) / 2)))

theorem vanishingTailPreparationInstabilityOnChart_of_spectrumEscapes
    [NeZero N] [NeZero D]
    (hP : ∀ a, (P a).IsHermitian)
    (hEsc : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    VanishingTailPreparationInstabilityOnChart P hP U :=
  ae_vanishingTailPreparationInstability_sortedSpectrum hP hEsc hU hUc hUne hUsimple

/-- Exact local-family packaging of the vanishing-tail preparation-instability law. -/
def QuditPathVanishingTailPreparationInstabilityLaw (n q : ℕ) : Prop :=
    ∃ e : ℕ, q ^ n = e + 3 ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin (e + 3))
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ)
        (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        (∃ U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
          IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP) ∧
        ∀ {U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ)},
          IsOpen U → IsPreconnected U → U.Nonempty →
          U ⊆ simpleEnsembleLocus hP →
          VanishingTailPreparationInstabilityOnChart P hP U

theorem quditPathVanishingTailPreparationInstabilityLaw_of_two_le
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    QuditPathVanishingTailPreparationInstabilityLaw n q := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily n q hn hq
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 3 := ⟨D - 3, by omega⟩
  letI := instP
  letI := instPd
  haveI := hNeZero
  refine ⟨e, hD, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hPHermitian, hprov,
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily, ?_⟩
  intro U hUopen hUconn hUne hUsimple
  exact vanishingTailPreparationInstabilityOnChart_of_spectrumEscapes
    hPHermitian hfamily.toRealRelations hUopen hUconn hUne hUsimple

/-- **Unconditional local-many-body capstone.** Every shifted path admits a full static local
coefficient family on whose every simple chart almost every Hamiltonian exhibits horizon-free
vanishing-tail activation of maximal unmeasured first-return exponent. -/
theorem universalQuditPathVanishingTailPreparationInstabilityLaw (n q : ℕ) :
    QuditPathVanishingTailPreparationInstabilityLaw (n + 2) (q + 2) :=
  quditPathVanishingTailPreparationInstabilityLaw_of_two_le
    (n + 2) (q + 2) (by omega) (by omega)

end
end GaloisForLFunctions.HTGeometry
