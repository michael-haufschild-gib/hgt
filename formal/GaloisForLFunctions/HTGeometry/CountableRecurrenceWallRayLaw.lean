import GaloisForLFunctions.HTGeometry.CountableProjectiveFutureUniversalityLaw
import GaloisForLFunctions.HTGeometry.ProjectiveRecurrenceProtectionLaw
import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageCharacterLaw

/-!
# Countable recurrence-wall rays

Every finitely supported balanced integer character defines an affine
recurrence wall in spectral-energy space.  Along a projectively free
direction, each nontrivial wall is crossed at most once.  For countable
spectra the complete exceptional coupling set is therefore countable.

An arbitrarily weak summable direction can be chosen projectively free.  At
every nonexceptional coupling strength the resulting unbounded diagonal
Hamiltonian keeps its maximal domain, has every finite temporal rank, has
dense forward tails in the full projective product torus, and has no nonzero
exact global return.  Finite-window histories nevertheless vary continuously
across every wall with a dimension-independent operator-norm bound.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set
open NormedSpace

/-- Coupling strengths at which an affine spectral ray carries a nonzero
finitely supported projective relation. -/
def projectiveCouplingExceptionalSet
    {I : Type*} (energy direction : I → ℝ) : Set ℝ :=
  {g | ¬ FinitelySupportedMaximallyProjectiveEnergy
    (fun i => energy i + g * direction i)}

theorem projectiveCharacterDetuning_affine
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (g : ℝ) :
    projectiveCharacterDetuning k
        (fun i => energy i + g * direction i) =
      projectiveCharacterDetuning k energy +
        g * projectiveCharacterDetuning k direction := by
  unfold projectiveCharacterDetuning
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A transverse character crosses its recurrence wall at one explicit
coupling strength. -/
theorem projectiveCharacter_on_affineWall_iff
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (g : ℝ)
    (htransverse : projectiveCharacterDetuning k direction ≠ 0) :
    projectiveCharacterDetuning k
        (fun i => energy i + g * direction i) = 0 ↔
      g = -projectiveCharacterDetuning k energy /
        projectiveCharacterDetuning k direction := by
  rw [projectiveCharacterDetuning_affine,
    eq_div_iff htransverse]
  constructor <;> intro h <;> linarith

/-- At every nonzero strength, an existing recurrence relation survives
exactly when the chosen direction is tangent to its wall. -/
theorem projectiveCharacter_relation_survives_nonzeroCoupling_iff
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (g : ℝ)
    (hbase : projectiveCharacterDetuning k energy = 0)
    (hg : g ≠ 0) :
    projectiveCharacterDetuning k
        (fun i => energy i + g * direction i) = 0 ↔
      projectiveCharacterDetuning k direction = 0 := by
  rw [projectiveCharacterDetuning_affine, hbase, zero_add]
  exact mul_eq_zero.trans (or_iff_right hg)

/-- Symmetric finite-time reporter of one recurrence wall along an affine
coupling ray. -/
def recurrenceWallReporter
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T g : ℝ) : ℂ :=
  symmetricPhaseAverage T
    (projectiveCharacterDetuning k
      (fun i => energy i + g * direction i))

/-- The finite-time wall reporter is exactly the sinc diffraction profile of
the affine character detuning. -/
theorem recurrenceWallReporter_eq_sinc
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T g : ℝ) (hT : T ≠ 0) :
    recurrenceWallReporter k energy direction T g =
      Real.sinc
        (T * (projectiveCharacterDetuning k energy +
          g * projectiveCharacterDetuning k direction)) := by
  rw [recurrenceWallReporter, symmetricPhaseAverage_eq_sinc _ _ hT,
    projectiveCharacterDetuning_affine]

/-- **Universal recurrence-wall spectroscopy law.** Around the unique
transverse wall crossing, every observation time and coupling offset collapse
exactly onto one scale-free sinc profile. The coupling width is therefore
proportional to the inverse observation time. -/
theorem recurrenceWallReporter_scaled_profile
    {I : Type*} (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T ξ : ℝ)
    (hT : T ≠ 0)
    (htransverse : projectiveCharacterDetuning k direction ≠ 0) :
    recurrenceWallReporter k energy direction T
        (-projectiveCharacterDetuning k energy /
            projectiveCharacterDetuning k direction + ξ / T) =
      Real.sinc (ξ * projectiveCharacterDetuning k direction) := by
  rw [recurrenceWallReporter_eq_sinc _ _ _ _ _ hT]
  congr 1
  field_simp [hT, htransverse]
  ring_nf

/-- A projectively free direction meets every nontrivial recurrence wall at
at most one coupling strength. Hence the exceptional strengths along the
entire ray are countable. -/
theorem projectiveCouplingExceptionalSet_countable
    {I : Type*} [Countable I]
    (energy direction : I → ℝ)
    (hdirection :
      FinitelySupportedMaximallyProjectiveEnergy direction) :
    (projectiveCouplingExceptionalSet energy direction).Countable := by
  let crossing : ProjectiveCharacter I → ℝ := fun k =>
    -projectiveCharacterDetuning k energy /
      projectiveCharacterDetuning k direction
  apply (Set.countable_range crossing).mono
  intro g hg
  change ¬ FinitelySupportedMaximallyProjectiveEnergy
      (fun i => energy i + g * direction i) at hg
  rw [FinitelySupportedMaximallyProjectiveEnergy] at hg
  push Not at hg
  obtain ⟨k, hzero, hk⟩ := hg
  have hdirectionNe : projectiveCharacterDetuning k direction ≠ 0 := by
    intro hkdir
    exact hk (hdirection k hkdir)
  refine ⟨k, ?_⟩
  have hzero' :
      projectiveCharacterDetuning k
          (fun i => energy i + g * direction i) = 0 := hzero
  rw [projectiveCharacterDetuning_affine] at hzero'
  dsimp [crossing]
  apply (div_eq_iff hdirectionNe).2
  linarith

/-- Every nondegenerate coupling interval contains a strength away from all
recurrence walls of a projectively free direction. -/
theorem exists_maximallyProjective_coupling_in_interval
    {I : Type*} [Countable I]
    (energy direction : I → ℝ)
    (hdirection :
      FinitelySupportedMaximallyProjectiveEnergy direction)
    {a b : ℝ} (hab : a < b) :
    ∃ g ∈ Set.Ioo a b,
      FinitelySupportedMaximallyProjectiveEnergy
        (fun i => energy i + g * direction i) := by
  have hcount :=
    projectiveCouplingExceptionalSet_countable
      energy direction hdirection
  by_contra hnone
  push Not at hnone
  have hIcount : (Set.Ioo a b).Countable :=
    hcount.mono (fun g hg => hnone g hg)
  have hle : b ≤ a :=
    (Cardinal.Real.Ioo_countable_iff (x := a) (y := b)).mp hIcount
  exact not_le.mpr hab hle

/-- Finite-window histories vary continuously across every recurrence wall,
with a bound independent of window dimension. -/
theorem finiteWindowHeisenberg_affineDirection_norm_sub_le
    {I J : Type*} [Fintype J] [DecidableEq J]
    (energy direction : I → ℝ) (e : J ↪ I)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hpoint : ∀ i, |direction i| ≤ δ)
    (O : RHTower.FiniteIndexClockSpace J →L[ℂ]
      RHTower.FiniteIndexClockSpace J)
    (g t : ℝ) :
    ‖exp (t • ((-Complex.I) •
          RHTower.finiteIndexDiagonalHamiltonian
            ((fun i => energy i + g * direction i) ∘ e))) * O *
          star (exp (t • ((-Complex.I) •
            RHTower.finiteIndexDiagonalHamiltonian
              ((fun i => energy i + g * direction i) ∘ e)))) -
        exp (t • ((-Complex.I) •
          RHTower.finiteIndexDiagonalHamiltonian (energy ∘ e))) * O *
          star (exp (t • ((-Complex.I) •
            RHTower.finiteIndexDiagonalHamiltonian
              (energy ∘ e))))‖
      ≤ 2 * |t| * (|g| * δ) * ‖O‖ := by
  let before : J → ℝ := energy ∘ e
  let after : J → ℝ :=
    (fun i => energy i + g * direction i) ∘ e
  have hwindowNorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian after -
          RHTower.finiteIndexDiagonalHamiltonian before‖ ≤ |g| * δ := by
    apply finiteIndexDiagonalHamiltonian_norm_sub_le
      after before (|g| * δ) (mul_nonneg (abs_nonneg g) hδ)
    intro j
    simp only [after, before, Function.comp_apply, add_sub_cancel_left]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hpoint (e j)) (abs_nonneg g)
  calc
    _ ≤ 2 * |t| *
          ‖RHTower.finiteIndexDiagonalHamiltonian after -
            RHTower.finiteIndexDiagonalHamiltonian before‖ * ‖O‖ :=
      selfAdjoint_heisenbergEvolution_norm_sub_le
        (RHTower.finiteIndexDiagonalHamiltonian after)
        (RHTower.finiteIndexDiagonalHamiltonian before) O
        (finiteIndexDiagonalHamiltonian_isSelfAdjoint after)
        (finiteIndexDiagonalHamiltonian_isSelfAdjoint before) t
    _ ≤ 2 * |t| * (|g| * δ) * ‖O‖ := by gcongr

/-- **Countable recurrence-wall ray law.** Every countably infinite
pure-point Hamiltonian admits an arbitrarily weak self-adjoint trace-class
direction such that the entire affine coupling ray has only countably many
exceptional strengths. At every other strength, the maximal domain is
unchanged, every finite temporal rank occurs, every future tail is dense in
the full projective product torus, and zero is the only exact global return
time. -/
theorem exists_arbitrarilyWeak_countableRecurrenceWallRay
    {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|), ∃ C : Set ℝ,
      (∀ i, |w i| < δ) ∧
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      IsSelfAdjoint (realSummableDiagonalOperator w hw) ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      C.Countable ∧
      (∀ a b : ℝ, a < b →
        ∃ g ∈ Set.Ioo a b, g ∉ C) ∧
      ∀ g ∉ C,
        RHTower.maximalRealDiagonalDomain
            (fun i => energy i + g * w i) =
          RHTower.maximalRealDiagonalDomain energy ∧
        IsSelfAdjoint
          (RHTower.maximalRealDiagonal
            (fun i => energy i + g * w i)) ∧
        FinitelySupportedMaximallyProjectiveEnergy
          (fun i => energy i + g * w i) ∧
        (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ I,
          projectiveTemporalRank
            ((fun i => energy i + g * w i) ∘ e) = n) ∧
        ∀ anchor : I,
          (∀ T : ℝ,
            closure
                (screwPhase
                  (anchoredProjectiveGap
                    (fun i => energy i + g * w i) anchor) '' Set.Ici T) =
              Set.univ) ∧
          ∀ t : ℝ,
            screwPhase
                (anchoredProjectiveGap
                  (fun i => energy i + g * w i) anchor) t = 0 →
              t = 0 := by
  classical
  obtain ⟨w, hw, hpoint, hnorm, hself, htrace,
      hdomain, hHamiltonian, hmaxZero⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      (fun _ : I => 0) δ hδ
  have hmaxDirection :
      FinitelySupportedMaximallyProjectiveEnergy w := by
    simpa using hmaxZero
  let C : Set ℝ := projectiveCouplingExceptionalSet energy w
  have hC : C.Countable :=
    projectiveCouplingExceptionalSet_countable
      energy w hmaxDirection
  refine ⟨w, hw, C, hpoint, hnorm, hself, htrace, hC, ?_, ?_⟩
  · intro a b hab
    obtain ⟨g, hgI, hgmax⟩ :=
      exists_maximallyProjective_coupling_in_interval
        energy w hmaxDirection hab
    refine ⟨g, hgI, ?_⟩
    simpa [C, projectiveCouplingExceptionalSet] using hgmax
  · intro g hg
    have hmaxg :
        FinitelySupportedMaximallyProjectiveEnergy
          (fun i => energy i + g * w i) := by
      simpa [C, projectiveCouplingExceptionalSet] using hg
    have hwg : Summable (fun i => |g * w i|) := by
      simpa [abs_mul] using hw.mul_left |g|
    refine ⟨maximalRealDiagonalDomain_add_summable_eq
        energy (fun i => g * w i) hwg,
      RHTower.maximalRealDiagonal_isSelfAdjoint _, hmaxg,
      hmaxg.unboundedFiniteWindowTemporalRank, ?_⟩
    intro anchor
    refine ⟨?_, hmaxg.no_nonzeroExactProjectiveReturn anchor⟩
    intro T
    exact
      closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
        (fun i => energy i + g * w i) anchor hmaxg T

end

end GaloisForLFunctions.HTGeometry
