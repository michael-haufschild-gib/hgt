import GaloisForLFunctions.RHTower.CyclicHilbertQuantumRecurrenceNoGoLaw
import GaloisForLFunctions.HTGeometry.ProbabilityMeasureSimplex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Nonperturbative quantum recurrence separation law

This file removes the heavy-tail limitation of moment-indeterminate recurrence
witnesses.  It constructs two smooth coupling families of probability spectra,
all supported in the fixed positive compact interval `[1, 2]`.

The complete coupling jet at zero of the full time-dependent survival form
factor is identical for the two families.  Nevertheless, at every positive
coupling the first family has a positive asymptotic mean return plateau, while
the second has plateau zero.  Thus no classifier fed the all-orders
perturbative spectral form factor can decide recurrence, even on uniformly
compact positive-energy cyclic Hilbert-space clocks.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace RHTower

theorem integrable_charFunKernel
    (mu : Measure ℝ) [IsFiniteMeasure mu] (t : ℝ) :
    Integrable
      (fun x : ℝ =>
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) mu := by
  refine Integrable.of_bound
    ((by fun_prop :
      Continuous
        (fun x : ℝ =>
          Complex.exp
            ((t : ℂ) * (x : ℂ) * Complex.I))).aestronglyMeasurable)
    1 ?_
  filter_upwards with x
  rw [Complex.norm_exp]
  simp

theorem charFun_probabilityMixture
    (u : ℝ≥0∞) (hu : u ≤ 1)
    (mu nu : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun
        (GaloisForLFunctions.HTGeometry.probabilityMixture
          u hu mu nu : Measure ℝ) t =
      u.toReal • charFun (mu : Measure ℝ) t +
        (1 - u).toReal • charFun (nu : Measure ℝ) t := by
  rw [charFun_apply_real,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp only [← charFun_apply_real]
  · exact
      (integrable_charFunKernel (mu : Measure ℝ) t).smul_measure
        (ne_of_lt (hu.trans_lt ENNReal.one_lt_top))
  · exact
      (integrable_charFunKernel (nu : Measure ℝ) t).smul_measure
        (ne_of_lt ((tsub_le_self : 1 - u ≤ 1).trans_lt
          ENNReal.one_lt_top))

/-- Atomless continuum spectrum, uniformly distributed on `[1, 2]`. -/
def compactPositiveContinuumSpectrum : ProbabilityMeasure ℝ := by
  refine ⟨volume.restrict (Icc (1 : ℝ) 2), ?_⟩
  rw [isProbabilityMeasure_iff, Measure.restrict_apply_univ,
    Real.volume_Icc]
  norm_num

/-- One positive-energy atom in the interior of `[1, 2]`. -/
def compactPositiveAtomSpectrum : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac (3 / 2 : ℝ),
    Measure.dirac.isProbabilityMeasure⟩

instance compactPositiveContinuumSpectrum_noAtoms :
    NoAtoms (compactPositiveContinuumSpectrum : Measure ℝ) := by
  change NoAtoms (volume.restrict (Icc (1 : ℝ) 2))
  infer_instance

/-- Smooth nonperturbative coupling weight.  It is zero to all orders at
`g = 0`, equals `exp (-1 / g)` for every `g > 0`, and lies in `[0, 1)`. -/
def nonperturbativeCouplingWeight (g : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (expNegInvGlue g)

theorem expNegInvGlue_lt_one (g : ℝ) :
    expNegInvGlue g < 1 := by
  by_cases hg : g ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hg]
    norm_num
  · rw [expNegInvGlue, if_neg hg, Real.exp_lt_one_iff]
    have hinv : 0 < g⁻¹ :=
      inv_pos.mpr (lt_of_not_ge hg)
    linarith

theorem nonperturbativeCouplingWeight_le_one (g : ℝ) :
    nonperturbativeCouplingWeight g ≤ 1 := by
  rw [nonperturbativeCouplingWeight, ENNReal.ofReal_le_one]
  exact (expNegInvGlue_lt_one g).le

theorem nonperturbativeCouplingWeight_lt_one (g : ℝ) :
    nonperturbativeCouplingWeight g < 1 := by
  rw [nonperturbativeCouplingWeight, ENNReal.ofReal_lt_one]
  exact expNegInvGlue_lt_one g

theorem nonperturbativeCouplingWeight_pos {g : ℝ} (hg : 0 < g) :
    0 < nonperturbativeCouplingWeight g := by
  rw [nonperturbativeCouplingWeight, ENNReal.ofReal_pos]
  exact expNegInvGlue.pos_of_pos hg

/-- Flat coupling of an arbitrary exact spectral completion to an arbitrary
base spectrum. -/
def nonperturbativeSpectralCompletion
    (completion base : ProbabilityMeasure ℝ) (g : ℝ) :
    ProbabilityMeasure ℝ :=
  GaloisForLFunctions.HTGeometry.probabilityMixture
    (nonperturbativeCouplingWeight g)
    (nonperturbativeCouplingWeight_le_one g)
    completion
    base

/-- Canonical nonperturbative atomic completion of an arbitrary probability
spectrum at an arbitrary energy. -/
def nonperturbativeAtomicCompletion
    (base : ProbabilityMeasure ℝ) (energy g : ℝ) :
    ProbabilityMeasure ℝ :=
  GaloisForLFunctions.HTGeometry.probabilityMixture
    (nonperturbativeCouplingWeight g)
    (nonperturbativeCouplingWeight_le_one g)
    ⟨Measure.dirac energy,
      Measure.dirac.isProbabilityMeasure⟩
    base

/-- Perturbatively identical comparison family with no completion. -/
def constantSpectrumFamily
    (base : ProbabilityMeasure ℝ) (_g : ℝ) :
    ProbabilityMeasure ℝ :=
  base

/-- Compact positive-energy family with a nonperturbatively small atom. -/
def recurrentCompactSpectrumFamily (g : ℝ) : ProbabilityMeasure ℝ :=
  GaloisForLFunctions.HTGeometry.probabilityMixture
    (nonperturbativeCouplingWeight g)
    (nonperturbativeCouplingWeight_le_one g)
    compactPositiveAtomSpectrum
    compactPositiveContinuumSpectrum

/-- Constant atomless comparison family. -/
def dispersiveCompactSpectrumFamily (_g : ℝ) : ProbabilityMeasure ℝ :=
  compactPositiveContinuumSpectrum

theorem recurrentCompactSpectrumFamily_singleton_atom (g : ℝ) :
    (recurrentCompactSpectrumFamily g : Measure ℝ)
        {(3 / 2 : ℝ)} =
      nonperturbativeCouplingWeight g := by
  rw [recurrentCompactSpectrumFamily,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [compactPositiveAtomSpectrum,
    compactPositiveContinuumSpectrum]

theorem recurrentCompactSpectrumFamily_singleton_formula
    (g x : ℝ) :
    (recurrentCompactSpectrumFamily g : Measure ℝ) {x} =
      if x = (3 / 2 : ℝ) then
        nonperturbativeCouplingWeight g else 0 := by
  rw [recurrentCompactSpectrumFamily,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  by_cases hx : x = (3 / 2 : ℝ)
  · subst x
    simp [compactPositiveAtomSpectrum,
      compactPositiveContinuumSpectrum]
  · have hcont :
        (compactPositiveContinuumSpectrum : Measure ℝ) {x} = 0 :=
      measure_singleton x
    rw [hcont]
    simp [compactPositiveAtomSpectrum, hx]

/-- Collision mass of a probability spectrum with exactly one atom. -/
theorem spectralDifferenceMeasure_singleton_zero_of_uniqueAtom
    (mu : ProbabilityMeasure ℝ) (a : ℝ) (m : ℝ≥0∞)
    (hatom : ∀ x : ℝ,
      (mu : Measure ℝ) {x} = if x = a then m else 0) :
    spectralDifferenceMeasure (mu : Measure ℝ) {0} = m * m := by
  rw [spectralDifferenceMeasure_singleton_zero,
    Measure.prod_apply measurableSet_diagonal]
  have hfiber (x : ℝ) :
      Prod.mk x ⁻¹' diagonal ℝ = {x} := by
    ext y
    simp [eq_comm]
  simp_rw [hfiber, hatom]
  rw [show (fun x : ℝ => if x = a then m else 0) =
      Set.indicator ({a} : Set ℝ) (fun _ : ℝ => m) by
    funext x
    by_cases hx : x = a
    · subst x
      simp
    · simp [hx]]
  rw [lintegral_indicator (measurableSet_singleton a)]
  simp [hatom]

/-- Adding the flat atomic completion to any atomless base spectrum creates
exactly one atom, at the selected energy. -/
theorem nonperturbativeAtomicCompletion_singleton_formula
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy g x : ℝ) :
    (nonperturbativeAtomicCompletion base energy g : Measure ℝ) {x} =
      if x = energy then nonperturbativeCouplingWeight g else 0 := by
  rw [nonperturbativeAtomicCompletion,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  by_cases hx : x = energy
  · subst x
    simp
  · have hbase : (base : Measure ℝ) {x} = 0 :=
      measure_singleton x
    rw [hbase]
    simp [hx]

/-- For every atomless base spectrum and every selected energy, the exact
return plateau of its nonperturbative completion is universal: it is the
square of the flat coupling weight and is independent of the base spectrum. -/
theorem nonperturbativeAtomicCompletion_plateau_exact
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy g : ℝ) :
    recurrencePlateau
        (nonperturbativeAtomicCompletion base energy g : Measure ℝ) =
      (expNegInvGlue g) ^ 2 := by
  rw [recurrencePlateau, Measure.real,
    spectralDifferenceMeasure_singleton_zero_of_uniqueAtom
      (nonperturbativeAtomicCompletion base energy g)
      energy (nonperturbativeCouplingWeight g)
      (nonperturbativeAtomicCompletion_singleton_formula
        base energy g)]
  rw [ENNReal.toReal_mul]
  simp [nonperturbativeCouplingWeight,
    expNegInvGlue.nonneg g, pow_two]

/-- At every positive coupling the exact return plateau has the instanton
scale `exp (-2 / g)`. -/
theorem nonperturbativeAtomicCompletion_plateau_instanton_exact
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy : ℝ)
    {g : ℝ} (hg : 0 < g) :
    recurrencePlateau
        (nonperturbativeAtomicCompletion base energy g : Measure ℝ) =
      Real.exp (-2 / g) := by
  rw [nonperturbativeAtomicCompletion_plateau_exact,
    expNegInvGlue, if_neg (not_le_of_gt hg), pow_two,
    ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem nonperturbativeAtomicCompletion_plateau_pos
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy : ℝ)
    {g : ℝ} (hg : 0 < g) :
    HasPersistentMeanRecurrence
      (nonperturbativeAtomicCompletion base energy g : Measure ℝ) := by
  rw [HasPersistentMeanRecurrence,
    nonperturbativeAtomicCompletion_plateau_exact]
  exact sq_pos_of_pos (expNegInvGlue.pos_of_pos hg)

theorem constantSpectrumFamily_plateau_zero
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (g : ℝ) :
    recurrencePlateau
        (constantSpectrumFamily base g : Measure ℝ) = 0 := by
  rw [constantSpectrumFamily, recurrencePlateau, Measure.real,
    spectralDifferenceMeasure_singleton_zero_of_noAtoms]
  simp

/-- The completion preserves every measurable support set that already
contains the selected energy. -/
theorem nonperturbativeAtomicCompletion_carried
    (base : ProbabilityMeasure ℝ) (energy g : ℝ)
    {K : Set ℝ} (hK : MeasurableSet K)
    (hbase : (base : Measure ℝ) Kᶜ = 0)
    (henergy : energy ∈ K) :
    (nonperturbativeAtomicCompletion base energy g : Measure ℝ) Kᶜ = 0 := by
  rw [nonperturbativeAtomicCompletion,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [Measure.dirac_apply' energy hK.compl, hbase, henergy]

theorem recurrentCompactSpectrumFamily_not_noAtoms
    {g : ℝ} (hg : 0 < g) :
    ¬ NoAtoms (recurrentCompactSpectrumFamily g : Measure ℝ) := by
  intro hno
  letI : NoAtoms (recurrentCompactSpectrumFamily g : Measure ℝ) :=
    hno
  have hzero :
      (recurrentCompactSpectrumFamily g : Measure ℝ)
          {(3 / 2 : ℝ)} = 0 :=
    measure_singleton _
  rw [recurrentCompactSpectrumFamily_singleton_atom] at hzero
  exact (nonperturbativeCouplingWeight_pos hg).ne' hzero

theorem recurrentCompactSpectrumFamily_plateau_pos
    {g : ℝ} (hg : 0 < g) :
    HasPersistentMeanRecurrence
      (recurrentCompactSpectrumFamily g : Measure ℝ) := by
  have hne :
      spectralDifferenceMeasure
          (recurrentCompactSpectrumFamily g : Measure ℝ) {0} ≠ 0 := by
    intro hzero
    exact recurrentCompactSpectrumFamily_not_noAtoms hg
      ((spectralDifferenceMeasure_singleton_zero_iff_noAtoms
        (recurrentCompactSpectrumFamily g : Measure ℝ)).mp hzero)
  rw [HasPersistentMeanRecurrence, recurrencePlateau, Measure.real]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

theorem dispersiveCompactSpectrumFamily_plateau_zero (g : ℝ) :
    recurrencePlateau
        (dispersiveCompactSpectrumFamily g : Measure ℝ) = 0 := by
  rw [dispersiveCompactSpectrumFamily, recurrencePlateau, Measure.real,
    spectralDifferenceMeasure_singleton_zero_of_noAtoms]
  simp

/-- Exact nonperturbative plateau: it is the square of the flat coupling
weight, hence nonzero for every positive coupling but invisible at every
perturbative order at zero coupling. -/
theorem recurrentCompactSpectrumFamily_plateau_exact (g : ℝ) :
    recurrencePlateau
        (recurrentCompactSpectrumFamily g : Measure ℝ) =
      (expNegInvGlue g) ^ 2 := by
  rw [recurrencePlateau, Measure.real,
    spectralDifferenceMeasure_singleton_zero_of_uniqueAtom
      (recurrentCompactSpectrumFamily g)
      (3 / 2 : ℝ) (nonperturbativeCouplingWeight g)
      (recurrentCompactSpectrumFamily_singleton_formula g)]
  rw [ENNReal.toReal_mul]
  simp [nonperturbativeCouplingWeight,
    expNegInvGlue.nonneg g, pow_two]

/-- Both families are supported in the same fixed strictly positive compact
energy interval. -/
def IsUniformlyCompactPositiveSpectrumFamily
    (family : ℝ → ProbabilityMeasure ℝ) : Prop :=
  ∀ g : ℝ,
    (family g : Measure ℝ) (Icc (1 : ℝ) 2)ᶜ = 0

theorem recurrentCompactSpectrumFamily_uniformlyCompactPositive :
    IsUniformlyCompactPositiveSpectrumFamily
      recurrentCompactSpectrumFamily := by
  intro g
  have hpoint : (3 / 2 : ℝ) ∈ Icc 1 2 := by norm_num
  rw [recurrentCompactSpectrumFamily,
    GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [compactPositiveAtomSpectrum,
    compactPositiveContinuumSpectrum, Measure.restrict_apply,
    hpoint]

theorem dispersiveCompactSpectrumFamily_uniformlyCompactPositive :
    IsUniformlyCompactPositiveSpectrumFamily
      dispersiveCompactSpectrumFamily := by
  intro g
  simp [dispersiveCompactSpectrumFamily,
    compactPositiveContinuumSpectrum, Measure.restrict_apply]

theorem charFun_recurrentCompactSpectrumFamily (g t : ℝ) :
    charFun (recurrentCompactSpectrumFamily g : Measure ℝ) t =
      expNegInvGlue g •
          charFun (compactPositiveAtomSpectrum : Measure ℝ) t +
        (1 - expNegInvGlue g) •
          charFun
            (compactPositiveContinuumSpectrum : Measure ℝ) t := by
  rw [recurrentCompactSpectrumFamily, charFun_probabilityMixture]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

theorem charFun_nonperturbativeSpectralCompletion
    (completion base : ProbabilityMeasure ℝ) (g t : ℝ) :
    charFun
        (nonperturbativeSpectralCompletion
          completion base g : Measure ℝ) t =
      expNegInvGlue g •
          charFun (completion : Measure ℝ) t +
        (1 - expNegInvGlue g) •
          charFun (base : Measure ℝ) t := by
  rw [nonperturbativeSpectralCompletion,
    charFun_probabilityMixture]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

theorem charFun_nonperturbativeAtomicCompletion
    (base : ProbabilityMeasure ℝ) (energy g t : ℝ) :
    charFun
        (nonperturbativeAtomicCompletion base energy g : Measure ℝ) t =
      expNegInvGlue g •
          charFun (Measure.dirac energy) t +
        (1 - expNegInvGlue g) •
          charFun (base : Measure ℝ) t := by
  rw [nonperturbativeAtomicCompletion, charFun_probabilityMixture]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

/-- The smooth transition is invisible to every perturbative order at the
zero-coupling boundary. -/
theorem iteratedDeriv_expNegInvGlue_zero (n : ℕ) :
    iteratedDeriv n expNegInvGlue 0 = 0 := by
  have hud : UniqueDiffOn ℝ (Iic (0 : ℝ)) :=
    uniqueDiffOn_Iic 0
  have hcd : ContDiffAt ℝ n expNegInvGlue 0 :=
    expNegInvGlue.contDiff.contDiffAt
  rw [← iteratedDerivWithin_eq_iteratedDeriv hud hcd
    (mem_Iic.mpr le_rfl)]
  have heq :
      Set.EqOn expNegInvGlue
        (fun _ : ℝ => 0) (Iic 0) :=
    fun x hx => expNegInvGlue.zero_of_nonpos hx
  rw [iteratedDerivWithin_congr heq (mem_Iic.mpr le_rfl)]
  simp

/-- The exact recurrence plateau itself is flat to every perturbative order
at zero coupling. -/
theorem recurrentCompactSpectrumFamily_plateau_flat (n : ℕ) :
    iteratedDeriv n
        (fun g =>
          recurrencePlateau
            (recurrentCompactSpectrumFamily g : Measure ℝ)) 0 = 0 := by
  have hfun :
      (fun g =>
        recurrencePlateau
          (recurrentCompactSpectrumFamily g : Measure ℝ)) =
        fun g => expNegInvGlue g *
          expNegInvGlue g := by
    funext g
    rw [recurrentCompactSpectrumFamily_plateau_exact, pow_two]
  rw [hfun]
  change iteratedDeriv n
    (expNegInvGlue * expNegInvGlue) 0 = 0
  rw [iteratedDeriv_mul
    expNegInvGlue.contDiff.contDiffAt
    expNegInvGlue.contDiff.contDiffAt]
  apply Finset.sum_eq_zero
  intro k hk
  rw [iteratedDeriv_expNegInvGlue_zero,
    iteratedDeriv_expNegInvGlue_zero]
  simp

/-- Every exact spectral completion is invisible in every coupling
coefficient of the full survival amplitude, at every physical time. -/
theorem charFun_nonperturbativeSpectralCompletion_flat
    (completion base : ProbabilityMeasure ℝ)
    (n : ℕ) (t : ℝ) :
    iteratedDeriv n
        (fun g =>
          charFun
            (nonperturbativeSpectralCompletion
              completion base g : Measure ℝ) t) 0 =
      iteratedDeriv n
        (fun _ : ℝ => charFun (base : Measure ℝ) t) 0 := by
  have hfun :
      (fun g =>
        charFun
          (nonperturbativeSpectralCompletion
            completion base g : Measure ℝ) t) =
        fun g =>
          charFun (base : Measure ℝ) t +
            expNegInvGlue g •
              (charFun (completion : Measure ℝ) t -
                charFun (base : Measure ℝ) t) := by
    funext g
    rw [charFun_nonperturbativeSpectralCompletion]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

/-- For every base spectrum, selected energy, perturbative order, and
physical time, the atomic completion has the same coupling coefficient as
the uncompleted spectrum. -/
theorem charFun_nonperturbativeAtomicCompletion_flat
    (base : ProbabilityMeasure ℝ) (energy : ℝ)
    (n : ℕ) (t : ℝ) :
    iteratedDeriv n
        (fun g =>
          charFun
            (nonperturbativeAtomicCompletion
              base energy g : Measure ℝ) t) 0 =
      iteratedDeriv n
        (fun _ : ℝ => charFun (base : Measure ℝ) t) 0 := by
  have hfun :
      (fun g =>
        charFun
          (nonperturbativeAtomicCompletion
            base energy g : Measure ℝ) t) =
        fun g =>
          charFun (base : Measure ℝ) t +
            expNegInvGlue g •
              (charFun (Measure.dirac energy) t -
                charFun (base : Measure ℝ) t) := by
    funext g
    rw [charFun_nonperturbativeAtomicCompletion]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

/-- At every physical time, the complete coupling jet of the survival
amplitude is identical for the recurrent and dispersive compact families. -/
theorem charFun_recurrentCompactSpectrumFamily_flat
    (n : ℕ) (t : ℝ) :
    iteratedDeriv n
        (fun g =>
          charFun
            (recurrentCompactSpectrumFamily g : Measure ℝ) t) 0 =
      iteratedDeriv n
        (fun _ : ℝ =>
          charFun
            (compactPositiveContinuumSpectrum : Measure ℝ) t) 0 := by
  have hfun :
      (fun g =>
        charFun
          (recurrentCompactSpectrumFamily g : Measure ℝ) t) =
        fun g =>
          charFun
              (compactPositiveContinuumSpectrum : Measure ℝ) t +
            expNegInvGlue g •
              (charFun
                  (compactPositiveAtomSpectrum : Measure ℝ) t -
                charFun
                  (compactPositiveContinuumSpectrum : Measure ℝ) t) := by
    funext g
    rw [charFun_recurrentCompactSpectrumFamily]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

theorem charFun_recurrentCompactSpectrumFamily_contDiff
    (n : ℕ) (t : ℝ) :
    ContDiff ℝ n
      (fun g =>
        charFun
          (recurrentCompactSpectrumFamily g : Measure ℝ) t) := by
  have hfun :
      (fun g =>
        charFun
          (recurrentCompactSpectrumFamily g : Measure ℝ) t) =
        fun g =>
          expNegInvGlue g •
              charFun
                (compactPositiveAtomSpectrum : Measure ℝ) t +
            (1 - expNegInvGlue g) •
              charFun
                (compactPositiveContinuumSpectrum : Measure ℝ) t := by
    funext g
    exact charFun_recurrentCompactSpectrumFamily g t
  rw [hfun]
  fun_prop

/-- All perturbative coefficients of the full time-dependent survival
amplitude. -/
def perturbativeSurvivalAmplitudeJet
    (family : ℝ → ProbabilityMeasure ℝ) : ℕ → ℝ → ℂ :=
  fun n t =>
    iteratedDeriv n
      (fun g => charFun (family g : Measure ℝ) t) 0

theorem perturbativeSurvivalAmplitudeJet_compactFamilies_eq :
    perturbativeSurvivalAmplitudeJet
        recurrentCompactSpectrumFamily =
      perturbativeSurvivalAmplitudeJet
        dispersiveCompactSpectrumFamily := by
  funext n t
  exact charFun_recurrentCompactSpectrumFamily_flat n t

/-- All perturbative coefficients of the full time-dependent spectral form
factor. -/
def perturbativeSpectralFormFactorJet
    (family : ℝ → ProbabilityMeasure ℝ) : ℕ → ℝ → ℂ :=
  fun n t =>
    iteratedDeriv n
      (fun g =>
        survivalFormFactor (family g : Measure ℝ) t) 0

theorem perturbativeSpectralFormFactorJet_compactFamilies_eq :
    perturbativeSpectralFormFactorJet
        recurrentCompactSpectrumFamily =
      perturbativeSpectralFormFactorJet
        dispersiveCompactSpectrumFamily := by
  funext n t
  change
    iteratedDeriv n
        ((fun g =>
          charFun
            (recurrentCompactSpectrumFamily g : Measure ℝ) t) *
          (fun g =>
            charFun
              (recurrentCompactSpectrumFamily g : Measure ℝ) (-t))) 0 =
      iteratedDeriv n
        ((fun _ : ℝ =>
          charFun
            (compactPositiveContinuumSpectrum : Measure ℝ) t) *
          (fun _ : ℝ =>
            charFun
              (compactPositiveContinuumSpectrum : Measure ℝ) (-t))) 0
  rw [iteratedDeriv_mul
      (charFun_recurrentCompactSpectrumFamily_contDiff
        n t).contDiffAt
      (charFun_recurrentCompactSpectrumFamily_contDiff
        n (-t)).contDiffAt,
    iteratedDeriv_mul
      (contDiff_const : ContDiff ℝ n
        (fun _ : ℝ =>
          charFun
            (compactPositiveContinuumSpectrum : Measure ℝ) t)).contDiffAt
      (contDiff_const : ContDiff ℝ n
        (fun _ : ℝ =>
          charFun
            (compactPositiveContinuumSpectrum : Measure ℝ)
              (-t))).contDiffAt]
  apply Finset.sum_congr rfl
  intro k hk
  rw [charFun_recurrentCompactSpectrumFamily_flat k t,
    charFun_recurrentCompactSpectrumFamily_flat (n - k) (-t)]

/-- Every bounded continuous spectral probe is integrable against every
finite spectral measure. -/
theorem integrable_boundedContinuous_spectralProbe
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (f : BoundedContinuousFunction ℝ ℂ) :
    Integrable f mu := by
  refine Integrable.of_bound
    f.continuous.aestronglyMeasurable ‖f‖ ?_
  filter_upwards with x
  exact f.norm_coe_le_norm x

theorem integral_probabilityMixture_boundedContinuous
    (u : ℝ≥0∞) (hu : u ≤ 1)
    (mu nu : ProbabilityMeasure ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) :
    (∫ x, f x
      ∂(GaloisForLFunctions.HTGeometry.probabilityMixture
        u hu mu nu : Measure ℝ)) =
      u.toReal • (∫ x, f x ∂(mu : Measure ℝ)) +
        (1 - u).toReal •
          (∫ x, f x ∂(nu : Measure ℝ)) := by
  rw [GaloisForLFunctions.HTGeometry.probabilityMixture_toMeasure,
    integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
  · exact
      (integrable_boundedContinuous_spectralProbe
        (mu : Measure ℝ) f).smul_measure
        (ne_of_lt (hu.trans_lt ENNReal.one_lt_top))
  · exact
      (integrable_boundedContinuous_spectralProbe
        (nu : Measure ℝ) f).smul_measure
        (ne_of_lt ((tsub_le_self : 1 - u ≤ 1).trans_lt
          ENNReal.one_lt_top))

theorem integral_nonperturbativeSpectralCompletion
    (completion base : ProbabilityMeasure ℝ) (g : ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) :
    (∫ x, f x
        ∂(nonperturbativeSpectralCompletion
          completion base g : Measure ℝ)) =
      expNegInvGlue g •
          (∫ x, f x ∂(completion : Measure ℝ)) +
        (1 - expNegInvGlue g) •
          (∫ x, f x ∂(base : Measure ℝ)) := by
  rw [nonperturbativeSpectralCompletion,
    integral_probabilityMixture_boundedContinuous]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

theorem integral_nonperturbativeAtomicCompletion
    (base : ProbabilityMeasure ℝ) (energy g : ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) :
    (∫ x, f x
        ∂(nonperturbativeAtomicCompletion
          base energy g : Measure ℝ)) =
      expNegInvGlue g • f energy +
        (1 - expNegInvGlue g) •
          (∫ x, f x ∂(base : Measure ℝ)) := by
  rw [nonperturbativeAtomicCompletion,
    integral_probabilityMixture_boundedContinuous]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

theorem integral_recurrentCompactSpectrumFamily
    (g : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    (∫ x, f x
        ∂(recurrentCompactSpectrumFamily g : Measure ℝ)) =
      expNegInvGlue g •
          (∫ x, f x
            ∂(compactPositiveAtomSpectrum : Measure ℝ)) +
        (1 - expNegInvGlue g) •
          (∫ x, f x
            ∂(compactPositiveContinuumSpectrum : Measure ℝ)) := by
  rw [recurrentCompactSpectrumFamily,
    integral_probabilityMixture_boundedContinuous]
  simp only [nonperturbativeCouplingWeight,
    ENNReal.toReal_ofReal (expNegInvGlue.nonneg g)]
  rw [ENNReal.toReal_sub_of_le]
  · simp [expNegInvGlue.nonneg g]
  · exact nonperturbativeCouplingWeight_le_one g
  · norm_num

/-- Complete perturbative spectral theory of a coupling family: every
coupling derivative at zero of the expectation of every bounded continuous
function of energy. -/
def perturbativeBoundedSpectralObservableJet
    (family : ℝ → ProbabilityMeasure ℝ) :
    BoundedContinuousFunction ℝ ℂ → ℕ → ℂ :=
  fun f n =>
    iteratedDeriv n
      (fun g => ∫ x, f x ∂(family g : Measure ℝ)) 0

/-- Every exact completion of every base spectrum has the same complete
perturbative bounded-observable theory as the uncompleted base. -/
theorem integral_nonperturbativeSpectralCompletion_flat
    (completion base : ProbabilityMeasure ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    iteratedDeriv n
        (fun g =>
          ∫ x, f x
            ∂(nonperturbativeSpectralCompletion
              completion base g : Measure ℝ)) 0 =
      iteratedDeriv n
        (fun _ : ℝ => ∫ x, f x ∂(base : Measure ℝ)) 0 := by
  have hfun :
      (fun g =>
        ∫ x, f x
          ∂(nonperturbativeSpectralCompletion
            completion base g : Measure ℝ)) =
        fun g =>
          (∫ x, f x ∂(base : Measure ℝ)) +
            expNegInvGlue g •
              ((∫ x, f x ∂(completion : Measure ℝ)) -
                ∫ x, f x ∂(base : Measure ℝ)) := by
    funext g
    rw [integral_nonperturbativeSpectralCompletion]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

theorem perturbativeBoundedSpectralObservableJet_everyCompletion_eq
    (completion base : ProbabilityMeasure ℝ) :
    perturbativeBoundedSpectralObservableJet
        (nonperturbativeSpectralCompletion completion base) =
      perturbativeBoundedSpectralObservableJet
        (constantSpectrumFamily base) := by
  funext f n
  exact
    integral_nonperturbativeSpectralCompletion_flat
      completion base f n

/-- Universal infinite-completion law: after fixing any base spectral theory,
every probability spectrum is an exact nonperturbative completion of that
same all-orders perturbative theory. -/
theorem every_exactSpectralCompletion_is_perturbativelyInvisible
    (base : ProbabilityMeasure ℝ) :
    ∀ completion : ProbabilityMeasure ℝ,
      perturbativeBoundedSpectralObservableJet
          (nonperturbativeSpectralCompletion completion base) =
        perturbativeBoundedSpectralObservableJet
          (constantSpectrumFamily base) :=
  fun completion =>
    perturbativeBoundedSpectralObservableJet_everyCompletion_eq
      completion base

/-- Complete perturbative spectral theory is unchanged by the canonical
atomic completion, for every base spectrum and every selected energy. -/
theorem integral_nonperturbativeAtomicCompletion_flat
    (base : ProbabilityMeasure ℝ) (energy : ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    iteratedDeriv n
        (fun g =>
          ∫ x, f x
            ∂(nonperturbativeAtomicCompletion
              base energy g : Measure ℝ)) 0 =
      iteratedDeriv n
        (fun _ : ℝ => ∫ x, f x ∂(base : Measure ℝ)) 0 := by
  have hfun :
      (fun g =>
        ∫ x, f x
          ∂(nonperturbativeAtomicCompletion
            base energy g : Measure ℝ)) =
        fun g =>
          (∫ x, f x ∂(base : Measure ℝ)) +
            expNegInvGlue g •
              (f energy - ∫ x, f x ∂(base : Measure ℝ)) := by
    funext g
    rw [integral_nonperturbativeAtomicCompletion]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

theorem perturbativeBoundedSpectralObservableJet_atomicCompletion_eq
    (base : ProbabilityMeasure ℝ) (energy : ℝ) :
    perturbativeBoundedSpectralObservableJet
        (nonperturbativeAtomicCompletion base energy) =
      perturbativeBoundedSpectralObservableJet
        (constantSpectrumFamily base) := by
  funext f n
  exact
    integral_nonperturbativeAtomicCompletion_flat
      base energy f n

/-- Universal completion law.  Every atomless probability spectrum, at every
chosen energy and every positive coupling, has a recurrent completion whose
entire perturbative bounded-observable theory is exactly the uncompleted
one, although the two exact return plateaus are respectively positive and
zero. -/
theorem every_atomlessSpectrum_has_perturbativelyInvisible_recurrentCompletion
    (base : ProbabilityMeasure ℝ)
    [NoAtoms (base : Measure ℝ)] (energy : ℝ)
    {g : ℝ} (hg : 0 < g) :
    perturbativeBoundedSpectralObservableJet
        (nonperturbativeAtomicCompletion base energy) =
        perturbativeBoundedSpectralObservableJet
          (constantSpectrumFamily base) ∧
      HasPersistentMeanRecurrence
        (nonperturbativeAtomicCompletion
          base energy g : Measure ℝ) ∧
      recurrencePlateau
        (constantSpectrumFamily base g : Measure ℝ) = 0 := by
  exact ⟨
    perturbativeBoundedSpectralObservableJet_atomicCompletion_eq
      base energy,
    nonperturbativeAtomicCompletion_plateau_pos base energy hg,
    constantSpectrumFamily_plateau_zero base g⟩

theorem integral_recurrentCompactSpectrumFamily_flat
    (f : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    iteratedDeriv n
        (fun g =>
          ∫ x, f x
            ∂(recurrentCompactSpectrumFamily g : Measure ℝ)) 0 =
      iteratedDeriv n
        (fun _ : ℝ =>
          ∫ x, f x
            ∂(compactPositiveContinuumSpectrum : Measure ℝ)) 0 := by
  have hfun :
      (fun g =>
        ∫ x, f x
          ∂(recurrentCompactSpectrumFamily g : Measure ℝ)) =
        fun g =>
          (∫ x, f x
              ∂(compactPositiveContinuumSpectrum : Measure ℝ)) +
            expNegInvGlue g •
              ((∫ x, f x
                  ∂(compactPositiveAtomSpectrum : Measure ℝ)) -
                ∫ x, f x
                  ∂(compactPositiveContinuumSpectrum : Measure ℝ)) := by
    funext g
    rw [integral_recurrentCompactSpectrumFamily]
    module
  rw [hfun]
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [iteratedDeriv_const_add (Nat.succ_pos n)]
      rw [iteratedDeriv_smul_const
        expNegInvGlue.contDiff.contDiffAt]
      rw [iteratedDeriv_expNegInvGlue_zero]
      simp
      simp [iteratedDeriv_const]

/-- The recurrent and dispersive families have identical complete
perturbative spectral theories, not merely identical form-factor series. -/
theorem perturbativeBoundedSpectralObservableJet_compactFamilies_eq :
    perturbativeBoundedSpectralObservableJet
        recurrentCompactSpectrumFamily =
      perturbativeBoundedSpectralObservableJet
        dispersiveCompactSpectrumFamily := by
  funext f n
  exact integral_recurrentCompactSpectrumFamily_flat f n

/-- No recurrence classifier can succeed even when given the coupling jets
of every bounded continuous spectral observable. -/
theorem no_universal_compactPositive_completePerturbativeSpectralTheory_recurrenceClassifier
    (gstar : ℝ) (hgstar : 0 < gstar) :
    ¬ ∃ classifier :
        (BoundedContinuousFunction ℝ ℂ → ℕ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeBoundedSpectralObservableJet family) ↔
          HasPersistentMeanRecurrence
            (family gstar : Measure ℝ)) := by
  rintro ⟨classifier, hclassifier⟩
  have hrec :=
    hclassifier recurrentCompactSpectrumFamily
      recurrentCompactSpectrumFamily_uniformlyCompactPositive
  have hdisp :=
    hclassifier dispersiveCompactSpectrumFamily
      dispersiveCompactSpectrumFamily_uniformlyCompactPositive
  have hclassified :
      classifier
        (perturbativeBoundedSpectralObservableJet
          recurrentCompactSpectrumFamily) :=
    hrec.mpr
      (recurrentCompactSpectrumFamily_plateau_pos hgstar)
  have hclassifiedDisp :
      classifier
        (perturbativeBoundedSpectralObservableJet
          dispersiveCompactSpectrumFamily) := by
    rw [←
      perturbativeBoundedSpectralObservableJet_compactFamilies_eq]
    exact hclassified
  have hfalse := hdisp.mp hclassifiedDisp
  rw [HasPersistentMeanRecurrence,
    dispersiveCompactSpectrumFamily_plateau_zero] at hfalse
  exact (lt_irrefl 0) hfalse

/-- **Nonperturbative recurrence forecast no-go law.**  For every positive
target coupling, no predicate on the complete all-orders, all-times
perturbative spectral form factor can correctly decide positive-plateau
recurrence for every probability-spectrum family supported in `[1, 2]`. -/
theorem no_universal_compactPositive_completePerturbativeSFF_recurrenceClassifier
    (gstar : ℝ) (hgstar : 0 < gstar) :
    ¬ ∃ classifier : (ℕ → ℝ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeSpectralFormFactorJet family) ↔
          HasPersistentMeanRecurrence
            (family gstar : Measure ℝ)) := by
  rintro ⟨classifier, hclassifier⟩
  have hrec :=
    hclassifier recurrentCompactSpectrumFamily
      recurrentCompactSpectrumFamily_uniformlyCompactPositive
  have hdisp :=
    hclassifier dispersiveCompactSpectrumFamily
      dispersiveCompactSpectrumFamily_uniformlyCompactPositive
  have hclassified :
      classifier
        (perturbativeSpectralFormFactorJet
          recurrentCompactSpectrumFamily) :=
    hrec.mpr
      (recurrentCompactSpectrumFamily_plateau_pos hgstar)
  have hclassifiedDisp :
      classifier
        (perturbativeSpectralFormFactorJet
          dispersiveCompactSpectrumFamily) := by
    rw [←
      perturbativeSpectralFormFactorJet_compactFamilies_eq]
    exact hclassified
  have hfalse := hdisp.mp hclassifiedDisp
  rw [HasPersistentMeanRecurrence,
    dispersiveCompactSpectrumFamily_plateau_zero] at hfalse
  exact (lt_irrefl 0) hfalse

end RHTower
