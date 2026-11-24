import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.PhaseLaw
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Born probabilities of discrete observations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory
open scoped ENNReal
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Total mass satisfying a test on the labels. -/
def selectedMass {ι : Type*} (w : ι → ℝ) (P : ι → Prop) := ∑' n, if P n then w n else 0

theorem selected_summable {ι : Type*} {w : ι → ℝ} (hs : Summable w) (P : ι → Prop) :
    Summable (fun n => if P n then w n else 0) := by
  apply (hs.indicator {n | P n}).congr
  intro n
  by_cases h : P n <;> simp [Set.indicator,h]

theorem selectedMass_congr {ι : Type*} (w : ι → ℝ) {P Q : ι → Prop} (h : ∀ n, P n ↔ Q n) :
    selectedMass w P = selectedMass w Q :=
  tsum_congr fun n => by simp only [h n]

/-- A sequence of label tests eventually separating one label recovers its weight
under any fixed summable nonnegative law. -/
theorem selectedMass_limit_singleton {ι : Type*} {w : ι → ℝ} (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (P : ℕ → ι → Prop) (a : ι) (h : ∀ n, ∀ᶠ j in atTop, P j n ↔ n = a) :
    Tendsto (fun j => selectedMass w (P j)) atTop (𝓝 (w a)) := by
  let f (j : ℕ) (n : ι) := if P j n then w n else 0
  have hl (n : ι) : Tendsto (fun j => f j n) atTop (𝓝 (if n = a then w n else 0)) := by
    apply EventuallyEq.tendsto
    filter_upwards [h n] with j hj
    simp only [f,hj]
  have hb : ∀ᶠ j in atTop, ∀ n, ‖f j n‖ ≤ w n := Eventually.of_forall fun j n => by
    by_cases hp : P j n <;> simp [f,hp,Real.norm_of_nonneg (hw n),hw n]
  have ht := tendsto_tsum_of_dominated_convergence hs hl hb
  have he : (∑' n, if n = a then w n else 0) = w a := by simp
  rw [he] at ht
  exact ht

/-- Law of a simultaneous or single observable obtained by assigning a report to each occupied label. -/
def labelReportLaw {X : Type*} [MeasurableSpace X] (v : MissingWave) (Z : ℕ+ → X) : ProbabilityMeasure X :=
  ⟨Measure.sum (fun n => ENNReal.ofReal (occupationProbability v n) • Measure.dirac (Z n)),⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,
      ← ENNReal.ofReal_tsum_of_nonneg (occupationLaw_nonneg v) (occupationLaw_hasSum v).summable,
      (occupationLaw_hasSum v).tsum_eq,ENNReal.ofReal_one]⟩⟩

theorem labelReportLaw_apply {X : Type*} [MeasurableSpace X] (v : MissingWave) (Z : ℕ+ → X)
    {s : Set X} (hs : MeasurableSet s) :
    (labelReportLaw v Z : Measure X) s = ENNReal.ofReal (selectedMass (occupationProbability v) (fun n => Z n ∈ s)) := by
  change (Measure.sum _) s = _
  rw [Measure.sum_apply _ hs,selectedMass,ENNReal.ofReal_tsum_of_nonneg _ (selected_summable (occupationLaw_hasSum v).summable _)]
  · apply tsum_congr
    intro n
    rw [Measure.smul_apply,Measure.dirac_apply' _ hs]
    by_cases h : Z n ∈ s <;> simp [Set.indicator,h,smul_eq_mul]
  · intro n
    split
    · exact occupationLaw_nonneg v n
    · exact le_rfl

/-- A singleton reading records total probability on its exact fiber. -/
theorem labelReportLaw_atom {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (v : MissingWave) (Z : ℕ+ → X) (x : X) :
    ((labelReportLaw v Z : Measure X) {x}).toReal =
      selectedMass (occupationProbability v) (fun n => Z n = x) := by
  rw [labelReportLaw_apply v Z (measurableSet_singleton x),ENNReal.toReal_ofReal]
  · rfl
  · apply tsum_nonneg
    intro n
    split
    · exact occupationLaw_nonneg v n
    · exact le_rfl

theorem phaseLaw_as_labelReport (v : MissingWave) (t : ℝ) :
    occupationPhaseLaw v t = labelReportLaw v (occupationPhase t) := rfl

#print axioms selected_summable
#print axioms selectedMass_congr
#print axioms selectedMass_limit_singleton
#print axioms labelReportLaw_apply
#print axioms labelReportLaw_atom
#print axioms phaseLaw_as_labelReport

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
