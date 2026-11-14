import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.GammaCoxDetection
import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite Gamma–Cox classification laws

Independent binary observations with the Gamma–Poisson detection marginals
recover the entire zero pattern with probability tending to one. Consequently
any observable of that pattern, including its counting measure, is consistent.
The law is extended to negative concentration by replacing it with zero.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- The detection probability as a point of the unit interval. -/
def parameter (K r : ℝ) : unitInterval :=
  ⟨detection (max K 0) r, detection_nonneg _ _ (le_max_right _ _),
    (detection_lt_one _ _).le⟩

/-- Independent occupancy reports with the integrated Gamma–Poisson marginals. -/
def binaryLaw {ι : Type*} [Fintype ι] (K : ℝ) (g : ι → ℝ) : Measure (ι → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (parameter K (g i))

instance {ι : Type*} [Fintype ι] (K : ℝ) (g : ι → ℝ) :
    IsProbabilityMeasure (binaryLaw K g) := by
  unfold binaryLaw
  infer_instance

/-- The deterministic pattern of exact zeros. -/
def zeroPattern {ι : Type*} (g : ι → ℝ) : ι → Bool := fun i => decide (g i = 0)

/-- An arbitrary Boolean pattern has the product of its marginal probabilities. -/
theorem binaryLaw_singleton {ι : Type*} [Fintype ι]
    (K : ℝ) (g : ι → ℝ) (b : ι → Bool) :
    (binaryLaw K g).real {b} =
      ∏ i, if b i then detection (max K 0) (g i) else 1 - detection (max K 0) (g i) := by
  rw [measureReal_def, binaryLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (bernoulliMeasure true false (parameter K (g i))).real {b i} = _
  cases b i <;> simp [parameter]

/-- Exact probability of at least one classification error. -/
theorem binaryLaw_error_eq {ι : Type*} [Fintype ι] (K : ℝ) (g : ι → ℝ) :
    (binaryLaw K g).real {b | b ≠ zeroPattern g} =
      1 - ∏ i, (1 - error (max K 0) (g i)) := by
  change (binaryLaw K g).real ({zeroPattern g}ᶜ) = _
  rw [measureReal_compl (measurableSet_singleton _), probReal_univ,
    binaryLaw_singleton]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : g i = 0 <;> simp [zeroPattern, error, h]

/-- Finite-set classification error is bounded by the sum of marginal envelopes. -/
theorem binaryLaw_error_le {ι : Type*} [Fintype ι] (K : ℝ) (g : ι → ℝ) :
    (binaryLaw K g).real {b | b ≠ zeroPattern g} ≤
      errorBound Finset.univ g (max K 0) := by
  rw [binaryLaw_error_eq]
  refine le_trans (one_sub_prod_le_sum_one_sub Finset.univ
    (fun i => 1 - error (max K 0) (g i)) ?_ ?_) ?_
  · intro i
    unfold error
    split_ifs
    · simpa only [sub_sub_cancel] using detection_nonneg _ (g i) (le_max_right K 0)
    · exact sub_nonneg.mpr (detection_lt_one _ _).le
  · intro i
    linarith only [error_nonneg (max K 0) (g i) (le_max_right K 0)]
  · simpa only [sub_sub_cancel] using sum_error_le Finset.univ g (max K 0) (le_max_right K 0)

/-- The probability of any error tends to zero on every finite candidate set. -/
theorem tendsto_binaryLaw_error {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    Tendsto (fun K => (binaryLaw K g).real {b | b ≠ zeroPattern g}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun K => binaryLaw_error_le K g)
  apply (tendsto_errorBound Finset.univ g).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK
  rw [max_eq_left hK]

/-- Any statistic of the finite pattern agrees exactly with its true value with
probability tending to one. No topology or measurability of the statistic is needed. -/
theorem tendsto_observable_error {ι Y : Type*} [Fintype ι]
    (g : ι → ℝ) (F : (ι → Bool) → Y) :
    Tendsto (fun K => (binaryLaw K g).real {b | F b ≠ F (zeroPattern g)}) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun K => ?_) (tendsto_binaryLaw_error g)
  exact measureReal_mono (fun b hb heq => hb (congrArg F heq)) (measure_ne_top _ _)

/-- The binary counting measure carried by a finite family of labelled locations. -/
def countingMeasure {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (x : ι → X) (b : ι → Bool) : Measure X :=
  ∑ i, if b i then Measure.dirac (x i) else 0

/-- Recovery of the whole atomic zero-counting measure; repeated locations are allowed. -/
theorem tendsto_countingMeasure_error {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (g : ι → ℝ) (x : ι → X) :
    Tendsto (fun K => (binaryLaw K g).real
      {b | countingMeasure x b ≠ countingMeasure x (zeroPattern g)}) atTop (𝓝 0) :=
  tendsto_observable_error g (countingMeasure x)

/-- Finite weighted tests converge in the stronger sense of exact agreement in probability. -/
theorem tendsto_weighted_statistic_error {ι : Type*} [Fintype ι] (g w : ι → ℝ) :
    Tendsto (fun K => (binaryLaw K g).real
      {b | (∑ i, if b i then w i else 0) ≠ ∑ i, if g i = 0 then w i else 0})
      atTop (𝓝 0) := by
  simpa only [zeroPattern, decide_eq_true_eq] using
    tendsto_observable_error g (fun b => ∑ i, if b i then w i else 0)

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.binaryLaw_singleton
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.binaryLaw_error_eq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.binaryLaw_error_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_binaryLaw_error
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_observable_error
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_countingMeasure_error
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_weighted_statistic_error
