import GaloisForLFunctions.HTGeometry.CyclicPhaseConcentration

/-!
# Quenched finite-union cyclic phase avoidance

The off-grid cyclic cap exponent survives a complete finite union over observation times and target
rays.  If the resulting entropy budget is below one, a single frequency draw avoids every target
at every listed time.  This is a same-draw statement: no frequency resampling occurs between times
or targets.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Frequencies whose phase state has overlap at least `threshold` with a target ray. -/
def cyclicOverlapCaptureSet
    {I : Type*} [Fintype I] (p : ℕ) (t : ℝ) (w : I → ℂ)
    (threshold : ℝ) : Set (I → Fin p) :=
  {q | threshold ≤ ‖∑ i, w i * cyclicPhaseValue p t (q i)‖}

variable {I K Y : Type*} [Fintype I] [Fintype K] [Fintype Y]

/-- A complete finite time-target dictionary pays only its exact cardinality against the
off-grid cyclic cap exponent. -/
theorem measureReal_iUnion_cyclicOverlapCaptureSet_le
    (p : ℕ) [NeZero p] (hp : 0 < p) (time : K → ℝ) (weight : Y → I → ℂ)
    {threshold bias energy : ℝ} (hbias : 0 ≤ bias) (hthreshold : bias ≤ threshold)
    (henergy : ∀ y, (↑(∑ i, ‖weight y i‖₊ ^ 2) : ℝ) = energy)
    (hmean : ∀ k y,
      ‖cyclicPhaseMean p (time k) * ∑ i, weight y i‖ ≤ bias) :
    (cyclicFrequencyProductMeasure p I).real
        (⋃ z : K × Y,
          cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) ≤
      ((Fintype.card K : ℝ) * Fintype.card Y) *
        (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
  classical
  calc
    (cyclicFrequencyProductMeasure p I).real
        (⋃ z : K × Y,
          cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold)
        ≤ ∑ z : K × Y,
            (cyclicFrequencyProductMeasure p I).real
              (cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) :=
          measureReal_iUnion_fintype_le _
    _ ≤ ∑ _z : K × Y,
          (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
      exact Finset.sum_le_sum fun z _hz => by
        simpa [cyclicOverlapCaptureSet, henergy z.2] using
          (measureReal_cyclicOverlap_ge_le p hp (time z.1) (weight z.2)
            hbias hthreshold (hmean z.1 z.2))
    _ = ((Fintype.card K : ℝ) * Fintype.card Y) *
          (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
      simp [Fintype.card_prod]

/-- Variance-budget version of the complete finite time-target union.  Target rays may carry
different or vanishing coefficient mass; only one common upper budget is charged. -/
theorem measureReal_iUnion_cyclicOverlapCaptureSet_le_of_energy_le
    (p : ℕ) [NeZero p] (hp : 0 < p) (time : K → ℝ) (weight : Y → I → ℂ)
    {threshold bias energy : ℝ} (henergy : 0 < energy)
    (hbias : 0 ≤ bias) (hthreshold : bias < threshold)
    (hweight : ∀ y, (↑(∑ i, ‖weight y i‖₊ ^ 2) : ℝ) ≤ energy)
    (hmean : ∀ k y,
      ‖cyclicPhaseMean p (time k) * ∑ i, weight y i‖ ≤ bias) :
    (cyclicFrequencyProductMeasure p I).real
        (⋃ z : K × Y,
          cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) ≤
      ((Fintype.card K : ℝ) * Fintype.card Y) *
        (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
  classical
  calc
    (cyclicFrequencyProductMeasure p I).real
        (⋃ z : K × Y,
          cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold)
        ≤ ∑ z : K × Y,
            (cyclicFrequencyProductMeasure p I).real
              (cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) :=
          measureReal_iUnion_fintype_le _
    _ ≤ ∑ _z : K × Y,
          (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
      exact Finset.sum_le_sum fun z _hz => by
        simpa [cyclicOverlapCaptureSet] using
          (measureReal_cyclicOverlap_ge_le_of_energy_le p hp (time z.1) (weight z.2)
            henergy hbias hthreshold (hweight z.2) (hmean z.1 z.2))
    _ = ((Fintype.card K : ℝ) * Fintype.card Y) *
          (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) := by
      simp [Fintype.card_prod]

/-- If the complete mesh-target union has mass below one, one quenched frequency draw avoids
every target at every mesh time simultaneously. -/
theorem exists_cyclicFrequencies_avoid_finite_time_target_union
    (p : ℕ) [NeZero p] (hp : 0 < p) (time : K → ℝ) (weight : Y → I → ℂ)
    {threshold bias energy : ℝ} (hbias : 0 ≤ bias) (hthreshold : bias ≤ threshold)
    (henergy : ∀ y, (↑(∑ i, ‖weight y i‖₊ ^ 2) : ℝ) = energy)
    (hmean : ∀ k y,
      ‖cyclicPhaseMean p (time k) * ∑ i, weight y i‖ ≤ bias)
    (hbudget : ((Fintype.card K : ℝ) * Fintype.card Y) *
        (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) < 1) :
    ∃ q : I → Fin p, ∀ k y,
      ‖∑ i, weight y i * cyclicPhaseValue p (time k) (q i)‖ < threshold := by
  classical
  let μ := cyclicFrequencyProductMeasure p I
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, cyclicFrequencyProductMeasure, cyclicFrequencyMeasure]
    infer_instance
  by_contra hex
  push Not at hex
  have huniv : (⋃ z : K × Y,
      cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨k, y, hky⟩ := hex q
    exact Set.mem_iUnion.mpr ⟨(k, y), hky⟩
  have hmass := measureReal_iUnion_cyclicOverlapCaptureSet_le
    p hp time weight hbias hthreshold henergy hmean
  change μ.real _ ≤ _ at hmass
  rw [huniv, probReal_univ] at hmass
  linarith

/-- Same-draw finite avoidance with only an upper bound on each target's coefficient energy. -/
theorem exists_cyclicFrequencies_avoid_finite_time_target_union_of_energy_le
    (p : ℕ) [NeZero p] (hp : 0 < p) (time : K → ℝ) (weight : Y → I → ℂ)
    {threshold bias energy : ℝ} (henergy : 0 < energy)
    (hbias : 0 ≤ bias) (hthreshold : bias < threshold)
    (hweight : ∀ y, (↑(∑ i, ‖weight y i‖₊ ^ 2) : ℝ) ≤ energy)
    (hmean : ∀ k y,
      ‖cyclicPhaseMean p (time k) * ∑ i, weight y i‖ ≤ bias)
    (hbudget : ((Fintype.card K : ℝ) * Fintype.card Y) *
        (4 * Real.exp (-(threshold - bias) ^ 2 / (16 * energy))) < 1) :
    ∃ q : I → Fin p, ∀ k y,
      ‖∑ i, weight y i * cyclicPhaseValue p (time k) (q i)‖ < threshold := by
  classical
  let μ := cyclicFrequencyProductMeasure p I
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, cyclicFrequencyProductMeasure, cyclicFrequencyMeasure]
    infer_instance
  by_contra hex
  push Not at hex
  have huniv : (⋃ z : K × Y,
      cyclicOverlapCaptureSet p (time z.1) (weight z.2) threshold) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨k, y, hky⟩ := hex q
    exact Set.mem_iUnion.mpr ⟨(k, y), hky⟩
  have hmass := measureReal_iUnion_cyclicOverlapCaptureSet_le_of_energy_le
    p hp time weight henergy hbias hthreshold hweight hmean
  change μ.real _ ≤ _ at hmass
  rw [huniv, probReal_univ] at hmass
  linarith

end

end GaloisForLFunctions.HTGeometry
