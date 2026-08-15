import GaloisForLFunctions.HTGeometry.BinomialTailDerivativeBound

/-!
# The bounded replica reporter brackets threshold probabilities

The bounded replica reporter is exponentially close to one above the upper threshold and
exponentially small below the lower threshold, so pointwise it is squeezed between the indicator of
the upper threshold event scaled by that exponential deficit and the indicator of the lower
threshold event shifted by the same exponential.

Integrating those two pointwise bounds against any probability law brackets the reporter mean
between the two threshold probabilities, with an error that depends only on the replica order and
the threshold gap — never on the size of the target dictionary.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

section ReporterExpectation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponential replica deficit. -/
noncomputable def replicaDeficit (r : ℕ) (a b : ℝ) : ℝ :=
  Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2))

theorem replicaDeficit_pos (r : ℕ) (a b : ℝ) : 0 < replicaDeficit r a b := Real.exp_pos _

theorem replicaDeficit_le_one (r : ℕ) (a b : ℝ) : replicaDeficit r a b ≤ 1 := by
  rw [replicaDeficit, Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ (r : ℝ) * (a - b) ^ 2 / 2 := by positivity
  linarith

private theorem integrable_binomialTail_comp (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) (r k : ℕ) :
    Integrable (fun ω => binomialTail r k (Y ω)) ν := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact ((continuous_binomialTail r k).measurable.comp hY).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (binomialTail_nonneg (hY0 ω) (hY1 ω) r k)]
    exact binomialTail_le_one (hY0 ω) (hY1 ω) r k

/-- **Reporter mean, lower half.**  Above the upper threshold the reporter mean dominates the
threshold probability up to the exponential deficit. -/
theorem replicaDeficit_mul_measure_le_integral (ν : Measure Ω) [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    {r : ℕ} {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    (1 - replicaDeficit r a b) * (ν {ω | a ≤ Y ω}).toReal ≤
      ∫ ω, binomialTail r (replicaThreshold r a b) (Y ω) ∂ν := by
  classical
  have hmeas : MeasurableSet {ω | a ≤ Y ω} := hY measurableSet_Ici
  have hdef1 : 1 - replicaDeficit r a b ≤ 1 := by
    have := (replicaDeficit_pos r a b)
    linarith
  have hdef0 : 0 ≤ 1 - replicaDeficit r a b := by
    have := replicaDeficit_le_one r a b
    linarith
  have hpoint : ∀ ω, (1 - replicaDeficit r a b) * Set.indicator {ω | a ≤ Y ω} 1 ω ≤
      binomialTail r (replicaThreshold r a b) (Y ω) := by
    intro ω
    by_cases hω : ω ∈ {ω | a ≤ Y ω}
    · rw [Set.indicator_of_mem hω]
      show (1 - replicaDeficit r a b) * 1 ≤ _
      rw [mul_one]
      exact one_sub_le_binomialTail_replicaThreshold hb hba ha hω (hY1 ω)
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact binomialTail_nonneg (hY0 ω) (hY1 ω) _ _
  have hint : Integrable (fun ω => (1 - replicaDeficit r a b) *
      Set.indicator {ω | a ≤ Y ω} 1 ω) ν := by
    refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff hmeas]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono hint
    (integrable_binomialTail_comp ν hY hY0 hY1 r (replicaThreshold r a b)) hpoint
  refine le_trans (le_of_eq ?_) hmono
  rw [integral_const_mul, integral_indicator_one hmeas]
  rfl

/-- **Reporter mean, upper half.**  The reporter mean is dominated by the lower threshold
probability plus the exponential deficit. -/
theorem integral_le_measure_add_replicaDeficit (ν : Measure Ω) [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1)
    {r : ℕ} {a b : ℝ} (hba : b < a) (ha : a < 1) :
    (∫ ω, binomialTail r (replicaThreshold r a b) (Y ω) ∂ν) ≤
      (ν {ω | b ≤ Y ω}).toReal + replicaDeficit r a b := by
  classical
  have hmeas : MeasurableSet {ω | b ≤ Y ω} := hY measurableSet_Ici
  have hpoint : ∀ ω, binomialTail r (replicaThreshold r a b) (Y ω) ≤
      Set.indicator {ω | b ≤ Y ω} 1 ω + replicaDeficit r a b := by
    intro ω
    by_cases hω : ω ∈ {ω | b ≤ Y ω}
    · rw [Set.indicator_of_mem hω]
      have h1 : binomialTail r (replicaThreshold r a b) (Y ω) ≤ 1 :=
        binomialTail_le_one (hY0 ω) (hY1 ω) _ _
      have h2 : (0 : ℝ) < replicaDeficit r a b := replicaDeficit_pos r a b
      show _ ≤ (1 : ℝ) + replicaDeficit r a b
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hlt : Y ω ≤ b := by
        by_contra hc
        exact hω (le_of_lt (lt_of_not_ge hc))
      have := binomialTail_replicaThreshold_le (r := r) hba ha (hY0 ω) hlt
      rw [replicaDeficit]
      linarith
  have hint : Integrable (fun ω => Set.indicator {ω | b ≤ Y ω} 1 ω + replicaDeficit r a b) ν := by
    refine Integrable.add ?_ (integrable_const _)
    rw [integrable_indicator_iff hmeas]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono (integrable_binomialTail_comp ν hY hY0 hY1 r
    (replicaThreshold r a b)) hint hpoint
  refine le_trans hmono (le_of_eq ?_)
  rw [integral_add ?_ (integrable_const _), integral_indicator_one hmeas, integral_const]
  · simp [measureReal_def]
  · rw [integrable_indicator_iff hmeas]
    exact integrableOn_const (by simp [measure_ne_top])

end ReporterExpectation

section ReplicaOrder

/-- The replica order that achieves a prescribed reporter error at a prescribed threshold gap. -/
noncomputable def replicaOrderOf (ζ δ : ℝ) : ℕ := ⌈2 * Real.log (1 / ζ) / δ ^ 2⌉₊

/-- **Prescribed reporter error.**  The stated replica order makes the exponential deficit at most
the prescribed error. -/
theorem replicaDeficit_replicaOrderOf_le {ζ δ a b : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδ : 0 < δ) (hab : a - b = δ) :
    replicaDeficit (replicaOrderOf ζ δ) a b ≤ ζ := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (1 / ζ) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hζ0, one_mul]
    exact hζ1
  have hceil : 2 * Real.log (1 / ζ) / δ ^ 2 ≤ (replicaOrderOf ζ δ : ℝ) :=
    Nat.le_ceil _
  have hkey : Real.log (1 / ζ) ≤ (replicaOrderOf ζ δ : ℝ) * δ ^ 2 / 2 := by
    rw [div_le_iff₀ hδ2] at hceil
    linarith
  rw [replicaDeficit, hab]
  have hexp : Real.exp (-((replicaOrderOf ζ δ : ℝ) * δ ^ 2 / 2)) ≤
      Real.exp (-Real.log (1 / ζ)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  refine le_trans hexp (le_of_eq ?_)
  rw [← Real.log_inv, one_div, inv_inv, Real.exp_log hζ0]

end ReplicaOrder

end GaloisForLFunctions.HTGeometry
