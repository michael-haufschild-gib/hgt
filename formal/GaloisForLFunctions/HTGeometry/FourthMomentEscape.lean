import GaloisForLFunctions.HTGeometry.PaleyZygmund

/-!
# A diverging second moment with a controlled fourth moment forces unboundedness

Let `f N` be nonnegative random variables whose second moments diverge and whose fourth moments stay
within a fixed multiple of the square of the second moments,

```text
∫ (f N)⁴ ≤ C (∫ (f N)²)² ,        ∫ (f N)² → ∞ .
```

Paley–Zygmund applied to `Z = (f N)²` at `θ = 1/2` gives, for every such `N`,

```text
P( (f N)² > (∫ (f N)²)/2 )  ≥  (1/4)(∫ (f N)²)² / ∫ (f N)⁴  ≥  1/(4C) ,
```

a lower bound *independent of `N`*.  Since the threshold `(∫ (f N)²)/2` escapes to infinity, every
level `M` is exceeded by some `f N` with probability at least `1/(4C)`, and taking the decreasing
intersection over integer levels shows the family is unbounded with probability at least `1/(4C)`.

This is the elementary replacement for Kolmogorov's three-series theorem in the argument that a
random series with diverging second moments cannot converge: it needs no stopping time, no maximal
inequality, and no martingale theory — only a fourth-moment bound, which for genuinely independent
summands is a finite orthogonality computation.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The uniform Paley–Zygmund bound.**  A fourth moment within `C` times the square of the second
moment forces the square to exceed half its mean with probability at least `1/(4C)`. -/
theorem measure_sq_gt_half_ge [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hmg : Measurable g)
    (hi2 : Integrable (fun x => g x ^ 2) μ)
    (hi4 : Integrable (fun x => (g x ^ 2) ^ 2) μ)
    {C : ℝ} (hC : 0 < C)
    (hup : ∫ x, (g x ^ 2) ^ 2 ∂μ ≤ C * (∫ x, g x ^ 2 ∂μ) ^ 2)
    (hpos : 0 < ∫ x, g x ^ 2 ∂μ) :
    1 / (4 * C) ≤ (μ {x | (1 / 2 : ℝ) * (∫ x, g x ^ 2 ∂μ) < g x ^ 2}).toReal := by
  have hpz := paley_zygmund (μ := μ) (Z := fun x => g x ^ 2) (hmg.pow_const 2)
    (fun x => sq_nonneg (g x)) hi2 hi4 (θ := 1 / 2) (by norm_num) (by norm_num)
  set A : ℝ := ∫ x, g x ^ 2 ∂μ with hAdef
  set p : ℝ := (μ {x | (1 / 2 : ℝ) * A < g x ^ 2}).toReal with hpdef
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hstep : (1 - 1 / 2 : ℝ) ^ 2 * A ^ 2 ≤ (C * A ^ 2) * p := by
    refine hpz.trans ?_
    exact mul_le_mul_of_nonneg_right hup hp0
  have hA2 : 0 < A ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hstep, hA2, hC, hp0]

/-- Every level is exceeded with probability at least `1/(4C)`. -/
theorem measure_exists_gt_ge [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hmeas : ∀ N, Measurable (f N)) (hf0 : ∀ N x, 0 ≤ f N x)
    (hi2 : ∀ N, Integrable (fun x => f N x ^ 2) μ)
    (hi4 : ∀ N, Integrable (fun x => (f N x ^ 2) ^ 2) μ)
    {C : ℝ} (hC : 0 < C)
    (hup : ∀ N, ∫ x, (f N x ^ 2) ^ 2 ∂μ ≤ C * (∫ x, f N x ^ 2 ∂μ) ^ 2)
    (hA : Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop atTop)
    {M : ℝ} (hM : 0 ≤ M) :
    1 / (4 * C) ≤ (μ {x | ∃ N, M < f N x}).toReal := by
  obtain ⟨N, hN⟩ := (hA.eventually_gt_atTop (max 1 (2 * M ^ 2))).exists
  have hpos : 0 < ∫ x, f N x ^ 2 ∂μ := lt_of_lt_of_le zero_lt_one (le_of_lt
    (lt_of_le_of_lt (le_max_left 1 (2 * M ^ 2)) hN))
  have hbase := measure_sq_gt_half_ge (μ := μ) (g := f N) (hmeas N) (hi2 N) (hi4 N)
    hC (hup N) hpos
  have hsub : {x | (1 / 2 : ℝ) * (∫ x, f N x ^ 2 ∂μ) < f N x ^ 2} ⊆ {x | ∃ N, M < f N x} := by
    intro x hx
    refine ⟨N, ?_⟩
    have hthr : M ^ 2 < f N x ^ 2 := by
      have h2 : 2 * M ^ 2 < ∫ x, f N x ^ 2 ∂μ :=
        lt_of_le_of_lt (le_max_right 1 (2 * M ^ 2)) hN
      have := hx
      simp only [Set.mem_setOf_eq] at this
      linarith
    nlinarith [hthr, hf0 N x, hM]
  refine hbase.trans ?_
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)

/-- **The family is unbounded with probability at least `1/(4C)`.** -/
theorem measure_unbounded_ge [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hmeas : ∀ N, Measurable (f N)) (hf0 : ∀ N x, 0 ≤ f N x)
    (hi2 : ∀ N, Integrable (fun x => f N x ^ 2) μ)
    (hi4 : ∀ N, Integrable (fun x => (f N x ^ 2) ^ 2) μ)
    {C : ℝ} (hC : 0 < C)
    (hup : ∀ N, ∫ x, (f N x ^ 2) ^ 2 ∂μ ≤ C * (∫ x, f N x ^ 2 ∂μ) ^ 2)
    (hA : Tendsto (fun N => ∫ x, f N x ^ 2 ∂μ) atTop atTop) :
    ENNReal.ofReal (1 / (4 * C)) ≤ μ {x | ∀ K : ℕ, ∃ N, (K : ℝ) < f N x} := by
  set S : ℕ → Set Ω := fun K => {x | ∃ N, (K : ℝ) < f N x} with hSdef
  have hSmeas : ∀ K, MeasurableSet (S K) := by
    intro K
    have : S K = ⋃ N, {x | (K : ℝ) < f N x} := by
      ext x; simp [hSdef]
    rw [this]
    exact MeasurableSet.iUnion fun N => measurableSet_lt measurable_const (hmeas N)
  have hanti : Antitone S := by
    intro a b hab x hx
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, lt_of_le_of_lt (by exact_mod_cast Nat.cast_le.2 hab) hN⟩
  have hbound : ∀ K : ℕ, ENNReal.ofReal (1 / (4 * C)) ≤ μ (S K) := by
    intro K
    refine ENNReal.ofReal_le_of_le_toReal ?_
    exact measure_exists_gt_ge hmeas hf0 hi2 hi4 hC hup hA (M := (K : ℝ)) (Nat.cast_nonneg K)
  have hlim := tendsto_measure_iInter_atTop
    (fun K => (hSmeas K).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  have hiInter : (⋂ K, S K) = {x | ∀ K : ℕ, ∃ N, (K : ℝ) < f N x} := by
    ext x
    simp [hSdef]
  rw [hiInter] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

end GaloisForLFunctions.HTGeometry

end
