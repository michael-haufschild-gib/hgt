import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareCapstone
import GaloisForLFunctions.RHTower.Sieve.RealWindowVariance

/-!
# The discrete short-interval mean square, bounded by Gallagher's machinery

The two halves meet.  `integral_realWindow_eq_sum` says the discrete mean square over the integer
starting points `Y, …, Y+K−1` *equals* the integral of the real-start window mean square over
`[Y, Y+K]`; `integral_Ioc_normSq_linSum_range_le` bounds that integral over any multiplicative range
`(Y, Y(1+ε)^{K'}]` by `K'` blocks of Gallagher cost.  Since the integrand is nonnegative, covering
`[Y, Y+K]` by such a range costs nothing:

```text
∑_{k < K} | ∑_{Y+k < n ≤ Y+k+L} c_n |²  ≤  Y(1+ε)^{K'} · K' · blockCost(L, Y, ε, M₁, M₂, W) ,
```

whenever `Y + K ≤ Y(1+ε)^{K'}`.  `M₁` bounds `|∑_n c_n n^{2πiw}|²` on `|w| ≤ W` — the cancellation
input — and `M₂` bounds it everywhere.

This is the form `MaximalWindowMeanSquare` consumes after the Rademacher–Menshov reduction of
`MaximalWindowDyadic`: a plain sum of squares of fixed-length window sums over consecutive integer
starting points.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The linear window sum, as a sum of indicators of the admissible starting points. -/
theorem measurable_linSum (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) : Measurable (linSum a s L) := by
  classical
  have heq : linSum a s L
      = fun x => ∑ n ∈ s,
          (Set.indicator (Set.Ico ((n : ℝ) - L) (n : ℝ)) (fun _ => (1 : ℝ)) x) • a n := by
    funext x
    rw [linSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcnd : x < (n : ℝ) ∧ (n : ℝ) ≤ x + L
    · have hmem : x ∈ Set.Ico ((n : ℝ) - L) (n : ℝ) := by
        rw [Set.mem_Ico]
        exact ⟨by linarith [hcnd.2], hcnd.1⟩
      rw [if_pos hcnd, Set.indicator_of_mem hmem, one_smul]
    · have hnot : x ∉ Set.Ico ((n : ℝ) - L) (n : ℝ) := by
        intro hmem
        rw [Set.mem_Ico] at hmem
        exact hcnd ⟨hmem.2, by linarith [hmem.1]⟩
      rw [if_neg hcnd, Set.indicator_of_notMem hnot, zero_smul]
  rw [heq]
  refine Finset.measurable_sum _ fun n _ => ?_
  exact ((measurable_one.indicator measurableSet_Ico).smul_const (a n))

theorem norm_linSum_le (a : ℕ → ℂ) (s : Finset ℕ) (L x : ℝ) :
    ‖linSum a s L x‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  classical
  rw [linSum]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro n _ _
  exact norm_nonneg _

/-- **The mean square of a linear window sum is integrable on every set of finite measure.** -/
theorem integrableOn_normSq_linSum (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) {E : Set ℝ}
    (hE : volume E ≠ ⊤) :
    IntegrableOn (fun x : ℝ => ‖linSum a s L x‖ ^ (2 : ℕ)) E := by
  classical
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖linSum a s L x‖ ^ (2 : ℕ))
      (volume.restrict E) :=
    (((measurable_linSum a s L).norm.pow_const 2)).aestronglyMeasurable
  refine Integrable.mono' (g := fun _ : ℝ => (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ))
    (integrableOn_const hE (by finiteness)) hmeas ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (linSum a s L x), norm_linSum_le a s L x]

/-- The real window, with the index set written as `Icc 1 M`. -/
theorem realWindow_eq_filter_Icc {x : ℝ} (hx : 0 ≤ x) (L M : ℕ) :
    realWindow x L (M + 1)
      = (Finset.Icc 1 M).filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L) := by
  classical
  ext n
  simp only [realWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hlt, h1, h2⟩
    refine ⟨⟨?_, by omega⟩, h1, h2⟩
    by_contra hc
    have hn0 : n = 0 := by omega
    rw [hn0] at h1
    simp at h1
    linarith
  · rintro ⟨⟨-, hle⟩, h1, h2⟩
    exact ⟨by omega, h1, h2⟩

/-- The real-window sum is the corpus's linear window sum at the index set `Icc 1 M`. -/
theorem sum_realWindow_eq_linSum (c : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) (L M : ℕ) :
    ∑ n ∈ realWindow x L (M + 1), c n = linSum c (Finset.Icc 1 M) (L : ℝ) x := by
  rw [realWindow_eq_filter_Icc hx L M, linSum]

/-- **The discrete short-interval mean square, bounded through Gallagher's lemma.** -/
theorem sum_normSq_window_le_gallagher (c : ℕ → ℂ) (hc : ∀ n : ℕ, ‖c n‖ ≤ 1)
    {L Y K M K' : ℕ} {ε M₁ M₂ W : ℝ}
    (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hM : Y + K + L < M + 1)
    (hcover : (Y : ℝ) + (K : ℝ) ≤ (Y : ℝ) * (1 + ε) ^ K')
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly c (Finset.Icc 1 M) w‖ ^ (2 : ℕ) ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly c (Finset.Icc 1 M) w‖ ^ (2 : ℕ) ≤ M₂) :
    ∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), c n‖ ^ (2 : ℕ)
      ≤ ((Y : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε M₁ M₂ W) := by
  classical
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  set s : Finset ℕ := Finset.Icc 1 M with hs
  have hspos : ∀ n ∈ s, 0 < n := by
    intro n hn
    rw [hs, Finset.mem_Icc] at hn
    omega
  -- the discrete mean square is an interval integral
  have hdisc := integral_realWindow_eq_sum c L Y K (M + 1) hM
  -- rewrite the integrand as the corpus's linear window sum
  have hcongr : (∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖∑ n ∈ realWindow x L (M + 1), c n‖ ^ (2 : ℕ))
      = ∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro x hx
    rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_of_lt_of_le hY0 hx.1.le)
    show ‖∑ n ∈ realWindow x L (M + 1), c n‖ ^ (2 : ℕ) = ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ)
    rw [sum_realWindow_eq_linSum c hx0 L M]
  -- pass to a set integral and enlarge the range
  have hnonneg : ∀ x : ℝ, (0 : ℝ) ≤ ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ) := fun x => by positivity
  have hsub : Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ))
      ⊆ Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K') :=
    Set.Ioc_subset_Ioc_right hcover
  have hbig : IntegrableOn (fun x : ℝ => ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ))
      (Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K')) :=
    integrableOn_normSq_linSum c s (L : ℝ) measure_Ioc_lt_top.ne
  have hmono : (∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ))
      ≤ ∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K'), ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ) := by
    refine setIntegral_mono_set hbig ?_ (LE.le.eventuallyLE hsub)
    exact Filter.Eventually.of_forall hnonneg
  have hIval : (∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ))
      = ∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_of_le (by linarith)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hfinal := integral_Ioc_normSq_linSum_range_le c s hspos hc hLR hY0 hε hW hM₁ hM₂ h₁ h₂ K'
  rw [← hdisc, hcongr, hIval]
  exact le_trans hmono hfinal

end RHTower.Sieve

end
