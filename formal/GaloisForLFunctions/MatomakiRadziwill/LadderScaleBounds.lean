import GaloisForLFunctions.MatomakiRadziwill.LadderMoment

/-!
# The two kinds of ladder steps

For continuous `Q_v, R_v` (`v ∈ V`) and thresholds `c_v > 0`, the frequencies where every `Q_v` is
small form the closed set `smallAt Q V c = {w : ∀ v ∈ V, |Q_v(w)| ≤ c_v}`.

* **First step** (`integral_indicator_small_le`): on `smallAt Q V c`,
  `|Σ_v Q_v R_v|² ≤ #V Σ_v c_v² |R_v|²`, so
  `∫_{|w|≤W} 1_{small} |Σ_v Q_v R_v|² ≤ #V Σ_v c_v² ∫_{|w|≤W} |R_v|²`.
* **Later steps** (`integral_indicator_small_not_small_le`): off `smallAt Q' U c'` some
  `|Q'_u| > c'_u`, so `1 ≤ Σ_u (|Q'_u|/c'_u)^{2ℓ(u,v)}` for any exponents `ℓ` (`one_le_sum_ratio_pow`);
  multiplying in this factor (the moment trick),
  `∫ 1_{small ∖ small'} |Σ_v Q_v R_v|² ≤ #V Σ_v Σ_u c_v² c'_u^{-2ℓ(u,v)} ∫ |Q'_u^{ℓ(u,v)} R_v|²`.
-/

open Finset MeasureTheory Set

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The frequencies where every `Q_v`, `v ∈ V`, is at most `c_v`. -/
def smallAt (Q : ℕ → ℝ → ℂ) (V : Finset ℕ) (c : ℕ → ℝ) : Set ℝ :=
  {w | ∀ v ∈ V, ‖Q v w‖ ≤ c v}

theorem isClosed_smallAt {Q : ℕ → ℝ → ℂ} (hQ : ∀ v, Continuous (Q v)) (V : Finset ℕ)
    (c : ℕ → ℝ) : IsClosed (smallAt Q V c) := by
  have : smallAt Q V c = ⋂ v ∈ V, {w | ‖Q v w‖ ≤ c v} := by
    ext w; simp [smallAt]
  rw [this]
  exact isClosed_biInter fun v _ => isClosed_le (hQ v).norm continuous_const

/-- On `smallAt`: `|Σ_v Q_v R_v|² ≤ #V Σ_v c_v² |R_v|²`. -/
theorem normSq_sum_le_of_small {Q R : ℕ → ℝ → ℂ} {V : Finset ℕ} {c : ℕ → ℝ} {w : ℝ}
    (hw : w ∈ smallAt Q V c) :
    ‖∑ v ∈ V, Q v w * R v w‖ ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, c v ^ 2 * ‖R v w‖ ^ 2 := by
  refine le_trans (normSq_sum_blocks_le (fun v => Q v w) (fun v => R v w)) ?_
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun v hv => ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw v hv) 2) (by positivity)

/-- **Off `smallAt` some ratio exceeds one**, so any sum of its even powers is at least one. -/
theorem one_le_sum_ratio_pow {Q : ℕ → ℝ → ℂ} {U : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ u ∈ U, 0 < c u)
    {w : ℝ} (hw : w ∉ smallAt Q U c) (ℓ : ℕ → ℕ) :
    1 ≤ ∑ u ∈ U, (‖Q u w‖ / c u) ^ (2 * ℓ u) := by
  simp only [smallAt, mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨u, hu, hlt⟩ := hw
  have hr : 1 ≤ ‖Q u w‖ / c u := by rw [le_div_iff₀ (hc u hu)]; linarith
  calc (1 : ℝ) ≤ (‖Q u w‖ / c u) ^ (2 * ℓ u) := one_le_pow₀ hr
    _ ≤ ∑ u ∈ U, (‖Q u w‖ / c u) ^ (2 * ℓ u) :=
        single_le_sum (f := fun u => (‖Q u w‖ / c u) ^ (2 * ℓ u))
          (fun u hu => pow_nonneg (div_nonneg (norm_nonneg _) (hc u hu).le) _) hu

theorem continuous_normSq_sum {Q R : ℕ → ℝ → ℂ} (hQ : ∀ v, Continuous (Q v))
    (hR : ∀ v, Continuous (R v)) (V : Finset ℕ) :
    Continuous fun w => ‖∑ v ∈ V, Q v w * R v w‖ ^ 2 :=
  ((continuous_finsetSum V fun v _ => (hQ v).mul (hR v)).norm).pow 2

/-- **The first ladder step.** -/
theorem integral_indicator_small_le {Q R : ℕ → ℝ → ℂ} (hR : ∀ v, Continuous (R v)) (V : Finset ℕ) (c : ℕ → ℝ) (W : ℝ) :
    (∫ w in Icc (-W) W, (smallAt Q V c).indicator (fun w => ‖∑ v ∈ V, Q v w * R v w‖ ^ 2) w)
      ≤ (V.card : ℝ) * ∑ v ∈ V, c v ^ 2 * ∫ w in Icc (-W) W, ‖R v w‖ ^ 2 := by
  have hint : ∀ v, IntegrableOn (fun w => ‖R v w‖ ^ 2) (Icc (-W) W) := fun v =>
    ((hR v).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmaj : IntegrableOn (fun w => (V.card : ℝ) * ∑ v ∈ V, c v ^ 2 * ‖R v w‖ ^ 2) (Icc (-W) W) :=
    (integrable_finsetSum V fun v _ => (hint v).const_mul _).const_mul _
  calc (∫ w in Icc (-W) W, (smallAt Q V c).indicator (fun w => ‖∑ v ∈ V, Q v w * R v w‖ ^ 2) w)
      ≤ ∫ w in Icc (-W) W, (V.card : ℝ) * ∑ v ∈ V, c v ^ 2 * ‖R v w‖ ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => ?_) hmaj
          (Filter.Eventually.of_forall fun w => ?_)
        · exact indicator_nonneg (fun w _ => by positivity) w
        · by_cases hw : w ∈ smallAt Q V c
          · rw [indicator_of_mem hw]; exact normSq_sum_le_of_small hw
          · rw [indicator_of_notMem hw]; positivity
    _ = (V.card : ℝ) * ∑ v ∈ V, c v ^ 2 * ∫ w in Icc (-W) W, ‖R v w‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum V fun v _ => (hint v).const_mul _]
        congr 1
        exact sum_congr rfl fun v _ => integral_const_mul _ _

/-- **A later ladder step (the moment trick).** -/
theorem integral_indicator_small_not_small_le {Q R Q' : ℕ → ℝ → ℂ}
    (hR : ∀ v, Continuous (R v)) (hQ' : ∀ u, Continuous (Q' u)) (V U : Finset ℕ) (c c' : ℕ → ℝ) (hc' : ∀ u ∈ U, 0 < c' u) (ℓ : ℕ → ℕ → ℕ) (W : ℝ) :
    (∫ w in Icc (-W) W, (smallAt Q V c ∩ (smallAt Q' U c')ᶜ).indicator
        (fun w => ‖∑ v ∈ V, Q v w * R v w‖ ^ 2) w)
      ≤ (V.card : ℝ) * ∑ v ∈ V, ∑ u ∈ U, c v ^ 2 / c' u ^ (2 * ℓ u v)
          * ∫ w in Icc (-W) W, ‖Q' u w ^ ℓ u v * R v w‖ ^ 2 := by
  have hint : ∀ u v, IntegrableOn (fun w => ‖Q' u w ^ ℓ u v * R v w‖ ^ 2) (Icc (-W) W) :=
    fun u v => ((((hQ' u).pow _).mul (hR v)).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  set G : ℝ → ℝ := fun w => (V.card : ℝ) * ∑ v ∈ V, ∑ u ∈ U, c v ^ 2 / c' u ^ (2 * ℓ u v)
    * ‖Q' u w ^ ℓ u v * R v w‖ ^ 2 with hG
  have hmaj : IntegrableOn G (Icc (-W) W) :=
    (integrable_finsetSum V fun v _ => integrable_finsetSum U fun u _ =>
      (hint u v).const_mul _).const_mul _
  have hpt : ∀ w ∈ smallAt Q V c ∩ (smallAt Q' U c')ᶜ, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2 ≤ G w := by
    intro w ⟨hs, hns⟩
    refine le_trans (normSq_sum_le_of_small hs) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine sum_le_sum fun v _ => ?_
    have h1 := one_le_sum_ratio_pow hc' hns (fun u => ℓ u v)
    have hnn : 0 ≤ c v ^ 2 * ‖R v w‖ ^ 2 := by positivity
    calc c v ^ 2 * ‖R v w‖ ^ 2 ≤ c v ^ 2 * ‖R v w‖ ^ 2 * ∑ u ∈ U, (‖Q' u w‖ / c' u) ^ (2 * ℓ u v) :=
          le_mul_of_one_le_right hnn h1
      _ = ∑ u ∈ U, c v ^ 2 / c' u ^ (2 * ℓ u v) * ‖Q' u w ^ ℓ u v * R v w‖ ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun u hu => ?_
          have hcu : c' u ≠ 0 := (hc' u hu).ne'
          rw [norm_mul, norm_pow, div_pow, mul_pow, ← pow_mul]
          field_simp
          ring
  calc (∫ w in Icc (-W) W, (smallAt Q V c ∩ (smallAt Q' U c')ᶜ).indicator
        (fun w => ‖∑ v ∈ V, Q v w * R v w‖ ^ 2) w)
      ≤ ∫ w in Icc (-W) W, G w := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => ?_) hmaj
          (Filter.Eventually.of_forall fun w => ?_)
        · exact indicator_nonneg (fun w _ => by positivity) w
        · by_cases hw : w ∈ smallAt Q V c ∩ (smallAt Q' U c')ᶜ
          · rw [indicator_of_mem hw]; exact hpt w hw
          · rw [indicator_of_notMem hw]
            simp only [hG]
            refine mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun v _ => sum_nonneg fun u hu => ?_)
            have := hc' u hu
            positivity
    _ = (V.card : ℝ) * ∑ v ∈ V, ∑ u ∈ U, c v ^ 2 / c' u ^ (2 * ℓ u v)
          * ∫ w in Icc (-W) W, ‖Q' u w ^ ℓ u v * R v w‖ ^ 2 := by
        simp only [hG]
        rw [integral_const_mul, integral_finsetSum V fun v _ => integrable_finsetSum U
          fun u _ => (hint u v).const_mul _]
        congr 1
        refine sum_congr rfl fun v _ => ?_
        rw [integral_finsetSum U fun u _ => (hint u v).const_mul _]
        exact sum_congr rfl fun u _ => integral_const_mul _ _

end

end GaloisForLFunctions.MatomakiRadziwill
