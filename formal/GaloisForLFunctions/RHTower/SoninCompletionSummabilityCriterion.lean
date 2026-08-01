import GaloisForLFunctions.RHTower.SoninCompletionEnergyThreshold

/-!
# Exactly when a completion restores the floor

A completion contributing a possibly different amount at each scale turns the packet channel into
the finite sums of one real sequence: the contribution at that scale minus its coupling energy.
Finite sums of a real sequence are bounded below exactly when the sequence's negative part is
summable, so the completed channel has a lower floor exactly when the coupling energy exceeds the
contribution by a summable amount.

This replaces the terminal disjunction by a summability condition on one explicit sequence.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap Filter

/-- **Finite sums are bounded below exactly when the negative part is summable.** -/
theorem bddBelow_finsetSum_iff_summable_min_zero (f : ℕ → ℝ) :
    (∃ M : ℝ, ∀ s : Finset ℕ, M ≤ ∑ i ∈ s, f i) ↔ Summable fun i => min (f i) 0 := by
  classical
  constructor
  · rintro ⟨M, hM⟩
    have hg : Summable fun i => -min (f i) 0 := by
      refine summable_of_sum_range_le (c := -M) (fun i => ?_) (fun n => ?_)
      · simp only [neg_nonneg]
        exact min_le_right _ _
      · have hkey : ∑ i ∈ Finset.range n, min (f i) 0 =
            ∑ i ∈ (Finset.range n).filter (fun i => f i < 0), f i := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : f i < 0
          · simp [h, min_eq_left h.le]
          · simp [h, min_eq_right (not_lt.mp h)]
        have hbound := hM ((Finset.range n).filter (fun i => f i < 0))
        rw [← hkey] at hbound
        rw [Finset.sum_neg_distrib]
        linarith
    simpa using hg.neg
  · intro hsum
    refine ⟨-∑' i, -min (f i) 0, fun s => ?_⟩
    have hnn : ∀ i, 0 ≤ -min (f i) 0 := fun i => by
      simp only [neg_nonneg]
      exact min_le_right _ _
    have hle : ∑ i ∈ s, -min (f i) 0 ≤ ∑' i, -min (f i) 0 :=
      Summable.sum_le_tsum s (fun i _ => hnn i) hsum.neg
    have h2 : ∑ i ∈ s, min (f i) 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_le_sum fun i _ => min_le_left _ _
    rw [Finset.sum_neg_distrib] at hle
    linarith

/-- The unit-weight packet curvature trace corrected by a scale-dependent contribution. -/
def soninCompletedPacketValueVar (s : Finset ℕ) (a b c : ℝ) (p : ℕ → ℝ) (hp : ∀ i, 1 < p i)
    (κ : ℕ → ℝ) : ℝ :=
  (opTrace (soninAperturePacketCurvature s a b c p hp (fun _ => 1))).re + ∑ i ∈ s, κ i

/-- **Per-scale form** for a scale-dependent contribution. -/
theorem soninCompletedPacketValueVar_eq_sum
    (s : Finset ℕ) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i ∈ s, c < p i * a) (κ : ℕ → ℝ) :
    soninCompletedPacketValueVar s a b c p hp κ =
      ∑ i ∈ s, (κ i - hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) := by
  rw [soninCompletedPacketValueVar,
    re_opTrace_soninAperturePacketCurvature s ha hab hbc p hp _ hcp, Finset.sum_sub_distrib]
  have hone : ∑ i ∈ s, (1 : ℝ) * hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) =
      ∑ i ∈ s, hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) :=
    Finset.sum_congr rfl fun i _ => one_mul _
  rw [hone]
  ring

/-- **The exact criterion.**  A scale-dependent completion restores the lower floor exactly when
the amount by which the coupling energy exceeds it is summable over the scales. -/
theorem bddBelow_soninCompletedPacketValueVar_iff
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i, c < p i * a) (κ : ℕ → ℝ) :
    (∃ M : ℝ, ∀ s : Finset ℕ, M ≤ soninCompletedPacketValueVar s a b c p hp κ) ↔
      Summable fun i => min (κ i - hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0 := by
  have hcongr : ∀ s : Finset ℕ, soninCompletedPacketValueVar s a b c p hp κ =
      ∑ i ∈ s, (κ i - hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) :=
    fun s => soninCompletedPacketValueVar_eq_sum s ha hab hbc p hp (fun i _ => hcp i) κ
  constructor
  · rintro ⟨M, hM⟩
    refine (bddBelow_finsetSum_iff_summable_min_zero _).mp ⟨M, fun s => ?_⟩
    rw [← hcongr s]
    exact hM s
  · intro hsum
    obtain ⟨M, hM⟩ := (bddBelow_finsetSum_iff_summable_min_zero _).mpr hsum
    refine ⟨M, fun s => ?_⟩
    rw [hcongr s]
    exact hM s

/-- **The floor forces the completion to track the energy.**  If the completion restores the
floor, the excess of the coupling energy over it tends to zero along the scales. -/
theorem tendsto_min_sub_hsNormSq_of_bddBelow
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i, c < p i * a) (κ : ℕ → ℝ)
    (hfloor : ∃ M : ℝ, ∀ s : Finset ℕ, M ≤ soninCompletedPacketValueVar s a b c p hp κ) :
    Tendsto (fun i => min (κ i - hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0)
      atTop (nhds 0) :=
  ((bddBelow_soninCompletedPacketValueVar_iff ha hab hbc p hp hcp κ).mp hfloor).tendsto_atTop_zero

/-- **Growing coupling energy defeats every bounded completion.**  If the coupling energy grows
without bound along the scales, no completion bounded above on them restores the floor. -/
theorem not_bddBelow_of_tendsto_hsNormSq_atTop
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i, c < p i * a) (κ : ℕ → ℝ)
    (M₀ : ℝ) (hκ : ∀ i, κ i ≤ M₀)
    (henergy : Tendsto (fun i => hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) atTop atTop) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ, M ≤ soninCompletedPacketValueVar s a b c p hp κ := by
  intro hfloor
  have hzero := tendsto_min_sub_hsNormSq_of_bddBelow ha hab hbc p hp hcp κ hfloor
  have hbig : ∀ᶠ i in atTop, M₀ + 1 ≤ hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) :=
    henergy.eventually_ge_atTop (M₀ + 1)
  have hsmall : ∀ᶠ i in atTop, (-1 : ℝ) / 2 < min (κ i - hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0 :=
    hzero.eventually_const_lt (by norm_num)
  obtain ⟨i, hi1, hi2⟩ := (hbig.and hsmall).exists
  have hmin := min_le_left (κ i - hsNormSq
    (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0
  have hki := hκ i
  linarith

end RHTower
