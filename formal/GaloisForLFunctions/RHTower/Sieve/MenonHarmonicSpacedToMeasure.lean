import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicIntervalCovering

/-!
# From a spaced-family count to a measure

Huxley's large-values estimate
(`Sieve/PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet`) bounds the cardinality of a
**one-spaced finite family** inside a level set.  The receivers of this chain consume a measure.
This file is the bridge.

Partition the window into intervals of length `delta`; the set is covered by the ones it meets
(`measureReal_le_of_subset_biUnion_Ico`); choosing one point of the set in each meeting interval and
splitting the indices into even and odd gives two `delta`-spaced families, so the number of meeting
intervals is at most twice the spaced-family bound.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The `delta`-mesh interval of index `i` in the window of radius `W`. -/
def meshInterval (W delta : ℝ) (i : ℕ) : Set ℝ :=
  Set.Ico (-W + (i : ℝ) * delta) (-W + ((i : ℝ) + 1) * delta)

/-- **A spaced-family bound gives a measure bound.** -/
theorem measureReal_le_of_spaced_card_le
    {E : Set ℝ} {W R delta : ℝ} (_hW : 0 ≤ W) (hdelta : 0 < delta)
    (hEs : E ⊆ Set.Icc (-W) W)
    (hR : ∀ P : Finset ℝ, (∀ x ∈ P, ∀ y ∈ P, x ≠ y → delta ≤ |x - y|) →
      (∀ x ∈ P, x ∈ E) → (P.card : ℝ) ≤ R) :
    volume.real E ≤ 2 * R * delta := by
  classical
  have hdne : delta ≠ 0 := ne_of_gt hdelta
  have hcov : E ⊆ ⋃ i ∈ (Finset.range (⌈2 * W / delta⌉₊ + 1)).filter
      (fun i => (E ∩ meshInterval W delta i).Nonempty), meshInterval W delta i := by
    intro x hx
    have hmem := Set.mem_Icc.1 (hEs hx)
    have hx0 : 0 ≤ (x + W) / delta := by
      have hxw : 0 ≤ x + W := by linarith [hmem.1]
      positivity
    have hlow : ((⌊(x + W) / delta⌋₊ : ℕ) : ℝ) ≤ (x + W) / delta := Nat.floor_le hx0
    have hhigh : (x + W) / delta < ((⌊(x + W) / delta⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h1 : ((⌊(x + W) / delta⌋₊ : ℕ) : ℝ) * delta ≤ x + W := by
      have := mul_le_mul_of_nonneg_right hlow hdelta.le
      rwa [div_mul_cancel₀ _ hdne] at this
    have h2 : x + W < (((⌊(x + W) / delta⌋₊ : ℕ) : ℝ) + 1) * delta := by
      have := mul_lt_mul_of_pos_right hhigh hdelta
      rwa [div_mul_cancel₀ _ hdne] at this
    have hxI : x ∈ meshInterval W delta ⌊(x + W) / delta⌋₊ := by
      rw [meshInterval, Set.mem_Ico]
      exact ⟨by linarith, by linarith⟩
    have hle : (x + W) / delta ≤ 2 * W / delta :=
      div_le_div_of_nonneg_right (by linarith [hmem.2]) hdelta.le
    have hfl : ⌊(x + W) / delta⌋₊ ≤ ⌊2 * W / delta⌋₊ := Nat.floor_le_floor hle
    have hfc : ⌊2 * W / delta⌋₊ ≤ ⌈2 * W / delta⌉₊ := Nat.floor_le_ceil _
    have hisub : ⌊(x + W) / delta⌋₊ ∈ (Finset.range (⌈2 * W / delta⌉₊ + 1)).filter
        (fun i => (E ∩ meshInterval W delta i).Nonempty) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ⟨x, hx, hxI⟩⟩
    exact Set.mem_biUnion hisub hxI
  have hmeas : volume.real E
      ≤ (((Finset.range (⌈2 * W / delta⌉₊ + 1)).filter
          (fun i => (E ∩ meshInterval W delta i).Nonempty)).card : ℝ) * delta :=
    measureReal_le_of_subset_biUnion_Ico hdelta.le hcov
  set s : Finset ℕ := (Finset.range (⌈2 * W / delta⌉₊ + 1)).filter
    (fun i => (E ∩ meshInterval W delta i).Nonempty) with hsdef
  have hchoice : ∀ i ∈ s, (E ∩ meshInterval W delta i).Nonempty := by
    intro i hi
    rw [hsdef, Finset.mem_filter] at hi
    exact hi.2
  set f : ℕ → ℝ := fun i =>
    if h : (E ∩ meshInterval W delta i).Nonempty then h.choose else 0 with hfdef
  have hfmem : ∀ i ∈ s, f i ∈ E ∩ meshInterval W delta i := by
    intro i hi
    rw [hfdef]
    simp only [dif_pos (hchoice i hi)]
    exact (hchoice i hi).choose_spec
  have hbounds : ∀ i ∈ s,
      -W + (i : ℝ) * delta ≤ f i ∧ f i < -W + ((i : ℝ) + 1) * delta := by
    intro i hi
    have := (hfmem i hi).2
    rw [meshInterval, Set.mem_Ico] at this
    exact this
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i + 2 ≤ j → delta ≤ |f i - f j| := by
    intro i hi j hj hij
    have hbi := hbounds i hi
    have hbj := hbounds j hj
    have hij' : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hij
    have hgap : delta ≤ f j - f i := by nlinarith [hbi.2, hbj.1, hdelta.le]
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ f j - f i)]
    exact hgap
  have hinj : ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j := by
    intro i hi j hj hfij
    by_contra hne
    have hbi := hbounds i hi
    have hbj := hbounds j hj
    rcases Nat.lt_or_ge i j with h | h
    · have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
      nlinarith [hbi.2, hbj.1, hdelta.le, hfij]
    · have hji : j < i := by omega
      have hc : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hji
      nlinarith [hbj.2, hbi.1, hdelta.le, hfij]
  have hclass : ∀ c : ℕ, (((s.filter (fun i => i % 2 = c)).image f).card : ℝ) ≤ R := by
    intro c
    refine hR _ ?_ ?_
    · intro x hx y hy hxy
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      have hi' := Finset.mem_filter.1 hi
      have hj' := Finset.mem_filter.1 hj
      have hij : i ≠ j := fun h => hxy (by rw [h])
      rcases Nat.lt_or_ge i j with h | h
      · exact hsep i hi'.1 j hj'.1 (by omega)
      · rw [abs_sub_comm]
        exact hsep j hj'.1 i hi'.1 (by omega)
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (hfmem i (Finset.mem_filter.1 hi).1).1
  have hcardclass : ∀ c : ℕ, ((s.filter (fun i => i % 2 = c)).card : ℝ) ≤ R := by
    intro c
    have hinj' : Set.InjOn f (s.filter (fun i => i % 2 = c)) := by
      intro i hi j hj hij
      exact hinj i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
    have hc := hclass c
    rwa [Finset.card_image_of_injOn hinj'] at hc
  have hsplit : s.card = (s.filter (fun i => i % 2 = 0)).card
      + (s.filter (fun i => i % 2 = 1)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hi
        rcases Nat.even_or_odd i with h | h
        · exact Or.inl ⟨hi, Nat.even_iff.1 h⟩
        · exact Or.inr ⟨hi, Nat.odd_iff.1 h⟩
      · rintro (⟨hi, -⟩ | ⟨hi, -⟩) <;> exact hi
    · rw [Finset.disjoint_left]
      rintro i hi hj
      have h0 := (Finset.mem_filter.1 hi).2
      have h1 := (Finset.mem_filter.1 hj).2
      omega
  have hcards : (s.card : ℝ) ≤ 2 * R := by
    rw [hsplit]
    push_cast
    linarith [hcardclass 0, hcardclass 1]
  calc volume.real E ≤ (s.card : ℝ) * delta := hmeas
    _ ≤ (2 * R) * delta := mul_le_mul_of_nonneg_right hcards hdelta.le
    _ = 2 * R * delta := by ring

end

end RHTower.Sieve
