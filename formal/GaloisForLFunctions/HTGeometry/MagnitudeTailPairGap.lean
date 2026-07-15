import GaloisForLFunctions.HTGeometry.MagnitudeDistinctSurvival

/-!
# Tail valuation gaps from one-sided support

For the log-superlacunary magnitude argument, the selected minimal atom is supported in a high
tail, but a competing atom need not agree with it below that tail.  Equal total degree is enough:
if the atoms differ, they must differ at some tail index.  The top differing index therefore lies
where the super-increasing estimate is available.
-/

open Finset

namespace GaloisForLFunctions

/-- Two bounded multi-indices whose difference occurs at or above `T` have a valuation gap governed
by a top differing index `K ≥ T`.  Unlike `finsupp_pair_valuation_gap_tail`, no agreement below `T`
is required. -/
theorem finsupp_pair_valuation_gap_of_diff_ge {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {D T : ℕ}
    (hsi : ∀ k, T ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D)
    (hdiff : ∃ n, T ≤ n ∧ ν n ≠ ν' n) :
    ∃ K : ℕ, T ≤ K ∧ b K / ((D : ℝ) + 1)
      ≤ |ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n)| := by
  classical
  set g : ℕ →₀ ℤ := ν.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero
    - ν'.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero with hg
  have hgn : ∀ n, g n = (ν n : ℤ) - (ν' n : ℤ) := by
    intro n
    rw [hg]
    simp [Finsupp.sub_apply, Finsupp.mapRange_apply]
  have hgbound : ∀ n, (g n).natAbs ≤ D := by
    intro n
    rw [hgn]
    have h1 := hν n
    have h2 := hν' n
    omega
  have hg0 : g ≠ 0 := by
    obtain ⟨n, _, hn⟩ := hdiff
    intro h0
    have := hgn n
    rw [h0] at this
    simp at this
    exact hn (by omega)
  have hne0 := Finsupp.support_nonempty_iff.mpr hg0
  set K := g.support.max' hne0 with hKdef
  have hKge : T ≤ K := by
    obtain ⟨n, hnT, hn⟩ := hdiff
    have hnmem : n ∈ g.support := by
      rw [Finsupp.mem_support_iff, hgn]
      exact sub_ne_zero.mpr (by exact_mod_cast hn)
    exact le_trans hnT (Finset.le_max' _ _ hnmem)
  have hval : ∑ n ∈ g.support, (g n : ℝ) * b n
      = ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n) := by
    rw [Finsupp.sum, Finsupp.sum]
    have hsupp : g.support ⊆ ν.support ∪ ν'.support := by
      intro n hn
      rw [Finsupp.mem_support_iff, hgn] at hn
      simp only [Finset.mem_union, Finsupp.mem_support_iff]
      by_cases hνn : ν n = 0
      · right
        intro hν'n
        rw [hνn, hν'n] at hn
        simp at hn
      · exact Or.inl hνn
    rw [Finset.sum_subset
      (Finset.subset_union_left (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset
      (Finset.subset_union_right (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset hsupp (fun n _ hn => by
      rw [Finsupp.notMem_support_iff.mp hn]
      simp), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [hgn]
    push_cast
    ring
  have hgap := valuation_gap_of_hsi_at_max hb hgbound hg0 (hsi K hKge)
  exact ⟨K, hKge, by rw [← hval]; exact hgap⟩

/-- Equal-count atoms differ in the high tail whenever the second atom is tail-supported.  Hence
their valuations inherit the tail super-increasing gap without any condition on the competitor's
low-index support. -/
theorem finsupp_pair_valuation_gap_of_count_eq_tailSupport {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) {D T : ℕ}
    (hsi : ∀ k, T ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D)
    (hcount : (ν.sum fun _ k => k) = ν'.sum fun _ k => k)
    (hν'tail : ∀ n, ν' n ≠ 0 → T ≤ n) (hne : ν ≠ ν') :
    ∃ K : ℕ, T ≤ K ∧ b K / ((D : ℝ) + 1)
      ≤ |ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n)| := by
  apply finsupp_pair_valuation_gap_of_diff_ge hb hsi hν hν'
  exact exists_diff_ge_of_count_eq hcount hν'tail hne

/-- Directed form for a selected valuation minimizer.  Equal count and one-sided tail support turn
the absolute pair gap into a lower bound above the minimizer. -/
theorem valuation_gap_above_min_of_count_eq_tailSupport {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) {D T : ℕ}
    (hsi : ∀ k, T ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν₀ : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν₀ : ∀ n, ν₀ n ≤ D)
    (hcount : (ν.sum fun _ k => k) = ν₀.sum fun _ k => k)
    (hν₀tail : ∀ n, ν₀ n ≠ 0 → T ≤ n) (hne : ν ≠ ν₀)
    (hmin : ν₀.sum (fun n k => (k : ℝ) * b n) ≤
      ν.sum (fun n k => (k : ℝ) * b n)) :
    ∃ K : ℕ, T ≤ K ∧
      ν₀.sum (fun n k => (k : ℝ) * b n) + b K / ((D : ℝ) + 1) ≤
        ν.sum (fun n k => (k : ℝ) * b n) := by
  obtain ⟨K, hKT, hgap⟩ :=
    finsupp_pair_valuation_gap_of_count_eq_tailSupport hb hsi hν hν₀ hcount hν₀tail hne
  refine ⟨K, hKT, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hmin)] at hgap
  linarith

/-- If the competitor has strictly smaller total count than a tail-supported atom, the two atoms
must differ at a tail index.  Agreement throughout the tail would leave the competitor with the
same high count plus a nonnegative low count. -/
theorem exists_diff_ge_of_count_lt_tailSupport {ν ν₀ : ℕ →₀ ℕ} {T : ℕ}
    (hcount : ν.sum (fun _ k => k) < ν₀.sum (fun _ k => k))
    (hν₀tail : ∀ n, ν₀ n ≠ 0 → T ≤ n) :
    ∃ n, T ≤ n ∧ ν n ≠ ν₀ n := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hν₀low : ∀ n, n < T → ν₀ n = 0 := fun n hn => by
    by_contra hne
    exact absurd (hν₀tail n hne) (not_le.mpr hn)
  let U := ν.support ∪ ν₀.support
  have hνsum : ν.sum (fun _ k => k) = ∑ n ∈ U, ν n := by
    rw [Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_left
      (fun n _ hn => Finsupp.notMem_support_iff.mp hn)
  have hν₀sum : ν₀.sum (fun _ k => k) = ∑ n ∈ U, ν₀ n := by
    rw [Finsupp.sum]
    exact Finset.sum_subset Finset.subset_union_right
      (fun n _ hn => Finsupp.notMem_support_iff.mp hn)
  have hhigh :
      ∑ n ∈ U.filter (fun n => ¬ n < T), ν n =
        ∑ n ∈ U.filter (fun n => ¬ n < T), ν₀ n :=
    Finset.sum_congr rfl fun n hn => by
      rw [Finset.mem_filter] at hn
      exact hcon n (not_lt.mp hn.2)
  have hlow₀ : ∑ n ∈ U.filter (fun n => n < T), ν₀ n = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [Finset.mem_filter] at hn
      exact hν₀low n hn.2
  have esplit := Finset.sum_filter_add_sum_filter_not U (fun n => n < T) ν
  have esplit₀ := Finset.sum_filter_add_sum_filter_not U (fun n => n < T) ν₀
  rw [hνsum, hν₀sum, ← esplit, ← esplit₀, hlow₀, hhigh] at hcount
  omega

/-- Directed valuation gap above a tail-supported minimizer when the competitor has smaller total
count. -/
theorem valuation_gap_above_min_of_count_lt_tailSupport {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) {D T : ℕ}
    (hsi : ∀ k, T ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν₀ : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν₀ : ∀ n, ν₀ n ≤ D)
    (hcount : ν.sum (fun _ k => k) < ν₀.sum (fun _ k => k))
    (hν₀tail : ∀ n, ν₀ n ≠ 0 → T ≤ n)
    (hmin : ν₀.sum (fun n k => (k : ℝ) * b n) ≤
      ν.sum (fun n k => (k : ℝ) * b n)) :
    ∃ K : ℕ, T ≤ K ∧
      ν₀.sum (fun n k => (k : ℝ) * b n) + b K / ((D : ℝ) + 1) ≤
        ν.sum (fun n k => (k : ℝ) * b n) := by
  obtain ⟨k, hkT, hk⟩ := exists_diff_ge_of_count_lt_tailSupport hcount hν₀tail
  obtain ⟨K, hKT, hgap⟩ :=
    finsupp_pair_valuation_gap_of_diff_ge hb hsi hν hν₀ ⟨k, hkT, hk⟩
  refine ⟨K, hKT, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hmin)] at hgap
  linarith

end GaloisForLFunctions
