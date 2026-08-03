import GaloisForLFunctions.RHTower.Sieve.WindowKernelExact

/-!
# The kernel is constant on the bulk of a shift

At shift `h ≤ L` the overlap kernel takes the constant value `L - h` for every start in the bulk
`L ≤ n`, `n + h ≤ X`:

`K(n, n+h) = L - h`.

Only the two boundary strips — fewer than `L` starts at each end — see a different value, and there
`K ≤ L`.  So a weighted correlation sum differs from `(L-h)` times the *unweighted* correlation sum
by at most `2L·L`, which is what lets a bound stated for `∑_n μ(n)μ(n+h)` (the form the literature
provides) be used in place of the weighted form.
-/

namespace RHTower.Sieve

open Finset

/-- **The kernel is constant on the bulk.** -/
theorem windowOverlap_bulk {X L h n : ℕ} (hL : L ≤ n) (hh : h ≤ L) (hn : n + h ≤ X) :
    windowOverlap X L n (n + h) = L - h := by
  have hd : Nat.dist n (n + h) = h := by
    rw [Nat.dist_eq_sub_of_le (Nat.le_add_right n h)]
    omega
  have hres := windowOverlap_eq_sub_dist (X := X) (L := L) (n := n) (m := n + h)
    hL (by omega) (by omega) hn (by rw [hd]; exact hh)
  rwa [hd] at hres

/-- The number of starts outside the bulk is at most `2L`. -/
theorem card_boundary_le (X L h : ℕ) :
    (((Finset.range (X + L + 1 - h)).filter
        (fun n => ¬ (L ≤ n ∧ n + h ≤ X))).card) ≤ 2 * L + 1 := by
  classical
  have hsub : (Finset.range (X + L + 1 - h)).filter (fun n => ¬ (L ≤ n ∧ n + h ≤ X))
      ⊆ Finset.range L ∪ Finset.Ico (X + 1 - h) (X + L + 1 - h) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hlt, hnot⟩ := hn
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    by_cases hnL : n < L
    · exact Or.inl hnL
    · refine Or.inr ⟨?_, hlt⟩
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_range, Nat.card_Ico]
  omega

/-- **The weighted correlation differs from the unweighted one by a boundary term.**  For
coefficients bounded by one, the kernel-weighted sum is `(L-h)` times the bulk sum up to `(2L+1)L`. -/
theorem abs_sum_kernel_sub_bulk_le {X L h : ℕ} (hh : h ≤ L) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    |∑ n ∈ Finset.range (X + L + 1 - h), ((windowOverlap X L n (n + h) : ℕ) : ℝ) * c n
        - ((L - h : ℕ) : ℝ)
          * ∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X), c n|
      ≤ ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ) := by
  classical
  set N := X + L + 1 - h with hN
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => L ≤ n ∧ n + h ≤ X)
    (fun n => ((windowOverlap X L n (n + h) : ℕ) : ℝ) * c n)
  have hbulk : ∑ n ∈ (Finset.range N).filter (fun n => L ≤ n ∧ n + h ≤ X),
      ((windowOverlap X L n (n + h) : ℕ) : ℝ) * c n
      = ((L - h : ℕ) : ℝ)
        * ∑ n ∈ (Finset.range N).filter (fun n => L ≤ n ∧ n + h ≤ X), c n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [windowOverlap_bulk hn.2.1 hh hn.2.2]
  have hbd : |∑ n ∈ (Finset.range N).filter (fun n => ¬ (L ≤ n ∧ n + h ≤ X)),
      ((windowOverlap X L n (n + h) : ℕ) : ℝ) * c n| ≤ ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ (Finset.range N).filter (fun n => ¬ (L ≤ n ∧ n + h ≤ X)),
        |((windowOverlap X L n (n + h) : ℕ) : ℝ) * c n| ≤ (L : ℝ) := by
      intro n _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hK : ((windowOverlap X L n (n + h) : ℕ) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast windowOverlap_le X L n (n + h)
      calc ((windowOverlap X L n (n + h) : ℕ) : ℝ) * |c n|
          ≤ ((windowOverlap X L n (n + h) : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hc n) (Nat.cast_nonneg _)
        _ = ((windowOverlap X L n (n + h) : ℕ) : ℝ) := by ring
        _ ≤ (L : ℝ) := hK
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((((Finset.range N).filter (fun n => ¬ (L ≤ n ∧ n + h ≤ X))).card : ℕ) : ℝ)
        ≤ ((2 * L + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_boundary_le X L h
    exact mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg L)
  rw [← hsplit, hbulk]
  simpa using hbd

end RHTower.Sieve
