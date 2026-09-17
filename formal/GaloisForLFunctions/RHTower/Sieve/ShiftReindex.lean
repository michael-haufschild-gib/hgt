import Mathlib

/-!
# Reindexing a pair sum by the shift

The strictly upper triangular pairs `n < m < R` are parametrised by the shift `h = m - n`:

`∑_{n < m < R} F(n,m) = ∑_{1 ≤ h < R} ∑_{n < R - h} F(n, n+h)`,

the bijection being `(n,m) ↦ (m-n, n)` with inverse `(h,n) ↦ (n, n+h)`.  Combined with the
trichotomy split of a symmetric pair sum into its diagonal and two triangles, this turns any
pair sum into a diagonal term plus a sum of *shifted correlations* — the form in which a
short-interval variance is actually estimated.
-/

namespace RHTower.Sieve

open Finset

/-- **Reindexing the upper triangle by the shift.** -/
theorem sum_upper_triangle_eq_sum_shift (R : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then F n m else 0)
      = ∑ h ∈ Finset.Ico 1 R, ∑ n ∈ Finset.range (R - h), F n (n + h) := by
  classical
  have hfilter : ∀ n, ∑ m ∈ Finset.range R, (if n < m then F n m else 0)
      = ∑ m ∈ (Finset.range R).filter (fun m => n < m), F n m := by
    intro n
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun n _ => hfilter n, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2 - x.1, x.1⟩) (fun y => ⟨y.2, y.2 + y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    omega
  · rintro ⟨h, n⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hy ⊢
    omega
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
    have : n + (m - n) = m := by omega
    simp [this]
  · rintro ⟨h, n⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hy
    simp
  · rintro ⟨n, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hx
    have : n + (m - n) = m := by omega
    simp [this]

/-- **Reindexing a strict dyadic interval triangle by the literal shift.**

The ordered pair `(u, a)` ranges over `N < a < u ≤ 2N`; it is sent to
`(u - a, a)`.  Thus no endpoint is averaged or completed: shift `h` retains
the exact inner interval `N < a ≤ 2N - h`. -/
theorem sum_strict_ioc_eq_sum_shift (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ ab ∈ (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N)) |>.filter
        (fun ab => ab.2 < ab.1), F ab.1 ab.2) =
      ∑ h ∈ Finset.Ico 1 N, ∑ a ∈ Finset.Ioc N (2 * N - h), F (a + h) a := by
  let S := Finset.Ioc N (2 * N)
  let G : ℕ × ℕ → ℝ := fun ab => F ab.1 ab.2
  let T := Finset.sigma (Finset.Ico 1 N) (fun h => Finset.Ioc N (2 * N - h))
  change (∑ ab ∈ (S.product S).filter (fun ab => ab.2 < ab.1), G ab) =
    ∑ h ∈ Finset.Ico 1 N, ∑ a ∈ Finset.Ioc N (2 * N - h), G (a + h, a)
  rw [Finset.sum_sigma']
  change (∑ ab ∈ (S.product S).filter (fun ab => ab.2 < ab.1), G ab) =
    ∑ ha ∈ T, G (ha.2 + ha.1, ha.2)
  refine Finset.sum_nbij' (fun ab : ℕ × ℕ => Sigma.mk (ab.1 - ab.2) ab.2)
    (fun ha : Sigma fun _ : ℕ => ℕ => (ha.2 + ha.1, ha.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, a⟩ hmem
    have hm : (u ∈ S ∧ a ∈ S) ∧ a < u := by
      simpa [S] using hmem
    have hu : N < u ∧ u ≤ 2 * N := by simpa [S] using hm.1.1
    have ha : N < a ∧ a ≤ 2 * N := by simpa [S] using hm.1.2
    have hua : a + (u - a) = u := Nat.add_sub_of_le (Nat.le_of_lt hm.2)
    change Sigma.mk (u - a) a ∈
      Finset.sigma (Finset.Ico 1 N) (fun h => Finset.Ioc N (2 * N - h))
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_Ico.mpr ?_, Finset.mem_Ioc.mpr ?_⟩
    · refine ⟨Nat.succ_le_iff.mpr (Nat.sub_pos_iff_lt.mpr hm.2), ?_⟩
      exact (Nat.sub_lt_iff_lt_add (Nat.le_of_lt hm.2)).mpr (by omega)
    · refine ⟨ha.1, Nat.le_sub_of_add_le ?_⟩
      simpa [hua] using hu.2
  · rintro ⟨h, a⟩ hmem
    have hm : (1 ≤ h ∧ h < N) ∧ N < a ∧ a ≤ 2 * N - h := by
      simpa [T] using hmem
    change (a + h, a) ∈ (S.product S).filter (fun ab => ab.2 < ab.1)
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by omega⟩
    · simpa [S] using (Finset.mem_Ioc.mpr (show N < a + h ∧ a + h ≤ 2 * N by omega))
    · simpa [S] using (Finset.mem_Ioc.mpr (show N < a ∧ a ≤ 2 * N by omega))
  · rintro ⟨u, a⟩ hmem
    have hm : (u ∈ S ∧ a ∈ S) ∧ a < u := by
      simpa [S] using hmem
    have hua : a + (u - a) = u := by omega
    dsimp
    simp [hua]
  · rintro ⟨h, a⟩ _
    dsimp
    apply Sigma.ext
    · simp
    · rfl
  · rintro ⟨u, a⟩ hmem
    have hua : a + (u - a) = u := by
      have hm : (u ∈ S ∧ a ∈ S) ∧ a < u := by
        simpa [S] using hmem
      omega
    change G (u, a) = G (a + (u - a), a)
    rw [hua]

/-- **Trichotomy split of a symmetric pair sum.** -/
theorem sum_pair_eq_diag_add_two_upper (R : ℕ) (W : ℕ → ℕ → ℝ)
    (hsymm : ∀ n m, W n m = W m n) :
    ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, W n m
      = ∑ n ∈ Finset.range R, W n n
        + 2 * ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
  classical
  have hsplit : ∀ n m : ℕ, W n m = (if n = m then W n m else 0) + (if n < m then W n m else 0)
      + (if m < n then W n m else 0) := by
    intro n m
    rcases lt_trichotomy n m with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring
  have hdiag : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n = m then W n m else 0)
      = ∑ n ∈ Finset.range R, W n n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_ite_eq (Finset.range R) n (fun m => W n m), if_pos hn]
  have hlower : ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if m < n then W n m else 0)
      = ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    by_cases h : n < m
    · rw [if_pos h, if_pos h, hsymm]
    · rw [if_neg h, if_neg h]
  calc ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, W n m
      = ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R,
          ((if n = m then W n m else 0) + (if n < m then W n m else 0)
            + (if m < n then W n m else 0)) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hsplit n m
    _ = ∑ n ∈ Finset.range R, W n n
        + 2 * ∑ n ∈ Finset.range R, ∑ m ∈ Finset.range R, (if n < m then W n m else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [hdiag, hlower]
        ring

end RHTower.Sieve
