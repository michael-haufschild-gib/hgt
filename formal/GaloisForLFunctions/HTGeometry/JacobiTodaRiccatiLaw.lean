import GaloisForLFunctions.HTGeometry.JacobiRiccatiTruncation

/-!
# The nonisospectral Toda system of a tridiagonal Riccati flow

A symmetric tridiagonal Jacobi matrix `J` with off-diagonal curve `a` and diagonal curve `b`, and
the skew tridiagonal connection `A` with `A_{k,k+1} = (k+1/2)a_{k+1}`, satisfy the nonisospectral
Lax equation

`J' = [J, A] - J^(2 : ℕ)`

precisely when the two coefficient curves obey the scalar system

`b_n' = 2(n-1)a_n^(2 : ℕ) - 2(n+1)a_{n+1}^(2 : ℕ) - b_n^(2 : ℕ)`,
`a_{n+1}' = a_{n+1}((n - 1/2)b_n - (n + 3/2)b_{n+1})`.

Both matrices are banded, so each entry of the Lax right side is a three-term sum, and the whole
identity reduces to a finite case analysis on the distance between the two indices.  Combined with
the one-level truncation identity, the finite compression therefore acquires exactly one rank-one
boundary source at the last diagonal entry.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Band entries -/

section Entries

variable (a b : ℕ → ℝ)

theorem jacobiEntry_diag (i : ℕ) : jacobiEntry a b i i = b i := by
  simp [jacobiEntry]

theorem jacobiEntry_succ (i : ℕ) : jacobiEntry a b i (i + 1) = a (i + 1) := by
  simp [jacobiEntry]

theorem jacobiEntry_succ' (i : ℕ) : jacobiEntry a b (i + 1) i = a (i + 1) := by
  have h2 : ¬ (i + 1 + 1 = i) := by omega
  simp [jacobiEntry, h2]

theorem jacobiEntry_of_lt {i j : ℕ} (h : i + 1 < j) : jacobiEntry a b i j = 0 := by
  have h1 : ¬ (i = j) := by omega
  have h2 : ¬ (i + 1 = j) := by omega
  have h3 : ¬ (j + 1 = i) := by omega
  simp [jacobiEntry, h1, h2, h3]

theorem jacobiEntry_of_gt {i j : ℕ} (h : j + 1 < i) : jacobiEntry a b i j = 0 := by
  have h1 : ¬ (i = j) := by omega
  have h2 : ¬ (i + 1 = j) := by omega
  have h3 : ¬ (j + 1 = i) := by omega
  simp [jacobiEntry, h1, h2, h3]

theorem connectionEntry_diag (i : ℕ) : connectionEntry a i i = 0 := by
  simp [connectionEntry]

theorem connectionEntry_succ (i : ℕ) :
    connectionEntry a i (i + 1) = ((i : ℝ) + 1 / 2) * a (i + 1) := by
  simp [connectionEntry]

theorem connectionEntry_succ' (i : ℕ) :
    connectionEntry a (i + 1) i = -(((i : ℝ) + 1 / 2) * a (i + 1)) := by
  have h1 : ¬ (i + 1 + 1 = i) := by omega
  simp [connectionEntry, h1]

theorem connectionEntry_of_lt {i j : ℕ} (h : i + 1 < j) : connectionEntry a i j = 0 := by
  have h1 : ¬ (i + 1 = j) := by omega
  have h2 : ¬ (j + 1 = i) := by omega
  simp [connectionEntry, h1, h2]

theorem connectionEntry_of_gt {i j : ℕ} (h : j + 1 < i) : connectionEntry a i j = 0 := by
  have h1 : ¬ (i + 1 = j) := by omega
  have h2 : ¬ (j + 1 = i) := by omega
  simp [connectionEntry, h1, h2]

end Entries

theorem jacobiEntry_symm (a b : ℕ → ℝ) (i j : ℕ) :
    jacobiEntry a b j i = jacobiEntry a b i j := by
  unfold jacobiEntry
  by_cases h : i = j
  · subst h; rfl
  · have h' : ¬ (j = i) := fun hh => h hh.symm
    by_cases h1 : i + 1 = j
    · have h2 : ¬ (j + 1 = i) := by omega
      simp [h, h', h1, h2]
    · by_cases h2 : j + 1 = i
      · simp [h, h', h1, h2]
      · simp [h, h', h1, h2]

theorem jacobiCompression_symm (a b : ℕ → ℝ) (n : ℕ) :
    (jacobiCompression a b n)ᵀ = jacobiCompression a b n := by
  ext i j
  simp only [Matrix.transpose_apply, jacobiCompression, Matrix.of_apply]
  exact jacobiEntry_symm a b i j

/-! ## The Lax right side, entry by entry -/

/-- One summand of the `(j,k)` entry of `JA - AJ - J²`. -/
def laxTerm (a b : ℕ → ℝ) (j k l : ℕ) : ℝ :=
  jacobiEntry a b j l * connectionEntry a l k - connectionEntry a j l * jacobiEntry a b l k
    - jacobiEntry a b j l * jacobiEntry a b l k

theorem laxTerm_of_lt (a b : ℕ → ℝ) (j k : ℕ) {l : ℕ} (h : j + 1 < l) :
    laxTerm a b j k l = 0 := by
  simp [laxTerm, jacobiEntry_of_lt a b h, connectionEntry_of_lt a h]

theorem laxTerm_of_gt (a b : ℕ → ℝ) (j k : ℕ) {l : ℕ} (h : l + 1 < j) :
    laxTerm a b j k l = 0 := by
  simp [laxTerm, jacobiEntry_of_gt a b h, connectionEntry_of_gt a h]

/-- The zeroth row of the Lax right side is a two-term sum. -/
theorem laxSum_zero (a b : ℕ → ℝ) (k N : ℕ) (hN : 2 ≤ N) :
    ∑ l ∈ Finset.range N, laxTerm a b 0 k l = laxTerm a b 0 k 0 + laxTerm a b 0 k 1 := by
  have hsub : Finset.range 2 ⊆ Finset.range N := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)
  have hzero : ∀ x ∈ Finset.range N, x ∉ Finset.range 2 → laxTerm a b 0 k x = 0 := by
    intro x _ hx
    exact laxTerm_of_lt a b 0 k (by simpa [Finset.mem_range] using hx)
  rw [← Finset.sum_subset hsub hzero]
  simp [Finset.sum_range_succ]

/-- Every later row of the Lax right side is a three-term sum. -/
theorem laxSum_succ (a b : ℕ → ℝ) (i k N : ℕ) (hN : i + 3 ≤ N) :
    ∑ l ∈ Finset.range N, laxTerm a b (i + 1) k l
      = laxTerm a b (i + 1) k i + laxTerm a b (i + 1) k (i + 1)
        + laxTerm a b (i + 1) k (i + 2) := by
  have hsub : Finset.range (i + 3) ⊆ Finset.range N := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)
  have hzero : ∀ x ∈ Finset.range N, x ∉ Finset.range (i + 3) → laxTerm a b (i + 1) k x = 0 := by
    intro x _ hx
    exact laxTerm_of_lt a b (i + 1) k (by simp only [Finset.mem_range, not_lt] at hx; omega)
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlow : ∑ l ∈ Finset.range i, laxTerm a b (i + 1) k l = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    exact laxTerm_of_gt a b (i + 1) k (by simp only [Finset.mem_range] at hl; omega)
  rw [hlow, zero_add]

/-! ## The scalar Toda system -/

/-- The two coefficient curves of a nonisospectral tridiagonal Riccati flow. -/
def JacobiTodaDeriv (a b a' b' : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧
    (∀ n : ℕ, b' n = 2 * ((n : ℝ) - 1) * a n ^ (2 : ℕ) - 2 * ((n : ℝ) + 1) * a (n + 1) ^ (2 : ℕ) - b n ^ (2 : ℕ)) ∧
    (∀ n : ℕ,
      a' (n + 1) = a (n + 1) * (((n : ℝ) - 1 / 2) * b n - ((n : ℝ) + 3 / 2) * b (n + 1)))

/-- **The Lax law, entrywise.**  If the two coefficient curves satisfy the nonisospectral Toda
system, then every entry of the derivative Jacobi matrix is the corresponding entry of
`JA - AJ - J²`, the sum being taken over any index range that covers both bands. -/
theorem laxSum_eq_jacobiEntry (a b a' b' : ℕ → ℝ) (h : JacobiTodaDeriv a b a' b')
    (N j k : ℕ) (hj : j + 2 ≤ N) (hk : k + 2 ≤ N) :
    ∑ l ∈ Finset.range N, laxTerm a b j k l = jacobiEntry a' b' j k := by
  obtain ⟨ha0, hb, ha⟩ := h
  match j with
  | 0 =>
    rw [laxSum_zero a b k N (by omega)]
    have hj00 : jacobiEntry a b 0 0 = b 0 := jacobiEntry_diag a b 0
    have hj01 : jacobiEntry a b 0 1 = a 1 := jacobiEntry_succ a b 0
    have hA00 : connectionEntry a 0 0 = 0 := connectionEntry_diag a 0
    have hA01 : connectionEntry a 0 1 = (1 / 2 : ℝ) * a 1 := by
      rw [connectionEntry_succ a 0]; norm_num
    have hrow : laxTerm a b 0 k 0 + laxTerm a b 0 k 1
        = b 0 * connectionEntry a 0 k - b 0 * jacobiEntry a b 0 k
          + (a 1 * connectionEntry a 1 k - (1 / 2 : ℝ) * a 1 * jacobiEntry a b 1 k
            - a 1 * jacobiEntry a b 1 k) := by
      simp only [laxTerm, hj00, hj01, hA00, hA01]
      ring
    rw [hrow]
    have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases hk4 with rfl | rfl | rfl | hk3
    · rw [hA00, hj00, connectionEntry_succ' a 0, jacobiEntry_succ' a b 0,
        jacobiEntry_diag a' b' 0, hb 0, ha0]
      norm_num
      ring
    · rw [hA01, hj01, connectionEntry_diag a 1, jacobiEntry_diag a b 1,
        jacobiEntry_succ a' b' 0, ha 0]
      norm_num
      ring
    · rw [connectionEntry_of_lt a (i := 0) (j := 2) (by omega),
        jacobiEntry_of_lt a b (i := 0) (j := 2) (by omega),
        connectionEntry_succ a 1, jacobiEntry_succ a b 1,
        jacobiEntry_of_lt a' b' (i := 0) (j := 2) (by omega)]
      norm_num
      ring
    · rw [connectionEntry_of_lt a (i := 0) (j := k) (by omega),
        jacobiEntry_of_lt a b (i := 0) (j := k) (by omega),
        connectionEntry_of_lt a (i := 1) (j := k) (by omega),
        jacobiEntry_of_lt a b (i := 1) (j := k) (by omega),
        jacobiEntry_of_lt a' b' (i := 0) (j := k) (by omega)]
      ring
  | (i + 1) =>
    rw [laxSum_succ a b i k N (by omega)]
    have hjs : jacobiEntry a b (i + 1) i = a (i + 1) := jacobiEntry_succ' a b i
    have hjd : jacobiEntry a b (i + 1) (i + 1) = b (i + 1) := jacobiEntry_diag a b (i + 1)
    have hju : jacobiEntry a b (i + 1) (i + 2) = a (i + 2) := jacobiEntry_succ a b (i + 1)
    have hAs : connectionEntry a (i + 1) i = -(((i : ℝ) + 1 / 2) * a (i + 1)) :=
      connectionEntry_succ' a i
    have hAd : connectionEntry a (i + 1) (i + 1) = 0 := connectionEntry_diag a (i + 1)
    have hAu : connectionEntry a (i + 1) (i + 2) = ((i : ℝ) + 1 + 1 / 2) * a (i + 2) := by
      rw [connectionEntry_succ a (i + 1)]; push_cast; ring
    have hrow : laxTerm a b (i + 1) k i + laxTerm a b (i + 1) k (i + 1)
          + laxTerm a b (i + 1) k (i + 2)
        = (a (i + 1) * connectionEntry a i k
            + ((i : ℝ) + 1 / 2) * a (i + 1) * jacobiEntry a b i k
            - a (i + 1) * jacobiEntry a b i k)
          + (b (i + 1) * connectionEntry a (i + 1) k - b (i + 1) * jacobiEntry a b (i + 1) k)
          + (a (i + 2) * connectionEntry a (i + 2) k
            - ((i : ℝ) + 1 + 1 / 2) * a (i + 2) * jacobiEntry a b (i + 2) k
            - a (i + 2) * jacobiEntry a b (i + 2) k) := by
      simp only [laxTerm, hjs, hjd, hju, hAs, hAd, hAu]
      ring
    rw [hrow]
    have hcase : k + 2 ≤ i ∨ k + 1 = i ∨ k = i ∨ k = i + 1 ∨ k = i + 2 ∨ k = i + 3 ∨ i + 4 ≤ k := by
      omega
    rcases hcase with hlow | hkm1 | rfl | rfl | rfl | rfl | hhigh
    · rw [connectionEntry_of_gt a (i := i) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := i) (j := k) (by omega),
        connectionEntry_of_gt a (i := i + 1) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := i + 1) (j := k) (by omega),
        connectionEntry_of_gt a (i := i + 2) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := i + 2) (j := k) (by omega),
        jacobiEntry_of_gt a' b' (i := i + 1) (j := k) (by omega)]
      ring
    · subst hkm1
      rw [connectionEntry_succ' a k, jacobiEntry_succ' a b k,
        connectionEntry_of_gt a (i := k + 1 + 1) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := k + 1 + 1) (j := k) (by omega),
        connectionEntry_of_gt a (i := k + 1 + 2) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := k + 1 + 2) (j := k) (by omega),
        jacobiEntry_of_gt a' b' (i := k + 1 + 1) (j := k) (by omega)]
      push_cast
      ring
    · rw [connectionEntry_diag a k, jacobiEntry_diag a b k,
        connectionEntry_succ' a k, jacobiEntry_succ' a b k,
        connectionEntry_of_gt a (i := k + 2) (j := k) (by omega),
        jacobiEntry_of_gt a b (i := k + 2) (j := k) (by omega),
        jacobiEntry_succ' a' b' k, ha k]
      ring
    · rw [connectionEntry_succ a i, jacobiEntry_succ a b i,
        connectionEntry_diag a (i + 1), jacobiEntry_diag a b (i + 1),
        connectionEntry_succ' a (i + 1), jacobiEntry_succ' a b (i + 1),
        jacobiEntry_diag a' b' (i + 1), hb (i + 1)]
      push_cast
      ring
    · rw [connectionEntry_of_lt a (i := i) (j := i + 2) (by omega),
        jacobiEntry_of_lt a b (i := i) (j := i + 2) (by omega),
        connectionEntry_succ a (i + 1), jacobiEntry_succ a b (i + 1),
        connectionEntry_diag a (i + 2), jacobiEntry_diag a b (i + 2),
        jacobiEntry_succ a' b' (i + 1), ha (i + 1)]
      push_cast
      ring
    · rw [connectionEntry_of_lt a (i := i) (j := i + 3) (by omega),
        jacobiEntry_of_lt a b (i := i) (j := i + 3) (by omega),
        connectionEntry_of_lt a (i := i + 1) (j := i + 3) (by omega),
        jacobiEntry_of_lt a b (i := i + 1) (j := i + 3) (by omega),
        connectionEntry_succ a (i + 2), jacobiEntry_succ a b (i + 2),
        jacobiEntry_of_lt a' b' (i := i + 1) (j := i + 3) (by omega)]
      push_cast
      ring
    · rw [connectionEntry_of_lt a (i := i) (j := k) (by omega),
        jacobiEntry_of_lt a b (i := i) (j := k) (by omega),
        connectionEntry_of_lt a (i := i + 1) (j := k) (by omega),
        jacobiEntry_of_lt a b (i := i + 1) (j := k) (by omega),
        connectionEntry_of_lt a (i := i + 2) (j := k) (by omega),
        jacobiEntry_of_lt a b (i := i + 2) (j := k) (by omega),
        jacobiEntry_of_lt a' b' (i := i + 1) (j := k) (by omega)]
      ring

/-! ## The finite compression -/

/-- The Lax right side of a compression, as a single sum over the index range. -/
theorem laxCompression_apply (a b : ℕ → ℝ) (N : ℕ) (x y : Fin N) :
    (jacobiCompression a b N * connectionCompression a N
        - connectionCompression a N * jacobiCompression a b N
        - jacobiCompression a b N * jacobiCompression a b N) x y
      = ∑ l ∈ Finset.range N, laxTerm a b x y l := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, jacobiCompression, connectionCompression,
    Matrix.of_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [← Fin.sum_univ_eq_sum_range (fun l => laxTerm a b x y l) N]
  rfl

/-- **The finite nonisospectral Riccati boundary law.**  A tridiagonal pair whose coefficient
curves satisfy the nonisospectral Toda system has, at every finite level `n = m+1`, the exact
compressed Riccati law with one negative rank-one boundary source of size `2n a_n²` at the last
diagonal entry. -/
theorem jacobiCompression_deriv_eq_riccati (a b a' b' : ℕ → ℝ) (h : JacobiTodaDeriv a b a' b')
    (m : ℕ) :
    jacobiCompression a' b' (m + 1)
      = jacobiCompression a b (m + 1) * connectionCompression a (m + 1)
        - connectionCompression a (m + 1) * jacobiCompression a b (m + 1)
        - jacobiCompression a b (m + 1) * jacobiCompression a b (m + 1)
        - (2 * ((m : ℝ) + 1) * a (m + 1) ^ (2 : ℕ)) •
            Matrix.vecMulVec (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0)
              (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0) := by
  rw [← jacobiCompression_riccati_matrix a b m]
  ext j k
  have hj : (j : ℕ) + 2 ≤ m + 2 := by have := j.isLt; omega
  have hk : (k : ℕ) + 2 ≤ m + 2 := by have := k.isLt; omega
  rw [Matrix.of_apply, laxCompression_apply a b (m + 2) j.castSucc k.castSucc]
  simpa only [Fin.val_castSucc, jacobiCompression, Matrix.of_apply] using
    (laxSum_eq_jacobiEntry a b a' b' h (m + 2) j k hj hk).symm

end GaloisForLFunctions.HTGeometry
