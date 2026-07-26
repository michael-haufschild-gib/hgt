/-
Weyl differencing for exponential sums.

The squaring step underlying the van der Corput `A` process.  For any `F : ℕ → ℂ`,

    ‖Σ_{n < N} F n‖² = Σ_{n < N} Σ_{m < N} F n · conj (F m),

and splitting the index square by comparison of the two coordinates and reindexing the strictly
upper part by the shift `h = n - m` gives

    ‖Σ_{n < N} F n‖² = Σ_{n < N} ‖F n‖² + 2 · Re ( Σ_{h=1}^{N-1} diffSum F N h ),

where `diffSum F N h = Σ_{m < N-h} F (m+h) · conj (F m)`.  When `‖F n‖ ≤ 1` this yields

    ‖Σ_{n < N} F n‖² ≤ N + 2 Σ_{h=1}^{N-1} ‖diffSum F N h‖.

For `F n = e(f n)` the differenced sums are `Σ_m e(f(m+h) - f(m))`: exactly the input the `A`
process consumes, and the reason `A` trades a sum of length `N` for `N` sums of shorter length.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace HTGeometry

open Finset Complex

/-- The differenced (autocorrelation) sum at shift `h`. -/
noncomputable def diffSum (F : ℕ → ℂ) (N h : ℕ) : ℂ :=
  ∑ m ∈ range (N - h), F (m + h) * (starRingEnd ℂ) (F m)

/-- The square of the modulus of a finite sum, as a double sum. -/
theorem normSq_sum_eq_doubleSum (N : ℕ) (F : ℕ → ℂ) :
    (‖∑ n ∈ range N, F n‖ : ℝ)^2
      = (∑ n ∈ range N, ∑ m ∈ range N, F n * (starRingEnd ℂ) (F m)).re := by
  have h1 : ∑ n ∈ range N, ∑ m ∈ range N, F n * (starRingEnd ℂ) (F m)
      = (∑ n ∈ range N, F n) * (starRingEnd ℂ) (∑ n ∈ range N, F n) := by
    rw [map_sum, Finset.sum_mul_sum]
  rw [h1, Complex.mul_conj]
  simpa using Complex.sq_norm (∑ n ∈ range N, F n)

/-- **The strictly-upper triangle is the sum of the differenced sums.**  Pairs `(n,m)` with
`m < n < N` are in bijection with pairs `(h,m)` with `1 ≤ h < N` and `m < N - h`, via `h = n - m`. -/
theorem upperTriangle_eq_sum_diffSum (N : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ range N, ∑ m ∈ range n, F n * (starRingEnd ℂ) (F m)
      = ∑ h ∈ Ico 1 N, diffSum F N h := by
  classical
  unfold diffSum
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.1 - p.2, p.2⟩) (j := fun q => ⟨q.2 + q.1, q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hp ⊢
    obtain ⟨hn, hm⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨h, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hq ⊢
    obtain ⟨⟨h1, h2⟩, hm⟩ := hq
    exact ⟨by omega, by omega⟩
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have : m + (n - m) = n := by omega
    simp [this]
  · rintro ⟨h, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hq
    simp
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have : m + (n - m) = n := by omega
    simp [this]

/-- **The diagonal-plus-triangles decomposition.**  Summing the inner index over `range N` splits
into the part below the diagonal, the diagonal, and the part above. -/
theorem doubleSum_eq_diag_add_triangles (N : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ range N, ∑ m ∈ range N, F n * (starRingEnd ℂ) (F m)
      = (∑ n ∈ range N, F n * (starRingEnd ℂ) (F n))
        + (∑ n ∈ range N, ∑ m ∈ range n, F n * (starRingEnd ℂ) (F m))
        + (∑ m ∈ range N, ∑ n ∈ range m, F n * (starRingEnd ℂ) (F m)) := by
  classical
  have key : ∀ n ∈ range N,
      ∑ m ∈ range N, F n * (starRingEnd ℂ) (F m)
        = (F n * (starRingEnd ℂ) (F n))
          + (∑ m ∈ range n, F n * (starRingEnd ℂ) (F m))
          + (∑ m ∈ Ico (n+1) N, F n * (starRingEnd ℂ) (F m)) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have h1 : range N = range n ∪ Ico n N := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      rw [← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le n) (le_of_lt hn)]
    have hdisj : Disjoint (range n) (Ico n N) := by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 n N
    rw [h1, Finset.sum_union hdisj, Finset.sum_eq_sum_Ico_succ_bot hn]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  -- the upper part, reindexed, is the lower triangle with the roles of the indices swapped
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.2, p.1⟩) (j := fun q => ⟨q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hp ⊢
    exact ⟨hp.2.2, by omega⟩
  · rintro ⟨m, n⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hq ⊢
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨n, m⟩ _; rfl
  · rintro ⟨m, n⟩ _; rfl
  · rintro ⟨n, m⟩ _; rfl


/-- The strictly-lower triangle is the complex conjugate of the strictly-upper one. -/
theorem lowerTriangle_eq_conj_upper (N : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ range N, ∑ n ∈ range m, F n * (starRingEnd ℂ) (F m)
      = (starRingEnd ℂ) (∑ n ∈ range N, ∑ m ∈ range n, F n * (starRingEnd ℂ) (F m)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

/-- **The Weyl differencing identity.**  The square of the modulus of an exponential sum is the sum
of the squared moduli of its terms plus twice the real part of the sum of the differenced sums. -/
theorem weyl_differencing_identity (N : ℕ) (F : ℕ → ℂ) :
    (‖∑ n ∈ range N, F n‖ : ℝ)^2
      = (∑ n ∈ range N, (‖F n‖ : ℝ)^2) + 2 * (∑ h ∈ Ico 1 N, diffSum F N h).re := by
  rw [normSq_sum_eq_doubleSum, doubleSum_eq_diag_add_triangles,
    lowerTriangle_eq_conj_upper, upperTriangle_eq_sum_diffSum]
  have hdiag : (∑ n ∈ range N, F n * (starRingEnd ℂ) (F n)).re
      = ∑ n ∈ range N, (‖F n‖ : ℝ)^2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.mul_conj]
    simpa using (Complex.sq_norm (F n)).symm
  rw [Complex.add_re, Complex.add_re, Complex.conj_re, hdiag]
  ring

/-- **The Weyl differencing bound.**  For unimodular-or-smaller terms, the square of the sum is
bounded by its length plus twice the total mass of the differenced sums.  This is the inequality the
`A` process applies: a sum of length `N` is traded for `N-1` differenced sums. -/
theorem weyl_differencing_bound (N : ℕ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) :
    (‖∑ n ∈ range N, F n‖ : ℝ)^2
      ≤ (N : ℝ) + 2 * ∑ h ∈ Ico 1 N, ‖diffSum F N h‖ := by
  rw [weyl_differencing_identity]
  have hdiag : (∑ n ∈ range N, (‖F n‖ : ℝ)^2) ≤ (N : ℝ) := by
    calc (∑ n ∈ range N, (‖F n‖ : ℝ)^2) ≤ ∑ _n ∈ range N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h0 : (0:ℝ) ≤ ‖F n‖ := norm_nonneg _
          nlinarith [hF n]
      _ = (N : ℝ) := by simp
  have hre : (∑ h ∈ Ico 1 N, diffSum F N h).re ≤ ∑ h ∈ Ico 1 N, ‖diffSum F N h‖ := by
    calc (∑ h ∈ Ico 1 N, diffSum F N h).re
        ≤ ‖∑ h ∈ Ico 1 N, diffSum F N h‖ := Complex.re_le_norm _
      _ ≤ ∑ h ∈ Ico 1 N, ‖diffSum F N h‖ := norm_sum_le _ _
  linarith

/-- The differenced sum at shift `h` has at most `N - h` terms, each of modulus at most `1` when
`F` is unimodular-or-smaller; so the trivial bound on it is `N - h`. -/
theorem norm_diffSum_le (N h : ℕ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) :
    ‖diffSum F N h‖ ≤ (N - h : ℕ) := by
  unfold diffSum
  calc ‖∑ m ∈ range (N - h), F (m + h) * (starRingEnd ℂ) (F m)‖
      ≤ ∑ m ∈ range (N - h), ‖F (m + h) * (starRingEnd ℂ) (F m)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ range (N - h), (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul, RCLike.norm_conj]
        have h1 := hF (m + h)
        have h2 := hF m
        have h0 : (0:ℝ) ≤ ‖F m‖ := norm_nonneg _
        nlinarith
    _ = ((N - h : ℕ) : ℝ) := by simp

end HTGeometry
