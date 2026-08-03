import GaloisForLFunctions.RHTower.Sieve.DirichletFarField
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum

/-!
# A mean value theorem for Dirichlet polynomials

Summing the far-field Gram bound over a family of frequencies separated by `δ` and spread over an
interval of length `V` gives, for `F(t) = ∑_{n ≤ N} a_n n^{it}`,

`∑_{r < R} |F(τ_r)|² ≤ (N + 2(N+2)(1 + log R)/δ + R V (1 + log N)) ∑_n |a_n|²`.

The diagonal contributes `N`; the reciprocal separations contribute a harmonic sum, bounded by
`SeparatedRowSum.lean`; and the linear term of the far-field estimate contributes the spread.

This beats the trivial `R N` of `DirichletTrivial.lean` whenever `R` is large compared with
`log R`.  It is not the sharp Montgomery–Vaughan form: the factor `log R` on the `N` term is the
cost of bounding `∑_{t ≠ r} |τ_t - τ_r|^{-1}` term by term, and `sum_inv_abs_dist_le` shows that
cost is unavoidable for any absolute-values argument — the same obstruction that caps the large
sieve constant in this folder.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Separated frequencies are pairwise distinct. -/
theorem ne_of_gap {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    {r s : ℕ} (hrs : r ≠ s) : lam r ≠ lam s := by
  rcases lt_or_gt_of_ne hrs with h | h
  · exact ne_of_lt (lt_of_gap hδ hgap h)
  · exact ne_of_gt (lt_of_gap hδ hgap h)

/-- **A mean value theorem for Dirichlet polynomials at separated frequencies.** -/
theorem dirichlet_meanValue (N R : ℕ) (τ : ℕ → ℝ) {δ V : ℝ} (hδ0 : 0 < δ) (hV : 0 ≤ V)
    (hgap : ∀ i, τ i + δ ≤ τ (i + 1))
    (hspread : ∀ r ∈ Finset.range R, ∀ t ∈ Finset.range R, |τ t - τ r| ≤ V)
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ Finset.range R, ‖⟪dirRow N (τ r), a⟫_ℂ‖ ^ 2
      ≤ ((N : ℝ) + 2 * ((N : ℝ) + 2) * (1 + Real.log R) / δ
          + (R : ℝ) * V * (1 + Real.log N)) * ‖a‖ ^ 2 := by
  classical
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hN)
  have hlogR : 0 ≤ Real.log (R : ℝ) := by
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hR)
  have hΔ0 : (0 : ℝ) ≤ (N : ℝ) + 2 * ((N : ℝ) + 2) * (1 + Real.log R) / δ
      + (R : ℝ) * V * (1 + Real.log N) := by positivity
  refine dirichlet_bessel N (Finset.range R) τ hΔ0 (fun r hr => ?_) a
  have hrR : r < R := Finset.mem_range.mp hr
  -- split off the diagonal
  have hsplit : ∑ t ∈ Finset.range R, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖
      = ‖⟪dirRow N (τ r), dirRow N (τ r)⟫_ℂ‖
        + ∑ t ∈ (Finset.range R).erase r, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖ :=
    (Finset.add_sum_erase _ _ hr).symm
  have hdiag : ‖⟪dirRow N (τ r), dirRow N (τ r)⟫_ℂ‖ = (N : ℝ) := by
    rw [inner_dirRow_self]
    simp
  -- bound the off-diagonal entries
  have hterm : ∀ t ∈ (Finset.range R).erase r,
      ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖
        ≤ ((N : ℝ) + 2) * (1 / |τ t - τ r|) + |τ t - τ r| * (1 + Real.log N) := by
    intro t ht
    have hne : r ≠ t := Ne.symm (Finset.mem_erase.mp ht).1
    have hval : τ r ≠ τ t := ne_of_gap hδ0 hgap hne
    have hb := norm_inner_dirRow_le_gap N (t := τ r) (u := τ t) hval
    have hrewrite : ((N : ℝ) + 2) / |τ t - τ r| = ((N : ℝ) + 2) * (1 / |τ t - τ r|) := by
      ring
    rw [hrewrite] at hb
    exact hb
  -- the reciprocal separations form a harmonic sum
  have hrec : ∑ t ∈ (Finset.range R).erase r, 1 / |τ t - τ r|
      ≤ 2 / δ * (1 + Real.log R) := by
    have h1 := sum_inv_abs_dist_le hδ0 hgap hrR
    have h2 : ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log R := by
      rw [← sum_Icc_one_div_eq_sum_range]
      exact sum_Icc_one_div_le_one_add_log R
    have h3 : (0 : ℝ) ≤ 2 / δ := by positivity
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h3)
  -- the spreads are bounded by the interval length
  have hspr : ∑ t ∈ (Finset.range R).erase r, |τ t - τ r| ≤ (R : ℝ) * V := by
    have hcard : ((Finset.range R).erase r).card ≤ R := by
      have h := Finset.card_erase_le (s := Finset.range R) (a := r)
      rw [Finset.card_range] at h
      exact h
    calc ∑ t ∈ (Finset.range R).erase r, |τ t - τ r|
        ≤ ∑ _t ∈ (Finset.range R).erase r, V :=
          Finset.sum_le_sum (fun t ht => hspread r hr t (Finset.mem_of_mem_erase ht))
      _ = (((Finset.range R).erase r).card : ℝ) * V := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R : ℝ) * V := by
          refine mul_le_mul_of_nonneg_right ?_ hV
          exact_mod_cast hcard
  -- assemble the row
  have hoff : ∑ t ∈ (Finset.range R).erase r, ‖⟪dirRow N (τ r), dirRow N (τ t)⟫_ℂ‖
      ≤ 2 * ((N : ℝ) + 2) * (1 + Real.log R) / δ + (R : ℝ) * V * (1 + Real.log N) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have hA : ((N : ℝ) + 2) * ∑ t ∈ (Finset.range R).erase r, 1 / |τ t - τ r|
        ≤ 2 * ((N : ℝ) + 2) * (1 + Real.log R) / δ := by
      have hpos : (0 : ℝ) ≤ (N : ℝ) + 2 := by positivity
      have := mul_le_mul_of_nonneg_left hrec hpos
      have heq : ((N : ℝ) + 2) * (2 / δ * (1 + Real.log R))
          = 2 * ((N : ℝ) + 2) * (1 + Real.log R) / δ := by ring
      linarith [this, heq.le, heq.ge]
    have hB : (∑ t ∈ (Finset.range R).erase r, |τ t - τ r|) * (1 + Real.log N)
        ≤ (R : ℝ) * V * (1 + Real.log N) := by
      refine mul_le_mul_of_nonneg_right hspr (by linarith)
    linarith
  rw [hsplit, hdiag]
  linarith

end RHTower.Sieve
