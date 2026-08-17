import GaloisForLFunctions.HTGeometry.ComplexBinomialRemainder

/-!
# A calculus of truncated expansions on a disc

A function has a polynomial expansion of order `n` on the disc of radius `r` when its difference from
that polynomial is at most a constant times the `n`-th power of the argument.  The relation is closed
under sums, scalar multiples and products -- for products no truncation is needed, because the
product of the two polynomials is again a polynomial and the two error terms are simply multiplied by
the other factor's bound.

Truncating the polynomial to degree below `n` costs one more term of the same order, provided the
disc has radius at most one; that step is taken once, at the end of a computation.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section DiscExpansion

/-- `f` agrees with the polynomial `P` to order `n` on the disc of radius `r`. -/
def HasPolyExpansion (r : ℝ) (n : ℕ) (C : ℝ) (f : ℂ → ℂ) (P : Polynomial ℂ) : Prop :=
  ∀ w : ℂ, ‖w‖ ≤ r → ‖f w - P.eval w‖ ≤ C * ‖w‖ ^ n

theorem HasPolyExpansion.add {r C D : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hg : HasPolyExpansion r n D g Q) :
    HasPolyExpansion r n (C + D) (fun w => f w + g w) (P + Q) := by
  intro w hw
  have hsplit : f w + g w - (P + Q).eval w
      = (f w - P.eval w) + (g w - Q.eval w) := by
    rw [Polynomial.eval_add]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hf w hw
  have h2 := hg w hw
  linarith [h1, h2, (by ring : (C + D) * ‖w‖ ^ n = C * ‖w‖ ^ n + D * ‖w‖ ^ n)]

theorem HasPolyExpansion.const_mul {r C : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (a : ℂ)
    (hf : HasPolyExpansion r n C f P) :
    HasPolyExpansion r n (‖a‖ * C) (fun w => a * f w) (Polynomial.C a * P) := by
  intro w hw
  have hsplit : a * f w - (Polynomial.C a * P).eval w = a * (f w - P.eval w) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hsplit, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf w hw) (norm_nonneg a)

/-- **The product rule.**  No truncation is needed: the product of the two polynomials is again a
polynomial, and each error term is multiplied by the other factor's bound. -/
theorem HasPolyExpansion.mul {r C D Bg Bp : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hg : HasPolyExpansion r n D g Q)
    (hgb : ∀ w : ℂ, ‖w‖ ≤ r → ‖g w‖ ≤ Bg) (hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ Bp)
    (hC : 0 ≤ C) :
    HasPolyExpansion r n (C * Bg + Bp * D) (fun w => f w * g w) (P * Q) := by
  intro w hw
  have hsplit : f w * g w - (P * Q).eval w
      = (f w - P.eval w) * g w + P.eval w * (g w - Q.eval w) := by
    rw [Polynomial.eval_mul]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖f w - P.eval w‖ * ‖g w‖ ≤ (C * ‖w‖ ^ n) * Bg := by
    refine mul_le_mul (hf w hw) (hgb w hw) (norm_nonneg _) (by positivity)
  have h2 : ‖P.eval w‖ * ‖g w - Q.eval w‖ ≤ Bp * (D * ‖w‖ ^ n) := by
    refine mul_le_mul (hPb w hw) (hg w hw) (norm_nonneg _) ?_
    exact le_trans (norm_nonneg _) (hPb w hw)
  calc ‖f w - P.eval w‖ * ‖g w‖ + ‖P.eval w‖ * ‖g w - Q.eval w‖
      ≤ (C * ‖w‖ ^ n) * Bg + Bp * (D * ‖w‖ ^ n) := add_le_add h1 h2
    _ = (C * Bg + Bp * D) * ‖w‖ ^ n := by ring

/-- A function with an expansion is bounded on the disc. -/
theorem HasPolyExpansion.norm_le {r C Bp : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ Bp)
    (hC : 0 ≤ C) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖f w‖ ≤ C * r ^ n + Bp := by
  have hsub : ‖f w - P.eval w‖ ≤ C * r ^ n := by
    refine le_trans (hf w hw) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw n) hC
  have h := norm_sub_norm_le (f w) (P.eval w)
  have h2 := hPb w hw
  linarith [h, hsub, h2]

/-- The polynomial truncated below degree `n`. -/
def truncBelow (n : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n, Polynomial.C (P.coeff k) * Polynomial.X ^ k

/-- The total absolute coefficient mass of a polynomial. -/
def polyAbsSum (P : Polynomial ℂ) : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖

theorem polyAbsSum_nonneg (P : Polynomial ℂ) : 0 ≤ polyAbsSum P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Truncating below degree `n` costs one more term of order `n`, on a disc of radius at most one. -/
theorem norm_eval_sub_truncBelow_le (P : Polynomial ℂ) (n : ℕ) {r : ℝ} (hr1 : r ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖P.eval w - (truncBelow n P).eval w‖ ≤ polyAbsSum P * ‖w‖ ^ n := by
  classical
  have hwr : ‖w‖ ≤ 1 := le_trans hw hr1
  have hPeval : P.eval w = ∑ k ∈ P.support, P.coeff k * w ^ k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
  have htrunc : (truncBelow n P).eval w
      = ∑ k ∈ Finset.range n, P.coeff k * w ^ k := by
    rw [truncBelow, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by simp
  have hsplit : ∑ k ∈ P.support, P.coeff k * w ^ k
      = ∑ k ∈ P.support.filter (fun k => k < n), P.coeff k * w ^ k
        + ∑ k ∈ P.support.filter (fun k => ¬ k < n), P.coeff k * w ^ k :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : ∑ k ∈ P.support.filter (fun k => k < n), P.coeff k * w ^ k
      = ∑ k ∈ Finset.range n, P.coeff k * w ^ k := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      rw [Finset.mem_filter] at hk
      exact Finset.mem_range.mpr hk.2
    · intro k hk hnk
      have hk' : ¬ (k ∈ P.support ∧ k < n) := by
        intro h
        exact hnk (Finset.mem_filter.mpr h)
      have hkn : k < n := Finset.mem_range.mp hk
      have hns : k ∉ P.support := by
        intro h
        exact hk' ⟨h, hkn⟩
      rw [Polynomial.notMem_support_iff.mp hns]
      ring
  rw [hPeval, hsplit, hlow, htrunc]
  simp only [add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) ?_
  rw [polyAbsSum, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum (fun k hk => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => by positivity))
  rw [Finset.mem_filter] at hk
  have hkn : n ≤ k := by omega
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact pow_le_pow_of_le_one (norm_nonneg w) hwr hkn

/-- The truncated expansion, on a disc of radius at most one. -/
theorem HasPolyExpansion.trunc {r C : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hr1 : r ≤ 1) :
    HasPolyExpansion r n (C + polyAbsSum P) f (truncBelow n P) := by
  intro w hw
  have hsplit : f w - (truncBelow n P).eval w
      = (f w - P.eval w) + (P.eval w - (truncBelow n P).eval w) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := hf w hw
  have h2 := norm_eval_sub_truncBelow_le P n hr1 hw
  nlinarith [h1, h2, pow_nonneg (norm_nonneg w) n]

end DiscExpansion

end

end GaloisForLFunctions.HTGeometry
