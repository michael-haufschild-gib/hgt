import GaloisForLFunctions.ThetaCuspSections.WeightedLegendrePolynomialData

/-!
# Exact norms of weighted Legendre modes

The derivative ladder retains a factorial quotient in each norm. Dividing
the squared leading coefficient by this norm exposes the endpoint
constraints that disappear in an unweighted polynomial embedding.
-/

open Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections

private theorem factorial_step {n r : ℕ} (hr : r < n) :
    ((n - r).factorial : ℝ) = (n - r : ℕ) * ((n - (r + 1)).factorial : ℝ) := by
  have he : n - r = n - (r + 1) + 1 := by omega
  have hh := Nat.factorial_succ (n - (r + 1))
  rw [← he] at hh
  exact_mod_cast hh

/-- The leading derivative product is the exact falling factorial. -/
theorem legendreDerivativeLead_mul_factorial {n r : ℕ} (hr : r ≤ n) :
    legendreDerivativeLead n r * ((n - r).factorial : ℝ) =
      legendreLead n * (n.factorial : ℝ) := by
  induction r with
  | zero => simp only [legendreDerivativeLead, Nat.sub_zero]
  | succ r ih =>
    rw [legendreDerivativeLead, mul_assoc, ← factorial_step (by omega)]
    exact ih (by omega)

/-- Each Sturm eigenvalue supplies one falling and one rising factor. -/
theorem legendreEigenProduct_mul_factorial {n r : ℕ} (hr : r ≤ n) :
    (∏ j ∈ Finset.range r, legendreDerivativeEigen n j) * ((n - r).factorial : ℝ) =
      ((n + r).factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hnr : r ≤ n := by omega
    have he : legendreDerivativeEigen n r = (n - r : ℕ) * ((n + r + 1 : ℕ) : ℝ) := by
      rw [legendreDerivativeEigen, Nat.cast_sub hnr]
      push_cast
      ring
    rw [Finset.prod_range_succ, he, show n + (r + 1) = (n + r) + 1 by omega,
      Nat.factorial_succ, Nat.cast_mul]
    calc
      _ = ((n + r + 1 : ℕ) : ℝ) *
          ((∏ j ∈ Finset.range r, legendreDerivativeEigen n j) *
            ((n - r : ℕ) * ((n - (r + 1)).factorial : ℝ))) := by ring
      _ = _ := by rw [← factorial_step (by omega), ih hnr]

/-- The exact derivative norm contains both endpoint factorials. -/
theorem weightedLegendreEnergy_self_factorial {n r : ℕ} (hr : r ≤ n) :
    weightedLegendreEnergy r n n =
      2 * ((n + r).factorial : ℝ) /
        (((n - r).factorial : ℝ) * (2 * (n : ℝ) + 1)) := by
  rw [weightedLegendreEnergy_self]
  have hf : ((n - r).factorial : ℝ) ≠ 0 := by positivity
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff (mul_ne_zero hf hn)).mpr
  calc
    _ = 2 * ((∏ j ∈ Finset.range r, legendreDerivativeEigen n j) *
        ((n - r).factorial : ℝ)) := by field_simp
    _ = _ := by rw [legendreEigenProduct_mul_factorial hr]

theorem weightedLegendreEnergy_self_pos {n r : ℕ} (hr : r ≤ n) :
    0 < weightedLegendreEnergy r n n := by
  rw [weightedLegendreEnergy_self_factorial hr]
  positivity

/-- Squared leading coefficient divided by the weighted squared norm. -/
def weightedLegendreLeadRatio (r n : ℕ) : ℝ :=
  legendreDerivativeLead (n + r) r ^ 2 / weightedLegendreEnergy r (n + r) (n + r)

theorem weightedLegendreLeadRatio_pos (r n : ℕ) : 0 < weightedLegendreLeadRatio r n :=
  div_pos (sq_pos_of_pos (legendreDerivativeLead_pos (by omega)))
    (weightedLegendreEnergy_self_pos (by omega))

/-- The factorial ratio measures precisely the retained endpoint constraints. -/
theorem weightedLegendreLeadRatio_factorial (r n : ℕ) :
    weightedLegendreLeadRatio r n =
      legendreLead (n + r) ^ 2 * (((n + r).factorial : ℝ) ^ 2) *
        (2 * ((n + r : ℕ) : ℝ) + 1) /
        (2 * (n.factorial : ℝ) * ((n + 2 * r).factorial : ℝ)) := by
  have hnr : r ≤ n + r := by omega
  have hL := legendreDerivativeLead_mul_factorial hnr
  have hsub : n + r - r = n := by omega
  have hadd : n + r + r = n + 2 * r := by omega
  rw [hsub] at hL
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hL' : legendreDerivativeLead (n + r) r =
      legendreLead (n + r) * ((n + r).factorial : ℝ) / (n.factorial : ℝ) :=
    (eq_div_iff hf).mpr hL
  rw [weightedLegendreLeadRatio, weightedLegendreEnergy_self_factorial hnr, hsub, hadd, hL']
  field_simp

/-- The weighted leading scale has an explicit positive consecutive ratio. -/
theorem weightedLegendreLeadRatio_succ (r n : ℕ) :
    weightedLegendreLeadRatio r (n + 1) =
      ((2 * (n : ℝ) + 2 * r + 3) * (2 * (n : ℝ) + 2 * r + 1) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2 * r + 1))) * weightedLegendreLeadRatio r n := by
  rw [weightedLegendreLeadRatio_factorial, weightedLegendreLeadRatio_factorial,
    show n + 1 + r = n + r + 1 by omega,
    show n + 1 + 2 * r = n + 2 * r + 1 by omega]
  simp only [legendreLead, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hN : (n.factorial : ℝ) ≠ 0 := by positivity
  have hR : ((n + 2 * r).factorial : ℝ) ≠ 0 := by positivity
  have hnr : (n : ℝ) + r + 1 ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnr2 : (n : ℝ) + 2 * r + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Higher degree increases the leading coefficient relative to its weighted norm. -/
theorem weightedLegendreLeadRatio_mono (r : ℕ) : Monotone (weightedLegendreLeadRatio r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [weightedLegendreLeadRatio_succ]
  have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2 * r + 1) := by positivity
  have hfactor : 1 ≤ (2 * (n : ℝ) + 2 * r + 3) * (2 * (n : ℝ) + 2 * r + 1) /
      (((n : ℝ) + 1) * ((n : ℝ) + 2 * r + 1)) := by
    rw [le_div_iff₀ hden]
    nlinarith only [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) r,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) r),
      sq_nonneg (n : ℝ), sq_nonneg (r : ℝ)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
    (weightedLegendreLeadRatio_pos r n).le

/-- The shifted leading coefficients satisfy the top-degree part of weighted Bonnet. -/
theorem shiftedLegendreLead_succ (r n : ℕ) :
    ((n : ℝ) + 1) * legendreDerivativeLead (n + 1 + r) r =
      (2 * (n : ℝ) + 2 * r + 1) * legendreDerivativeLead (n + r) r := by
  have h0 := legendreDerivativeLead_mul_factorial (n := n + r) (r := r) (by omega)
  have h1 := legendreDerivativeLead_mul_factorial (n := n + 1 + r) (r := r) (by omega)
  rw [show n + r - r = n by omega] at h0
  rw [show n + 1 + r - r = n + 1 by omega,
    show n + 1 + r = n + r + 1 by omega] at h1
  simp only [legendreLead, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have hnr : (n : ℝ) + r + 1 ≠ 0 := by positivity
  have hN : (n.factorial : ℝ) ≠ 0 := by positivity
  have he : legendreDerivativeLead (n + r + 1) r * (((n : ℝ) + 1) * (n.factorial : ℝ)) =
      (2 * (n : ℝ) + 2 * r + 1) * (legendreLead (n + r) * ((n + r).factorial : ℝ)) := by
    calc
      _ = _ := h1
      _ = _ := by field_simp
  rw [← h0] at he
  rw [show n + 1 + r = n + r + 1 by omega]
  apply (mul_right_cancel₀ hN)
  linear_combination he

#print axioms weightedLegendreEnergy_self_factorial
#print axioms weightedLegendreLeadRatio_factorial
#print axioms weightedLegendreLeadRatio_mono
#print axioms shiftedLegendreLead_succ

end GaloisForLFunctions.ThetaCuspSections
