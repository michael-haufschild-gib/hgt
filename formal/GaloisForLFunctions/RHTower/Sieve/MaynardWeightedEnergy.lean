import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedDyadic

/-!
# Support-aware weighted energy for raised Maynard factors

Huxley absorption near `sigma = 1` requires retaining the full real-axis weight.  On a block
`[D,2D)`, monotonicity gives `n^(-sigma) <= D^(-sigma)`, so weighted Hilbert energy is the raw
coefficient energy times `D^(-2 sigma)`.  This missing factor is the power saving that makes the
all-short argument possible.
-/

namespace RHTower.Sieve

open Finset

/-- Weighted dyadic energy retains its support-edge decay. -/
theorem norm_dyadicWeightedCoeff_sq_le_edge_weight
    (M D : ℕ) (b : Fin M → ℂ) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hD : 1 ≤ D) :
    ‖dyadicWeightedCoeff M b sigma D‖ ^ 2 ≤
      ((D : ℝ) ^ (-sigma)) ^ 2 * ∑ j : Fin M, ‖b j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hDR : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hD
  have hterm : ∀ j : Fin D,
      ‖(dyadicWeightedCoeff M b sigma D) j‖ ^ 2 ≤
        ((D : ℝ) ^ (-sigma)) ^ 2 *
          ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 := by
    intro j
    have hDn : (D : ℝ) ≤ ((D + (j : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right D (j : ℕ)
    have hw0 : 0 ≤ (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma)) :=
      Real.rpow_nonneg (by positivity) _
    have hDweight0 : 0 ≤ (D : ℝ) ^ (-sigma) := Real.rpow_nonneg hDR.le _
    have hw : (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma)) ≤
        (D : ℝ) ^ (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hDR hDn (by linarith)
    simp only [dyadicWeightedCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
    have hc0 := norm_nonneg (anchoredCoeff M b (D + (j : ℕ)))
    have hmul : ‖anchoredCoeff M b (D + (j : ℕ))‖ *
          (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma)) ≤
        ‖anchoredCoeff M b (D + (j : ℕ))‖ * ((D : ℝ) ^ (-sigma)) :=
      mul_le_mul_of_nonneg_left hw hc0
    calc
      (‖anchoredCoeff M b (D + (j : ℕ))‖ *
          (((D + (j : ℕ) : ℕ) : ℝ) ^ (-sigma))) ^ 2
          ≤ (‖anchoredCoeff M b (D + (j : ℕ))‖ *
              ((D : ℝ) ^ (-sigma))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hc0 hw0) hmul 2
      _ = ((D : ℝ) ^ (-sigma)) ^ 2 *
          ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 := by ring
  have hsum : ∑ j : Fin D, ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 =
      ∑ n ∈ Finset.Ico D (2 * D), ‖anchoredCoeff M b n‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : 2 * D - D = D := by omega
    rw [hlen]
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ ‖anchoredCoeff M b (D + j)‖ ^ 2) D
  calc
    ∑ j : Fin D, ‖(dyadicWeightedCoeff M b sigma D) j‖ ^ 2
        ≤ ∑ j : Fin D, ((D : ℝ) ^ (-sigma)) ^ 2 *
            ‖anchoredCoeff M b (D + (j : ℕ))‖ ^ 2 :=
      Finset.sum_le_sum fun j _ ↦ hterm j
    _ = ((D : ℝ) ^ (-sigma)) ^ 2 *
        ∑ n ∈ Finset.Ico D (2 * D), ‖anchoredCoeff M b n‖ ^ 2 := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ ((D : ℝ) ^ (-sigma)) ^ 2 * ∑ j : Fin M, ‖b j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_normSq_anchoredCoeff_Ico_le M D b) (sq_nonneg _)

end RHTower.Sieve
