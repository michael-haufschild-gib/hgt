import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMeanBinomialBound

/-! The edge-to-midpoint bridge transfers binomial concentration to canonical transport edges. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgeCenteredSecondMoment (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * (((i : ℕ) : ℝ) - (r : ℝ) / 2) ^ 2

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeCenteredSecondMoment r k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (finiteWeilCanonicalEdgeMass_pos r k i)) (by positivity)

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_normalized_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    finiteWeilCanonicalEdgeCenteredSecondMoment r k / ((r + 1 : ℕ) : ℝ) ^ 2 ≤
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hf (u : Fin (r + 2)) : |(((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2| ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 / 4 := by
    have hu0 : (0 : ℝ) ≤ ((u : ℕ) : ℝ) := Nat.cast_nonneg _
    have hu1 : ((u : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (u : ℕ) ≤ r + 1 by have := u.isLt; omega)
    have hp := mul_nonneg hu0 (sub_nonneg.mpr hu1)
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [hp]
  have hl := finiteWeil_profile_test_l1_bound
    (finiteWeilCanonicalMixture r k (1 / 2))
    (fun u : Fin (r + 2) => ((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1))
    (fun u => (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2)
    (((r + 1 : ℕ) : ℝ) ^ 2 / 4) hf
  have hm : (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u *
      (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) =
      finiteWeilCanonicalEdgeCenteredSecondMoment r k + 1 / 4 :=
    finiteWeilCanonicalMixture_midpoint_edge_half_centered_second_moment r k
  rw [hm, finiteWeil_binomial_probability_centered_second_moment] at hl
  have hu := (abs_le.mp hl).2
  have hD := mul_le_mul_of_nonneg_left
    (finiteWeilCanonicalMixture_midpoint_binomial_bound r k hwidth)
    (show 0 ≤ ((r + 1 : ℕ) : ℝ) ^ 2 / 4 by positivity)
  have hraw : finiteWeilCanonicalEdgeCenteredSecondMoment r k ≤ (r : ℝ) / 4 +
      (((r + 1 : ℕ) : ℝ) ^ 2 / 2) *
        (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
    push_cast at hu hD ⊢
    nlinarith only [hu, hD]
  have hnorm : finiteWeilCanonicalEdgeCenteredSecondMoment r k / ((r + 1 : ℕ) : ℝ) ^ 2 ≤
      (r : ℝ) / (4 * ((r + 1 : ℕ) : ℝ) ^ 2) +
        (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) / 2 := by
    calc
      _ ≤ ((r : ℝ) / 4 + (((r + 1 : ℕ) : ℝ) ^ 2 / 2) *
          (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) /
            ((r + 1 : ℕ) : ℝ) ^ 2 := div_le_div_of_nonneg_right hraw (by positivity)
      _ = _ := by field_simp
  have hS : (1 : ℝ) / 2 ≤ Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
    have hs0 := Real.sqrt_nonneg ((((r + 1 : ℕ) : ℝ) + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (((r + 1 : ℕ) : ℝ) + 1) / 2 by positivity)
    nlinarith only [hs0, hs2, hn1]
  have hsmall : (r : ℝ) / (4 * ((r + 1 : ℕ) : ℝ) ^ 2) ≤
      (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) / 2 := by
    calc
      _ ≤ ((r + 1 : ℕ) : ℝ) / (4 * ((r + 1 : ℕ) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by push_cast; linarith) (by positivity)
      _ = (((1 : ℝ) / 2) / ((r + 1 : ℕ) : ℝ)) / 2 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hS hn.le) (by positivity)
  linarith only [hnorm, hsmall]

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_bound (r t : ℕ) :
    finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) ^ 2 ≤
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ) := by
  apply finiteWeilCanonicalEdgeCenteredSecondMoment_normalized_bound
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
