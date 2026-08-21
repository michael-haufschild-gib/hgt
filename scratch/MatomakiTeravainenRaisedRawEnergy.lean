import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedLemma41Energy
import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedEnergy

namespace RHTower.Sieve

open Finset

theorem scratch_raised_dyadic_block_mass_le_of_raw_energy
    {N A ell : ℕ} (hA : 1 ≤ A) (a : Fin N → ℂ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (henergy : ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
      Q * ((A ^ ell : ℕ) : ℝ))
    (r : Fin (ell + 1)) :
    ‖dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1
      (A ^ ell * 2 ^ (r : ℕ))‖ ^ 2 ≤
        Q / ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) := by
  let D : ℕ := A ^ ell * 2 ^ (r : ℕ)
  have hD : 1 ≤ D := by
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (r : ℕ) (by norm_num)))
  have hbase := norm_dyadicWeightedCoeff_sq_le_edge_weight
    (N ^ ell) D (convPow N ell a) (sigma := (1 : ℝ)) (by norm_num) hD
  have hweighted :
      ‖dyadicWeightedCoeff (N ^ ell) (convPow N ell a) 1 D‖ ^ 2 ≤
        (((D : ℝ) ^ (-(1 : ℝ))) ^ 2) *
          (Q * ((A ^ ell : ℕ) : ℝ)) :=
    hbase.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hAD : (((A ^ ell : ℕ) : ℝ)) ≤ (D : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) (r : ℕ))
  rw [Real.rpow_neg_one] at hweighted
  refine hweighted.trans ?_
  change (D : ℝ)⁻¹ ^ 2 * (Q * ((A ^ ell : ℕ) : ℝ)) ≤ Q / (D : ℝ)
  have hfrac : ((A ^ ell : ℕ) : ℝ) / (D : ℝ) ^ 2 ≤ 1 / (D : ℝ) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hD0) hD0]
    nlinarith
  calc
    (D : ℝ)⁻¹ ^ 2 * (Q * ((A ^ ell : ℕ) : ℝ)) =
        Q * (((A ^ ell : ℕ) : ℝ) / (D : ℝ) ^ 2) := by
      field_simp
    _ ≤ Q * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left hfrac hQ
    _ = Q / (D : ℝ) := by ring

end RHTower.Sieve
