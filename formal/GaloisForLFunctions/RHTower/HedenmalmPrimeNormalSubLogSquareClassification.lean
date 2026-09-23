import GaloisForLFunctions.RHTower.HedenmalmPrimeNormalWickBoundaryEnergy
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Exact domain of the Hedenmalm prime-normal sub-log-square completion

The source-normal Hedenmalm prime row has energy equal to vertical trigonometric energy plus
radial hyperbolic energy.  The radial lower bound already shows that sub-`log²` energy forces zero
radial displacement.  This module proves the converse: on the centered real axis the vertical
energy is bounded by the harmonic series, hence is `o(log² N)`.

Consequently the regular domain of this fixed all-prime completion is exactly the centered real
axis.  This is a domain-classification theorem, not a proof that Xi root blocks enter that domain.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The vertical prime-clock energy is at most four times the ordinary harmonic number. -/
lemma primeClockVerticalEnergy_le_four_mul_harmonic
    (N : ℕ) (x : ℝ) :
    primeClockVerticalEnergy N x ≤ 4 * (harmonic N : ℝ) := by
  rw [primeClockVerticalEnergy, Nat.primesLE_eq_filter_Icc_one]
  calc
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        4 * Real.sin (x * Real.log p / 2) ^ (2 : ℕ) / p) ≤
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, 4 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hmul : 4 * Real.sin (x * Real.log p / 2) ^ (2 : ℕ) ≤ (4 : ℝ) := by
        nlinarith [Real.sin_sq_le_one (x * Real.log p / 2)]
      exact (div_le_div_iff_of_pos_right hp0).2 hmul
    _ ≤ ∑ p ∈ Finset.Icc 1 N, 4 / (p : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
        (fun p _ _ => by
          exact div_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le p)))
    _ = 4 * (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [div_eq_mul_inv]

/-- Every centered-real source point belongs to the sub-`log²` Hedenmalm prime-normal domain. -/
theorem hedenmalmPrimeNormalSubLogSquare_of_im_eq_zero
    {z : ℂ} (hz : z.im = 0) :
    HedenmalmPrimeNormalSubLogSquare z := by
  rw [HedenmalmPrimeNormalSubLogSquare]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto (fun N : ℕ => (8 : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero'
  · filter_upwards with N
    have henergy : 0 ≤ hedenmalmPrimeNormalEnergy N z := by
      rw [hedenmalmPrimeNormalEnergy_eq_vertical_add_radial]
      exact add_nonneg (primeClockVerticalEnergy_nonneg N z.re)
        (primeClockCutoffEnergy_nonneg N (z.im / 2))
    exact div_nonneg henergy (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hlogone : 1 ≤ Real.log N := by
      have h3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans_le (by norm_num)
      have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN
      calc
        1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (h3.le.trans hNreal)
    have henergy : hedenmalmPrimeNormalEnergy N z ≤
        4 * (harmonic N : ℝ) := by
      rw [hedenmalmPrimeNormalEnergy_eq_vertical_add_radial, hz, zero_div,
        primeClockCutoffEnergy_zero, add_zero]
      exact primeClockVerticalEnergy_le_four_mul_harmonic N z.re
    have hharm : (harmonic N : ℝ) ≤ 1 + Real.log N :=
      harmonic_le_one_add_log N
    have hlogpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlogone
    calc
      hedenmalmPrimeNormalEnergy N z / Real.log N ^ (2 : ℕ) ≤
          (4 * (harmonic N : ℝ)) / Real.log N ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right henergy (sq_nonneg _)
      _ ≤ (4 * (1 + Real.log N)) / Real.log N ^ (2 : ℕ) := by
        gcongr
      _ ≤ 8 / Real.log N := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogpos) hlogpos]
        nlinarith
  · exact hinvlog

/-- **Exact Hedenmalm prime-normal domain classification.**  Sub-`log²` source-normal energy is
equivalent to zero radial displacement. -/
theorem hedenmalmPrimeNormalSubLogSquare_iff_im_eq_zero (z : ℂ) :
    HedenmalmPrimeNormalSubLogSquare z ↔ z.im = 0 := by
  exact ⟨im_eq_zero_of_hedenmalmPrimeNormalSubLogSquare,
    hedenmalmPrimeNormalSubLogSquare_of_im_eq_zero⟩

end

end RHTower
