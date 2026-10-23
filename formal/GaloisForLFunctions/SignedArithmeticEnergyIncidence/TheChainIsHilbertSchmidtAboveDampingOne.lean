import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsATailPhenomenon
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheInversionDefectIsPositive
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic

/-!
# The chain is Hilbert–Schmidt above damping one

The centred damping chain `C_η` acts on `c₀`; its receiver norm is `ℓ²`.  Above damping one the
source is bounded and the chain is bounded in `ℓ²` by size alone.

* **The source is bounded** (`abs_centeredPrefix_le`): for `η > 1`,
  `|P_η(m)| ≤ ζ(η) + 1`.  In floor coordinates
  `P_η(m) = Σ_{d ≤ m} μ(d) d^{−η} (⌊m/d⌋ − m/d) − m Σ_{d > m} μ(d) d^{−1−η}`, and both pieces are
  bounded by size.
* **Kernel bound** (`abs_centeredRow_le`): writing `A_η = ρ x + P_η`, the centred entry of the
  chain from state `n + 1` to state `k + 1` is at most `2(ρ + ζ(η) + 1) (k+1)^{1−η}/(n+1)` for
  `k ≤ n`, and is minus the entrance mass `e_η(k+1) ≤ ρ (k+1)^{−η}` beyond (`entrance_le`).
* **Hilbert–Schmidt bound** (`sum_sq_centeredRow_le`, `centeredOperator_l2_le`): every column has
  `Σ_n C(n,k)² ≲ (k+1)^{1−2η}`, which is summable exactly when `η > 1`; so `C_η` is bounded in
  `ℓ²` on finitely supported sequences, with constant `(8(ρ + ζ(η) + 1)² + ρ²) ζ(2η − 1)`.

Below damping one this size argument fails: the bound `|P_η(m)| ≲ m^{1−η}` makes every column
square-summable but not uniformly so.  Between half damping and one, `ℓ²`-boundedness of the chain
needs cancellation in the source.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The source is bounded above damping one -/

/-- `Σ_{j ≥ m+1} 1/j² ≤ 1/m`. -/
theorem tsum_inv_sq_tail_le {m : ℕ} (hm : 1 ≤ m) :
    ∑' j : ℕ, 1 / ((j + m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / m := by
  refine tsum_le_of_sum_range_le (fun j => by positivity) fun J => ?_
  have h := RHTower.sum_inv_sq_tail_le hm (m + J)
  have hre : ∑ j ∈ range J, 1 / ((j + m + 1 : ℕ) : ℝ) ^ 2 =
      ∑ n ∈ Icc (m + 1) (m + J), 1 / (n : ℝ) ^ (2 : ℕ) := by
    have hIcc : Icc (m + 1) (m + J) = Ico (m + 1) (m + 1 + J) := by
      ext n; simp only [mem_Icc, mem_Ico]; omega
    rw [hIcc, sum_Ico_eq_sum_range, show m + 1 + J - (m + 1) = J by omega]
    exact sum_congr rfl fun j _ => by rw [show j + m + 1 = m + 1 + j by ring]
  rw [hre]
  exact h

/-- The density is the Möbius series `ρ_η = Σ_d μ(d) d^{−(1+η)}`. -/
theorem density_re_eq_tsum {η : ℝ} (hη : 0 < η) :
    (pmPowerDampedDivisorDensity η).re = ∑' d : ℕ, (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) := by
  have h := HTGeometry.ofReal_tsum_moebius_eq (σ := 1 + η) (by linarith)
  have hc : (1 : ℂ) + (η : ℂ) = ((1 + η : ℝ) : ℂ) := by push_cast; ring
  rw [pmPowerDampedDivisorDensity, hc, ← h, Complex.ofReal_re]

/-- `|μ(d) d^{−(1+η)}| ≤ 1/d²` for `η ≥ 1`. -/
theorem abs_moebius_rpow_le {η : ℝ} (hη : 1 ≤ η) {d : ℕ} (hd : 1 ≤ d) :
    |(moebius d : ℝ) * (d : ℝ) ^ (-(1 + η))| ≤ 1 / (d : ℝ) ^ 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hp : (d : ℝ) ^ (-(1 + η)) ≤ (d : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have h2 : (d : ℝ) ^ (-(2 : ℝ)) = 1 / (d : ℝ) ^ 2 := by
    rw [Real.rpow_neg (by positivity), one_div, Real.rpow_two]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), ← h2]
  calc |(moebius d : ℝ)| * (d : ℝ) ^ (-(1 + η)) ≤ 1 * (d : ℝ) ^ (-(2 : ℝ)) :=
        mul_le_mul hμ hp (Real.rpow_nonneg (Nat.cast_nonneg d) _) zero_le_one
    _ = _ := one_mul _

/-- **The source is bounded above damping one**: `|P_η(m)| ≤ ζ(η) + 1` for `η > 1`. -/
theorem abs_centeredPrefix_le {η : ℝ} (hη : 1 < η) (m : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix η m| ≤ realZetaSeries η + 1 := by
  have hζ : 0 ≤ realZetaSeries η :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pmPowerDampedCenteredDivisorPrefix_eq]; simp; linarith
  set f : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (g := fun d : ℕ => (d : ℝ) ^ (-(1 + η))) ?_ fun d => ?_
    · exact Real.summable_nat_rpow.2 (by linarith)
    · rw [Real.norm_eq_abs, hfdef, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      have hμ : |(moebius d : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) hμ
  -- split the density series at `m`
  have hρ : (pmPowerDampedDivisorDensity η).re =
      ∑ d ∈ Icc 1 m, f d + ∑' j, f (j + (m + 1)) := by
    rw [density_re_eq_tsum (by linarith), ← sum_add_tsum_nat_add (m + 1) hfs]
    congr 1
    rw [range_eq_Ico, show Ico 0 (m + 1) = insert 0 (Icc 1 m) by
      ext d; simp only [mem_Ico, mem_insert, mem_Icc]; omega, sum_insert (by simp), hf0, zero_add]
  -- head: `Σ μ(d) d^{−η} (⌊m/d⌋ − m/d)`; tail: `m Σ_{d > m} μ(d) d^{−1−η}`
  have hhead : ∀ d ∈ Icc 1 m, f d * m = (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((m : ℝ) / d) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Icc.1 hd).1; positivity
    simp only [hfdef]
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0]
    field_simp
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum, hρ, add_mul, sum_mul,
    sum_congr rfl hhead]
  have e : (∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((m / d : ℕ) : ℝ)) -
      (∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((m : ℝ) / d) +
        (∑' j, f (j + (m + 1))) * m) =
      ∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) * (((m / d : ℕ) : ℝ) - (m : ℝ) / d) -
        (∑' j, f (j + (m + 1))) * m := by
    rw [← sub_sub, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun d _ => by ring
  rw [e]
  -- the head is at most `ζ(η)`
  have hH : |∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
      (((m / d : ℕ) : ℝ) - (m : ℝ) / d)| ≤ realZetaSeries η := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (sum_le_sum fun d hd => ?_) (by
      have := sum_Icc_rpow_le_realZetaSeries (ε := η - 1) (by linarith) m
      rwa [show 1 + (η - 1) = η by ring] at this)
    have hd1 := (mem_Icc.1 hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hμ : |(moebius d : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    -- `|⌊m/d⌋ − m/d| ≤ 1`
    have hfl : |((m / d : ℕ) : ℝ) - (m : ℝ) / d| ≤ 1 := by
      have hdm : (((m / d : ℕ) : ℝ)) * d + ((m % d : ℕ) : ℝ) = m := by
        exact_mod_cast Nat.div_mul_add_mod m d
      have hlt : ((m % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt m (by omega)
      have hq : ((m / d : ℕ) : ℝ) - (m : ℝ) / d = -(((m % d : ℕ) : ℝ) / d) := by
        field_simp; linarith
      rw [hq, abs_neg, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hd0,
        div_le_one hd0]
      exact hlt.le
    rw [show -(1 + (η - 1)) = -η by ring, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) * |((m / d : ℕ) : ℝ) - (m : ℝ) / d|
        ≤ 1 * (d : ℝ) ^ (-η) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg (Nat.cast_nonneg d) _))
            hfl (abs_nonneg _) (by positivity)
      _ = (d : ℝ) ^ (-η) := by ring
  -- the tail is at most `1`
  have hT : |(∑' j, f (j + (m + 1))) * m| ≤ 1 := by
    have hs2 : Summable fun j : ℕ => 1 / ((j + m + 1 : ℕ) : ℝ) ^ 2 := by
      have := (summable_nat_add_iff (m + 1)).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      refine this.congr fun j => ?_
      push_cast; ring_nf
    have hb : ∀ j, ‖f (j + (m + 1))‖ ≤ 1 / ((j + m + 1 : ℕ) : ℝ) ^ 2 := fun j => by
      rw [Real.norm_eq_abs, show j + m + 1 = j + (m + 1) by ring]
      exact abs_moebius_rpow_le hη.le (by omega)
    have h1 : |∑' j, f (j + (m + 1))| ≤ 1 / m :=
      (norm_tsum_le_tsum_norm (Summable.of_norm_bounded hs2 hb)).trans
        ((Summable.of_norm_bounded hs2 hb).norm.tsum_le_tsum hb hs2 |>.trans
          (tsum_inv_sq_tail_le hm))
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [abs_mul, abs_of_pos hm0]
    calc |∑' j, f (j + (m + 1))| * m ≤ 1 / m * m := mul_le_mul_of_nonneg_right h1 hm0.le
      _ = 1 := by field_simp
  calc _ ≤ |∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
        (((m / d : ℕ) : ℝ) - (m : ℝ) / d)| + |(∑' j, f (j + (m + 1))) * m| := abs_sub _ _
    _ ≤ _ := add_le_add hH hT

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
