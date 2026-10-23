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

The column bound `(k+1)^{1−2η}` is summable exactly when `η > 1`; between half damping and one the
size of the source does not decide `ℓ²`-boundedness of the chain.
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
    ∑' j : ℕ, 1 / ((j + m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun j => by positivity) fun J => ?_
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
    rw [density_re_eq_tsum (by linarith), ← hfs.sum_add_tsum_nat_add (m + 1)]
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
      have hdm : (d : ℝ) * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) = m := by
        exact_mod_cast Nat.div_add_mod m d
      have hlt : ((m % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt m (by omega)
      have hq : ((m / d : ℕ) : ℝ) - (m : ℝ) / d = -(((m % d : ℕ) : ℝ) / d) := by
        field_simp; linarith
      rw [hq, abs_neg, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hd0,
        div_le_one hd0]
      exact hlt.le
    rw [abs_mul, abs_mul,
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
    have hsf : Summable fun j => f (j + (m + 1)) := Summable.of_norm_bounded hs2 hb
    have h1 : |∑' j, f (j + (m + 1))| ≤ 1 / m :=
      (norm_tsum_le_tsum_norm hsf.norm).trans
        ((hsf.norm.tsum_le_tsum hb hs2).trans (tsum_inv_sq_tail_le hm))
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [abs_mul, abs_of_pos hm0]
    calc |∑' j, f (j + (m + 1))| * m ≤ 1 / m * m := mul_le_mul_of_nonneg_right h1 hm0.le
      _ = 1 := by field_simp
  calc _ ≤ |∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
        (((m / d : ℕ) : ℝ) - (m : ℝ) / d)| + |(∑' j, f (j + (m + 1))) * m| := abs_sub _ _
    _ ≤ _ := add_le_add hH hT

/-! ### The kernel of the chain -/

/-- `A_η(x) = ρ x + P_η(x)`. -/
theorem arithmeticDampingPrefix_eq (η : ℝ) (x : ℕ) :
    arithmeticDampingPrefix η x =
      (pmPowerDampedDivisorDensity η).re * x + pmPowerDampedCenteredDivisorPrefix η x := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]; unfold arithmeticDampingPrefix; ring

/-- `|⌊N/K⌋ − N/K| ≤ 1`. -/
theorem abs_natDiv_sub_div_le (N K : ℕ) (hK : 0 < K) :
    |((N / K : ℕ) : ℝ) - (N : ℝ) / K| ≤ 1 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hdm : (K : ℝ) * ((N / K : ℕ) : ℝ) + ((N % K : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.div_add_mod N K
  have hlt : ((N % K : ℕ) : ℝ) < K := by exact_mod_cast Nat.mod_lt N hK
  have hq : ((N / K : ℕ) : ℝ) - (N : ℝ) / K = -(((N % K : ℕ) : ℝ) / K) := by
    field_simp; linarith
  rw [hq, abs_neg, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hK0, div_le_one hK0]
  exact hlt.le

/-- The entrance mass is at most `ρ (k+1)^{−η}`. -/
theorem entrance_le {η : ℝ} (hη : 0 < η) (k : ℕ) :
    arithmeticDampingEntrance η (k + 1) ≤
      (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-η) := by
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  unfold arithmeticDampingEntrance
  have h1 : ((k + 1 + 1 : ℕ) : ℝ) ^ (-1 - η) ≥ 0 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-1 - η) = ((k + 1 : ℕ) : ℝ) ^ (-η) := by
    rw [show -1 - η = -η - 1 by ring, Real.rpow_sub_one hK.ne']
    field_simp
  calc (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) ^ (-1 - η) - ((k + 1 + 1 : ℕ) : ℝ) ^ (-1 - η))
      ≤ (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-1 - η) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by rw [mul_assoc, h2]

/-- **Kernel identity**: with `a = ⌊N/K⌋`, `a' = ⌊N/(K+1)⌋`,
`C(n,k) = (K/N)(K^{−η}(ρ(a − N/K) + P(a)) − (K+1)^{−η}(ρ(a' − N/(K+1)) + P(a')))`. -/
theorem centeredRow_eq (η : ℝ) (n k : ℕ) :
    arithmeticDampingCenteredRow η n k =
      ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) ^ (-η) * ((pmPowerDampedDivisorDensity η).re *
            ((((n + 1) / (k + 1) : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) +
            pmPowerDampedCenteredDivisorPrefix η ((n + 1) / (k + 1))) -
          ((k + 1 + 1 : ℕ) : ℝ) ^ (-η) * ((pmPowerDampedDivisorDensity η).re *
            ((((n + 1) / (k + 1 + 1) : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) / ((k + 1 + 1 : ℕ) : ℝ)) +
            pmPowerDampedCenteredDivisorPrefix η ((n + 1) / (k + 1 + 1)))) := by
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hK' : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold arithmeticDampingCenteredRow arithmeticDampingTransition arithmeticDampingEntrance
  rw [arithmeticDampingPrefix_eq, arithmeticDampingPrefix_eq,
    show -1 - η = -η - 1 by ring, Real.rpow_sub_one hK.ne', Real.rpow_sub_one hK'.ne']
  field_simp
  ring

/-- **Kernel bound**: for `k ≤ n` the centred entry is at most
`2(ρ + ζ(η) + 1) (k+1)^{1−η}/(n+1)`. -/
theorem abs_centeredRow_le {η : ℝ} (hη : 1 < η) (n k : ℕ) :
    |arithmeticDampingCenteredRow η n k| ≤
      2 * ((pmPowerDampedDivisorDensity η).re + (realZetaSeries η + 1)) *
        ((k + 1 : ℕ) : ℝ) ^ (1 - η) / ((n + 1 : ℕ) : ℝ) := by
  set ρ := (pmPowerDampedDivisorDensity η).re
  set B := realZetaSeries η + 1
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos (by linarith)
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  set K' : ℝ := ((k + 1 + 1 : ℕ) : ℝ) with hK'def
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hK : 0 < K := by positivity
  have hK' : 0 < K' := by positivity
  have hN : 0 < N := by positivity
  set a := (n + 1) / (k + 1)
  set a' := (n + 1) / (k + 1 + 1)
  -- centre the floors: `R = (K/N)(K^{−η}(ρ(a − N/K) + P a) − K'^{−η}(ρ(a' − N/K') + P a'))`
  have hR : arithmeticDampingCenteredRow η n k =
      K / N * (K ^ (-η) * (ρ * ((a : ℝ) - N / K) + pmPowerDampedCenteredDivisorPrefix η a) -
        K' ^ (-η) * (ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a')) :=
    centeredRow_eq η n k
  have hPa := abs_centeredPrefix_le hη a
  have hPa' := abs_centeredPrefix_le hη a'
  have hfa := abs_natDiv_sub_div_le (n + 1) (k + 1) (by omega)
  have hfa' := abs_natDiv_sub_div_le (n + 1) (k + 1 + 1) (by omega)
  have hb1 : |ρ * ((a : ℝ) - N / K) + pmPowerDampedCenteredDivisorPrefix η a| ≤ ρ + B := by
    refine (abs_add_le _ _).trans (add_le_add ?_ hPa)
    rw [abs_mul, abs_of_pos hρ]
    exact mul_le_of_le_one_right hρ.le hfa
  have hb2 : |ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a'| ≤ ρ + B := by
    refine (abs_add_le _ _).trans (add_le_add ?_ hPa')
    rw [abs_mul, abs_of_pos hρ]
    exact mul_le_of_le_one_right hρ.le hfa'
  have hKK : K' ^ (-η) ≤ K ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hK (by simp only [hKdef, hK'def]; push_cast; linarith)
      (by linarith)
  have hpos1 : 0 ≤ K ^ (-η) := Real.rpow_nonneg hK.le _
  have hpos2 : 0 ≤ K' ^ (-η) := Real.rpow_nonneg hK'.le _
  have hexp : K ^ (1 - η) = K * K ^ (-η) := by
    rw [show 1 - η = 1 + -η by ring, Real.rpow_add hK, Real.rpow_one]
  rw [hR, hexp, abs_mul, abs_of_pos (div_pos hK hN)]
  have hin : |K ^ (-η) * (ρ * ((a : ℝ) - N / K) + pmPowerDampedCenteredDivisorPrefix η a) -
      K' ^ (-η) * (ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a')| ≤
      2 * (ρ + B) * K ^ (-η) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hpos1, abs_of_nonneg hpos2]
    nlinarith [abs_nonneg (ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a')]
  calc K / N * |K ^ (-η) * (ρ * ((a : ℝ) - N / K) + pmPowerDampedCenteredDivisorPrefix η a) -
        K' ^ (-η) * (ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a')|
      ≤ K / N * (2 * (ρ + B) * K ^ (-η)) := mul_le_mul_of_nonneg_left hin (div_pos hK hN).le
    _ = 2 * (ρ + B) * (K * K ^ (-η)) / N := by ring

/-! ### Hilbert–Schmidt bound -/

/-- `Σ_{k ≤ n < T} 1/(n+1)² ≤ 2/(k+1) − 2/(max k T + 1)`, by telescoping
`1/(n+1)² ≤ 2/(n+1) − 2/(n+2)`. -/
theorem sum_range_ite_inv_sq_le (k : ℕ) : ∀ T : ℕ,
    ∑ n ∈ range T, (if k ≤ n then 1 / ((n + 1 : ℕ) : ℝ) ^ 2 else 0) ≤
      2 / ((k + 1 : ℕ) : ℝ) - 2 / ((max k T + 1 : ℕ) : ℝ)
  | 0 => by simp
  | T + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_range_ite_inv_sq_le k T
    by_cases hkT : k ≤ T
    · rw [if_pos hkT, max_eq_right (by omega : k ≤ T + 1)]
      rw [max_eq_right hkT] at ih
      have hT : (1 : ℝ) / ((T + 1 : ℕ) : ℝ) ^ 2 ≤
          2 / ((T + 1 : ℕ) : ℝ) - 2 / ((T + 1 + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · rw [if_neg hkT, add_zero, max_eq_left (by omega : T + 1 ≤ k)]
      rwa [max_eq_left (by omega : T ≤ k)] at ih

/-- **Column bound**: `Σ_{n<T} C(n,k)² ≤ (8(ρ + ζ(η) + 1)² + ρ²) (k+1)^{1−2η}`. -/
theorem sum_sq_centeredRow_le {η : ℝ} (hη : 1 < η) (k T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      (2 * (2 * ((pmPowerDampedDivisorDensity η).re + (realZetaSeries η + 1))) ^ 2 +
        (pmPowerDampedDivisorDensity η).re ^ 2) * ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * η) := by
  set ρ := (pmPowerDampedDivisorDensity η).re
  set c := 2 * (ρ + (realZetaSeries η + 1))
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  have hK : 0 < K := by positivity
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos (by linarith)
  -- pointwise bound by the two regimes
  have hpt : ∀ n, arithmeticDampingCenteredRow η n k ^ 2 ≤
      (if k ≤ n then c ^ 2 * K ^ (2 - 2 * η) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) else 0) +
        (if k ≤ n then 0 else ρ ^ 2 * K ^ (-2 * η)) := by
    intro n
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, if_pos hkn, add_zero]
      have h := abs_centeredRow_le hη n k
      have hsq : arithmeticDampingCenteredRow η n k ^ 2 ≤
          (c * K ^ (1 - η) / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have he : K ^ (2 - 2 * η) = (K ^ (1 - η)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]; push_cast; ring_nf
      rw [he]
      calc _ ≤ (c * K ^ (1 - η) / ((n + 1 : ℕ) : ℝ)) ^ 2 := hsq
        _ = _ := by ring
    · rw [if_neg hkn, if_neg hkn, zero_add]
      have hzero : arithmeticDampingTransition η (n + 1) (k + 1) = 0 :=
        arithmeticDampingTransition_eq_zero_of_lt η (by omega)
      have he0 := arithmeticDampingEntrance_nonneg (by linarith : 0 < η) (k + 1)
      have hle := entrance_le (by linarith : 0 < η) k
      have hR : arithmeticDampingCenteredRow η n k = -arithmeticDampingEntrance η (k + 1) := by
        unfold arithmeticDampingCenteredRow; rw [hzero, zero_sub]
      have he : K ^ (-2 * η) = (K ^ (-η)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]; push_cast; ring_nf
      rw [hR, neg_sq, he, ← mul_pow]
      exact pow_le_pow_left₀ he0 hle 2
  refine (sum_le_sum fun n _ => hpt n).trans ?_
  rw [sum_add_distrib]
  -- the regime `k ≤ n` telescopes, the regime `n < k` has at most `k` terms
  have h1 : ∑ n ∈ range T, (if k ≤ n then c ^ 2 * K ^ (2 - 2 * η) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      else 0) ≤ 2 * c ^ 2 * K ^ (1 - 2 * η) := by
    have hs : ∑ n ∈ range T, (if k ≤ n then c ^ 2 * K ^ (2 - 2 * η) *
        (1 / ((n + 1 : ℕ) : ℝ) ^ 2) else 0) = c ^ 2 * K ^ (2 - 2 * η) *
        ∑ n ∈ range T, (if k ≤ n then 1 / ((n + 1 : ℕ) : ℝ) ^ 2 else 0) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by split_ifs <;> ring
    have ht := sum_range_ite_inv_sq_le k T
    have hpos : 0 ≤ 2 / ((max k T + 1 : ℕ) : ℝ) := by positivity
    have hc : 0 ≤ c ^ 2 * K ^ (2 - 2 * η) := by positivity
    have hexp : K ^ (2 - 2 * η) * (2 / K) = 2 * K ^ (1 - 2 * η) := by
      rw [show 2 - 2 * η = (1 - 2 * η) + 1 by ring, Real.rpow_add hK, Real.rpow_one]
      field_simp
    rw [hs]
    calc c ^ 2 * K ^ (2 - 2 * η) *
          ∑ n ∈ range T, (if k ≤ n then 1 / ((n + 1 : ℕ) : ℝ) ^ 2 else 0)
        ≤ c ^ 2 * K ^ (2 - 2 * η) * (2 / K) := mul_le_mul_of_nonneg_left (by linarith) hc
      _ = 2 * c ^ 2 * K ^ (1 - 2 * η) := by rw [mul_assoc, hexp]; ring
  have h2 : ∑ n ∈ range T, (if k ≤ n then 0 else ρ ^ 2 * K ^ (-2 * η)) ≤
      ρ ^ 2 * K ^ (1 - 2 * η) := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    have hcard : ((filter (fun n => ¬ k ≤ n) (range T)).card : ℝ) ≤ K := by
      have : (filter (fun n => ¬ k ≤ n) (range T)).card ≤ k + 1 := by
        refine (card_le_card fun n hn => ?_).trans (card_range (k + 1)).le
        simp only [mem_filter, mem_range] at hn ⊢; omega
      simp only [hKdef]; exact_mod_cast this
    have hexp : K * K ^ (-2 * η) = K ^ (1 - 2 * η) := by
      rw [show 1 - 2 * η = 1 + -2 * η by ring, Real.rpow_add hK, Real.rpow_one]
    calc ((filter (fun n => ¬ k ≤ n) (range T)).card : ℝ) * (ρ ^ 2 * K ^ (-2 * η))
        ≤ K * (ρ ^ 2 * K ^ (-2 * η)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ρ ^ 2 * K ^ (1 - 2 * η) := by rw [← hexp]; ring
  have hcK : 2 * c ^ 2 * K ^ (1 - 2 * η) + ρ ^ 2 * K ^ (1 - 2 * η) =
      (2 * c ^ 2 + ρ ^ 2) * K ^ (1 - 2 * η) := by ring
  linarith

/-- The Hilbert–Schmidt constant `(8(ρ + ζ(η) + 1)² + ρ²) ζ(2η − 1)` of the chain. -/
def chainHilbertSchmidtConstant (η : ℝ) : ℝ :=
  (2 * (2 * ((pmPowerDampedDivisorDensity η).re + (realZetaSeries η + 1))) ^ 2 +
    (pmPowerDampedDivisorDensity η).re ^ 2) * realZetaSeries (2 * η - 1)

/-- **The chain is bounded in `ℓ²` above damping one**: for finitely supported `b` and every
horizon, `Σ_{n<T} (C_η b)(n)² ≤ M_η Σ_k b_k²`. -/
theorem centeredOperator_l2_le {η : ℝ} (hη : 1 < η) (b : C₀(ℕ, ℝ)) {N : ℕ}
    (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
      chainHilbertSchmidtConstant η * ∑ k ∈ range N, b k ^ 2 := by
  have hη0 : (0 : ℝ) < η := by linarith
  set M := 2 * (2 * ((pmPowerDampedDivisorDensity η).re + (realZetaSeries η + 1))) ^ 2 +
    (pmPowerDampedDivisorDensity η).re ^ 2
  have hM : 0 ≤ M := by positivity
  -- finite support turns the action into a finite sum
  have happ : ∀ n, arithmeticDampingCenteredOperator hη0 b n =
      ∑ k ∈ range N, arithmeticDampingCenteredRow η n k * b k := by
    intro n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by
      rw [hb k (by simpa using hk), mul_zero]
  have hrow : ∀ n, arithmeticDampingCenteredOperator hη0 b n ^ 2 ≤
      (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) * ∑ k ∈ range N, b k ^ 2 := by
    intro n; rw [happ]; exact sum_mul_sq_le_sq_mul_sq _ _ _
  have hcols : ∑ k ∈ range N, ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
      M * realZetaSeries (2 * η - 1) := by
    have hz : ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * η) ≤ realZetaSeries (2 * η - 1) := by
      have hs := summable_realZetaTerm (s := 2 * η - 1) (by linarith)
      refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_))
        (hs.sum_le_tsum (range N) fun k _ => Real.rpow_nonneg (by positivity) _)
      push_cast; ring_nf
    calc ∑ k ∈ range N, ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2
        ≤ ∑ k ∈ range N, M * ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * η) :=
          sum_le_sum fun k _ => sum_sq_centeredRow_le hη k T
      _ = M * ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * η) := by rw [mul_sum]
      _ ≤ M * realZetaSeries (2 * η - 1) := mul_le_mul_of_nonneg_left hz hM
  have hb0 : 0 ≤ ∑ k ∈ range N, b k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  calc ∑ n ∈ range T, arithmeticDampingCenteredOperator hη0 b n ^ 2
      ≤ ∑ n ∈ range T, (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := sum_le_sum fun n _ => hrow n
    _ = (∑ k ∈ range N, ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := by rw [← sum_mul, sum_comm]
    _ ≤ M * realZetaSeries (2 * η - 1) * ∑ k ∈ range N, b k ^ 2 :=
          mul_le_mul_of_nonneg_right hcols hb0
    _ = _ := rfl

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
