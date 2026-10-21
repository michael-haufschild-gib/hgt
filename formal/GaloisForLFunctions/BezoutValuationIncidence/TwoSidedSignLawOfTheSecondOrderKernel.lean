import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveDispersionForBoundedRows

/-!
# The two-sided sign law of the second-order kernel

`Φ_d(m) = (d²/2) B₂({m/d}) - 1/12`, so the Bernoulli kernel is `𝔅(d, n) = (d²/2) Σ_j B₂({jn/d})/j² - π²/72`.
Near the residue `d/2`, write `n mod d = d(1/2 + σ)`. For `k ≤ 16` and `|σ| ≤ 1/64`,

`B₂({k/2 + kσ}) = (kσ)² - 1/12` (k odd),  `≤ (kσ)² + 1/6` (k even),

and `B₂ ≤ 1/6` beyond. The odd terms dominate:
`Σ_{k ≤ 16} c_k/k² ≤ -(1/12)·1.2025 + (1/6)·0.3818 < -0.0365`. With `16σ² ≤ 1/256` and the tail
`1/(6·16)`,

`|n mod d - d/2| ≤ d/64  ⟹  𝔅(d, n) ≤ -d²/100`.

Together with `𝔅(d, n) ≥ d²/25 - 1/4` at `n mod d ≤ d/32`, the second-order cross-scale term changes sign
at full size `≍ d²`. For two primes `p < q`, by the second-order law,

`𝒢^{ec}(p, q) - [D_p log q - p β_p] ≤ -p²/(100 q) + ¾ p³/q²`  when `|q mod p - p/2| ≤ p/64`,

`𝒢^{ec}(p, q) - [D_p log q - p β_p] ≥ (p²/25 - 1/4)/q - ¾ p³/q²`  when `q mod p ≤ p/32`.

Relative to the rank-two prediction, the pronic Gram of two primes oscillates in sign with the residue
of the large prime, at amplitude `≍ p²/q`. No one-sided estimate of the remainder improves the rank-two
remainder bound by more than a constant factor.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. `B₂` near the half and near the integers -/

theorem bernoulliTwo_fract_half_add {t : ℝ} (ht : |t| ≤ 1 / 4) :
    bernoulliTwo (Int.fract (1 / 2 + t)) = t ^ 2 - 1 / 12 := by
  have h1 : Int.fract (1 / 2 + t) = 1 / 2 + t := by
    rw [Int.fract_eq_self]; constructor <;> linarith [abs_le.mp ht]
  rw [h1, bernoulliTwo]; ring

theorem bernoulliTwo_fract_le {t : ℝ} (ht : |t| ≤ 1 / 4) :
    bernoulliTwo (Int.fract t) ≤ t ^ 2 + 1 / 6 := by
  rcases le_or_gt 0 t with h | h
  · have h1 : Int.fract t = t := by
      rw [Int.fract_eq_self]; constructor <;> linarith [abs_le.mp ht]
    rw [h1, bernoulliTwo]; nlinarith
  · have h1 : Int.fract t = 1 + t := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [abs_le.mp ht], by linarith, -1, by push_cast; ring⟩
    rw [h1, bernoulliTwo]; nlinarith

theorem bernoulliTwo_fract_le_sixth (x : ℝ) : bernoulliTwo (Int.fract x) ≤ 1 / 6 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [bernoulliTwo]; nlinarith

/-- The `k`-th term near the half: `B₂({k(1/2 + σ)}) ≤ (kσ)² + c_k` with `c_k = -1/12` for odd `k`
and `1/6` for even `k`, when `|kσ| ≤ 1/4`. -/
theorem bernoulliTwo_fract_mul_half_add_le (k : ℕ) {σ : ℝ} (hk : |(k : ℝ) * σ| ≤ 1 / 4) :
    bernoulliTwo (Int.fract ((k : ℝ) * (1 / 2 + σ))) ≤
      ((k : ℝ) * σ) ^ 2 + (if k % 2 = 1 then -1 / 12 else 1 / 6) := by
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k
  · subst hi
    have hmod : (2 * i) % 2 = 0 := by omega
    rw [if_neg (by omega)]
    have : ((2 * i : ℕ) : ℝ) * (1 / 2 + σ) = ((2 * i : ℕ) : ℝ) * σ + (i : ℤ) := by push_cast; ring
    rw [this, Int.fract_add_intCast]
    exact bernoulliTwo_fract_le hk
  · subst hi
    rw [if_pos (by omega)]
    have : ((2 * i + 1 : ℕ) : ℝ) * (1 / 2 + σ) = (1 / 2 + ((2 * i + 1 : ℕ) : ℝ) * σ) + (i : ℤ) := by
      push_cast; ring
    rw [this, Int.fract_add_intCast, bernoulliTwo_fract_half_add hk]
    linarith

/-! ## §2. Negativity near the half -/

/-- `Φ_d(M) = (d²/2) B₂({M/d}) - 1/12`. -/
theorem residuePotential_eq_bernoulliTwo_fract {d : ℕ} (hd : 0 < d) (M : ℕ) :
    residuePotential d M = (d : ℝ) ^ 2 / 2 * bernoulliTwo (Int.fract ((M : ℝ) / d)) - 1 / 12 := by
  rw [residuePotential_eq_bernoulli hd, Int.fract_div_natCast_eq_div_natCast_mod, bernoulliTwo]

theorem fract_mul_div_eq {d n k : ℕ} (hd : 0 < d) :
    Int.fract (((k * n : ℕ) : ℝ) / d) =
      Int.fract ((k : ℝ) * (1 / 2 + (((n % d : ℕ) : ℝ) / d - 1 / 2))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (n : ℝ) = d * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n d).symm
  have hz : ((((k * (n / d) : ℕ) : ℤ)) : ℝ) = (k : ℝ) * ((n / d : ℕ) : ℝ) := by
    rw [Int.cast_natCast, Nat.cast_mul]
  have h : ((k * n : ℕ) : ℝ) / d = (k : ℝ) * (1 / 2 + (((n % d : ℕ) : ℝ) / d - 1 / 2)) +
      ((k * (n / d) : ℕ) : ℤ) := by
    rw [hz, Nat.cast_mul, hn]; field_simp; ring
  rw [h, Int.fract_add_intCast]

/-- **Negativity near the half.** If `|n mod d / d - 1/2| ≤ 1/64` then `𝔅(d, n) ≤ -d²/100`. -/
theorem bernoulliKernel_le_of_near_half {d n : ℕ} (hd : 0 < d)
    (hn : |((n % d : ℕ) : ℝ) / d - 1 / 2| ≤ 1 / 64) :
    bernoulliKernel d n ≤ -((d : ℝ) ^ 2 / 100) := by
  set σ : ℝ := ((n % d : ℕ) : ℝ) / d - 1 / 2 with hσ
  have hS := summable_residuePotential_div_sq hd n
  have hsplit := (hS.sum_add_tsum_nat_add 16).symm
  rw [bernoulliKernel, hsplit]
  -- the first sixteen terms
  have hhead : ∑ j ∈ range 16, residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 ≤
      (d : ℝ) ^ 2 / 2 * (16 * σ ^ 2 + ∑ j ∈ range 16,
        (if (j + 1) % 2 = 1 then -1 / 12 else 1 / 6) / ((j : ℝ) + 1) ^ 2) := by
    calc ∑ j ∈ range 16, residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2
        ≤ ∑ j ∈ range 16, (d : ℝ) ^ 2 / 2 * (σ ^ 2 +
            (if (j + 1) % 2 = 1 then -1 / 12 else 1 / 6) / ((j : ℝ) + 1) ^ 2) := by
          refine sum_le_sum fun j hj => ?_
          have hj16 := mem_range.mp hj
          have hk : |((j + 1 : ℕ) : ℝ) * σ| ≤ 1 / 4 := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            have : ((j + 1 : ℕ) : ℝ) ≤ 16 := by exact_mod_cast (by omega : j + 1 ≤ 16)
            nlinarith [abs_nonneg σ]
          have hB := bernoulliTwo_fract_mul_half_add_le (j + 1) hk
          rw [residuePotential_eq_bernoulliTwo_fract hd, fract_mul_div_eq hd, ← hσ]
          have hpos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
          have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 / 2 := by positivity
          rw [div_le_iff₀ hpos]
          have e : (d : ℝ) ^ 2 / 2 * (σ ^ 2 + (if (j + 1) % 2 = 1 then -1 / 12 else 1 / 6) /
              ((j : ℝ) + 1) ^ 2) * ((j : ℝ) + 1) ^ 2 = (d : ℝ) ^ 2 / 2 * ((((j + 1 : ℕ) : ℝ) * σ) ^ 2 +
              (if (j + 1) % 2 = 1 then -1 / 12 else 1 / 6)) := by push_cast; field_simp
          rw [e]
          nlinarith [mul_le_mul_of_nonneg_left hB hd2]
      _ = (d : ℝ) ^ 2 / 2 * (16 * σ ^ 2 + ∑ j ∈ range 16,
            (if (j + 1) % 2 = 1 then -1 / 12 else 1 / 6) / ((j : ℝ) + 1) ^ 2) := by
          rw [← mul_sum, sum_add_distrib, sum_const, card_range]; ring
  -- the tail
  have htail : ∑' j, residuePotential d ((j + 16 + 1) * n) / (((j + 16 : ℕ) : ℝ) + 1) ^ 2 ≤
      (d : ℝ) ^ 2 / 12 * (1 / 16) := by
    have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
      have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
      simpa using this
    have hzs := hz.summable
    have htz : ∑' j : ℕ, 1 / (((j + 16 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / 16 := by
      have h1 := abs_hasSum_sub_partial_le hz zero_le_one
        (fun h => le_of_eq (abs_of_nonneg (by positivity))) (H₁ := 16) (by norm_num)
      have h2 := hzs.sum_add_tsum_nat_add 16
      rw [hz.tsum_eq] at h2
      have : ∑' j : ℕ, 1 / (((j + 16 : ℕ) : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 -
          ∑ i ∈ range 16, 1 / ((i : ℝ) + 1) ^ 2 := by
        rw [← h2]; push_cast; ring
      rw [this]; linarith [(abs_le.mp h1).2]
    calc ∑' j, residuePotential d ((j + 16 + 1) * n) / (((j + 16 : ℕ) : ℝ) + 1) ^ 2
        ≤ ∑' j : ℕ, (d : ℝ) ^ 2 / 12 * (1 / (((j + 16 : ℕ) : ℝ) + 1) ^ 2) := by
          refine Summable.tsum_le_tsum (fun j => ?_) ((summable_nat_add_iff 16).mpr hS)
            (((summable_nat_add_iff 16).mpr hzs).mul_left _)
          rw [div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 := residuePotential_le_zero_value hd ((j + 16 + 1) * n)
          have h0 : residuePotential d 0 = ((d : ℝ) ^ 2 - 1) / 12 := by simp [residuePotential]
          linarith
      _ = (d : ℝ) ^ 2 / 12 * ∑' j : ℕ, 1 / (((j + 16 : ℕ) : ℝ) + 1) ^ 2 := tsum_mul_left
      _ ≤ (d : ℝ) ^ 2 / 12 * (1 / 16) := mul_le_mul_of_nonneg_left htz (by positivity)
  have hσ2 : σ ^ 2 ≤ (1 / 64) ^ 2 := by
    have := abs_nonneg σ
    nlinarith [sq_abs σ]
  have hC : ∑ j ∈ range 16, (if (j + 1) % 2 = 1 then (-1 / 12 : ℝ) else 1 / 6) / ((j : ℝ) + 1) ^ 2 ≤
      -(73 / 2000) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have : (d : ℝ) ^ 2 / 2 * (16 * σ ^ 2 + ∑ j ∈ range 16,
      (if (j + 1) % 2 = 1 then (-1 / 12 : ℝ) else 1 / 6) / ((j : ℝ) + 1) ^ 2) ≤
      (d : ℝ) ^ 2 / 2 * (16 * (1 / 64) ^ 2 + -(73 / 2000)) := by gcongr
  linarith [hhead, htail]

/-! ## §3. Two primes -/

/-- **Two-sided second-order sign law for two primes.** With the rank-two prediction
`D_p log q - p β_p`: near the half the Gram lies below it by `≥ p²/(100q) - ¾p³/q²`, near zero it lies
above it by `≥ (p²/25 - 1/4)/q - ¾p³/q²`. -/
theorem pmRamanujanEnergyCenteredGram_two_sided_sign {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p ≤ N) (hqN : q ≤ N) :
    (|((q % p : ℕ) : ℝ) / p - 1 / 2| ≤ 1 / 64 →
      pmRamanujanEnergyCenteredGram p q - ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
        p * rowBeta N (unitRow p)) ≤ -((p : ℝ) ^ 2 / (100 * q)) + 3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2) ∧
    (32 * (q % p) ≤ p →
      ((p : ℝ) ^ 2 / 25 - 1 / 4) / q - 3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 ≤
        pmRamanujanEnergyCenteredGram p q - ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
          p * rowBeta N (unitRow p))) := by
  have h := abs_pmRamanujanEnergyCenteredGram_sub_second_order_le hp hq hpN hqN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hab := abs_le.mp h
  constructor
  · intro hhalf
    have hk := bernoulliKernel_le_of_near_half hp.pos hhalf
    have : bernoulliKernel p q / q ≤ -((p : ℝ) ^ 2 / 100) / q :=
      div_le_div_of_nonneg_right hk hqR.le
    have e : -((p : ℝ) ^ 2 / 100) / q = -((p : ℝ) ^ 2 / (100 * q)) := by field_simp
    linarith [hab.2]
  · intro hzero
    have hk := bernoulliKernel_ge hp.pos hzero
    have : ((p : ℝ) ^ 2 / 25 - 1 / 4) / q ≤ bernoulliKernel p q / q :=
      div_le_div_of_nonneg_right hk hqR.le
    linarith [hab.1]

end

end GaloisForLFunctions.BezoutValuationIncidence
