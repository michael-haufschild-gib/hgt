import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicHighLadderError
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicTruncatedLadderError

/-!
# Full-range harmonic ladder error at Menon's schedule

The truncated prefix has the previously established hard-support budget.  Above its endpoint,
prime/cofactor products are injective, so the high suffix has overlap one.  Together these bounds
control the exact ladder over the full final designated-prime range.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- The truncated ladder depth is eventually a prefix of the full final-range depth. -/
theorem eventually_menonTruncatedRangeLadderSteps_le_finalRangeLadderSteps :
    ∀ᶠ x : ℝ in atTop,
      menonTruncatedRangeLadderSteps x ≤ menonFinalRangeLadderSteps x := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic] with x hx
  rcases hx with ⟨hxone, hlogOne, hH, hQ, htop, _, _⟩
  have hQ0 : 0 < menonFinalRangeLadderBase x := menonFinalRangeLadderBase_pos hQ
  have htruncTop : (menonTruncatedPrimeTopNat x : ℝ) ≤
      (menonFinalRangeTopNat x : ℝ) := by
    rw [menonTruncatedPrimeTopNat, menonFinalRangeTopNat]
    exact_mod_cast Nat.floor_mono (by
      rw [menonTruncatedPrimeTop]
      have hpow : 1 ≤ (Real.log x) ^ (20 : ℕ) := one_le_pow₀ hlogOne
      exact (div_le_self (by linarith) hpow).trans (by linarith))
  have hratio : (menonTruncatedPrimeTopNat x : ℝ) /
      menonFinalRangeLadderBase x ≤
      (menonFinalRangeTopNat x : ℝ) / menonFinalRangeLadderBase x :=
    div_le_div_of_nonneg_right htruncTop hQ0.le
  have hratio0 : 0 < (menonTruncatedPrimeTopNat x : ℝ) /
      menonFinalRangeLadderBase x := div_pos (lt_trans (menonFinalRangeLadderBase_pos hQ) htop) hQ0
  have hlog := Real.log_le_log hratio0 hratio
  have harg := mul_le_mul_of_nonneg_left hlog hH.le
  rw [menonTruncatedRangeLadderSteps, menonFinalRangeLadderSteps]
  exact Nat.ceil_mono harg

/-- The truncated natural endpoint is eventually positive and quadratically above the ambient
cofactor top. -/
theorem eventually_menonFinalRangeTopNat_lt_truncatedPrimeTopNat_sq :
    ∀ᶠ x : ℝ in atTop,
      0 < menonTruncatedPrimeTopNat x ∧
      (menonFinalRangeTopNat x : ℝ) < (menonTruncatedPrimeTopNat x : ℝ) ^ 2 := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_const_mul_one_add_log_pow_le_rpow
      (δ := (1 : ℝ)) (c := 13) (by norm_num) (by norm_num) 40] with x hx hgrowth
  rcases hx with ⟨hxone, hlogOne, _, hQ, htop, _, _⟩
  have hx0 : 0 < x := lt_trans zero_lt_one hxone
  have hlog0 : 0 < Real.log x := Real.log_pos hxone
  have hlog20 : 0 < (Real.log x) ^ (20 : ℕ) := pow_pos hlog0 _
  have hlog20_le_40 : (Real.log x) ^ (20 : ℕ) ≤ (Real.log x) ^ (40 : ℕ) :=
    pow_le_pow_right₀ hlogOne (by omega)
  have hlog40_le : (Real.log x) ^ (40 : ℕ) ≤
      (1 + Real.log x) ^ (40 : ℕ) := by
    exact pow_le_pow_left₀ hlog0.le (by linarith) 40
  have hcore : 12 * (Real.log x) ^ (40 : ℕ) < x := by
    have h13 : 13 * (Real.log x) ^ (40 : ℕ) ≤ x :=
      (mul_le_mul_of_nonneg_left hlog40_le (by norm_num)).trans (by simpa using hgrowth)
    calc
      12 * (Real.log x) ^ (40 : ℕ) < 13 * (Real.log x) ^ (40 : ℕ) := by
        nlinarith [pow_pos hlog0 40]
      _ ≤ x := h13
  have htopTwo : 2 ≤ menonTruncatedPrimeTop x := by
    rw [menonTruncatedPrimeTop, le_div_iff₀ hlog20]
    exact le_of_lt ((by
      calc
        2 * (Real.log x) ^ (20 : ℕ) ≤ 12 * (Real.log x) ^ (40 : ℕ) := by
          nlinarith [hlog20_le_40, pow_pos hlog0 20]
        _ < x := hcore) : 2 * (Real.log x) ^ (20 : ℕ) < x)
  have hUfloor : menonTruncatedPrimeTop x - 1 <
      (menonTruncatedPrimeTopNat x : ℝ) := by
    rw [menonTruncatedPrimeTopNat]
    have hfloor := Nat.lt_floor_add_one (menonTruncatedPrimeTop x)
    linarith
  have hUhalf : menonTruncatedPrimeTop x / 2 ≤
      (menonTruncatedPrimeTopNat x : ℝ) := by linarith
  have hUposR : 0 < (menonTruncatedPrimeTopNat x : ℝ) := by
    have : 1 ≤ (menonTruncatedPrimeTopNat x : ℝ) := by linarith
    linarith
  have hB : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hhalfSq : 3 * x < (menonTruncatedPrimeTop x / 2) ^ 2 := by
    rw [menonTruncatedPrimeTop]
    field_simp
    ring_nf at hcore ⊢
    simpa [mul_comm] using hcore
  have hsq : (menonTruncatedPrimeTop x / 2) ^ 2 ≤
      (menonTruncatedPrimeTopNat x : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hUhalf 2
  exact ⟨by exact_mod_cast hUposR, lt_of_le_of_lt hB (hhalfSq.trans_le hsq)⟩

set_option maxHeartbeats 1000000 in
/-- Menon's actual high-suffix budget is smaller than eight negative logarithmic powers, uniformly
for receiver heights between zero and `x`. -/
theorem eventually_menonFinalRange_highLadderErrorBudget_le_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ x →
      menonHarmonicHighLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderEta x) (menonTruncatedPrimeTopNat x : ℝ) W ≤
        (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten,
    eventually_menonFinalRangeTopNat_lt_truncatedPrimeTopNat_sq,
    Real.tendsto_log_atTop.eventually_ge_atTop (5720 : ℝ)] with x hx heta hsep hlogLarge
  intro W hW0 hWx
  rcases hx with ⟨hxone, hlogOne, _, hQ, _, heta0, _⟩
  rcases heta with ⟨_, hetaLe, hrTwo⟩
  rcases hsep with ⟨hUnat, hU2⟩
  let A : ℝ := (⌈x⌉₊ : ℝ)
  let B : ℝ := (menonFinalRangeTopNat x : ℝ)
  let U : ℝ := (menonTruncatedPrimeTopNat x : ℝ)
  let M : ℕ := ⌊B / U⌋₊
  let N : ℕ := ⌊B * (1 + menonFinalRangeLadderEta x)⌋₊
  have hx0 : 0 < x := lt_trans zero_lt_one hxone
  have hlog0 : 0 < Real.log x := Real.log_pos hxone
  have hlog9 : 0 < (Real.log x) ^ (9 : ℕ) := pow_pos hlog0 _
  have hlog10 : 0 < (Real.log x) ^ (10 : ℕ) := pow_pos hlog0 _
  have hlog20 : 0 < (Real.log x) ^ (20 : ℕ) := pow_pos hlog0 _
  have hAlo : x ≤ A := by dsimp [A]; exact Nat.le_ceil x
  have hAhi : A ≤ 2 * x := by
    dsimp [A]
    have hceil := Nat.ceil_lt_add_one hx0.le
    linarith
  have hB : B ≤ 3 * x := by
    dsimp [B]
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hU0 : 0 < U := by
    dsimp [U]
    exact_mod_cast hUnat
  have hUtop : U ≤ x / (Real.log x) ^ (20 : ℕ) := by
    dsimp [U]
    rw [menonTruncatedPrimeTopNat]
    exact Nat.floor_le (by rw [menonTruncatedPrimeTop]; positivity)
  have hBU : B / U < U := (div_lt_iff₀ hU0).2 (by simpa [B, U, pow_two] using hU2)
  have hMlt : (M : ℝ) < U := by
    have hfloor := Nat.floor_le (div_nonneg (by positivity : 0 ≤ B) hU0.le)
    exact hfloor.trans_lt hBU
  have hMx : (M : ℝ) ≤ x := by
    exact hMlt.le.trans (hUtop.trans
      (div_le_self hx0.le (one_le_pow₀ hlogOne)))
  have hlogM : Real.log (M : ℝ) ≤ Real.log x := by
    by_cases hM : M = 0
    · simp [hM, hlog0.le]
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hM) hMx
  have hlogFactor : 1 + Real.log (M : ℝ) ≤ 2 * Real.log x := by linarith
  have hAB : A + B ≤ 5 * x := by linarith
  have hfirst : (A + B) * menonFinalRangeLadderEta x *
      (1 + Real.log (M : ℝ)) ≤ 20 * x / (Real.log x) ^ (9 : ℕ) := by
    calc
      (A + B) * menonFinalRangeLadderEta x * (1 + Real.log (M : ℝ)) ≤
          (5 * x) * (2 / (Real.log x) ^ (10 : ℕ)) * (2 * Real.log x) := by
            gcongr
      _ = 20 * x / (Real.log x) ^ (9 : ℕ) := by
        field_simp
        ring
  have hMtop : (M : ℝ) ≤ x / (Real.log x) ^ (20 : ℕ) := hMlt.le.trans hUtop
  have hpow9le20 : (Real.log x) ^ (9 : ℕ) ≤ (Real.log x) ^ (20 : ℕ) :=
    pow_le_pow_right₀ hlogOne (by omega)
  have hsecond : 6 * (M : ℝ) ≤ 6 * x / (Real.log x) ^ (9 : ℕ) := by
    calc
      6 * (M : ℝ) ≤ 6 * (x / (Real.log x) ^ (20 : ℕ)) :=
        mul_le_mul_of_nonneg_left hMtop (by norm_num)
      _ ≤ 6 * (x / (Real.log x) ^ (9 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hx0.le hlog9 hpow9le20) (by norm_num)
      _ = 6 * x / (Real.log x) ^ (9 : ℕ) := by ring
  have hgap : (A + B) * menonFinalRangeLadderEta x *
        (1 + Real.log (M : ℝ)) + 6 * (M : ℝ) ≤
      26 * x / (Real.log x) ^ (9 : ℕ) := by
    calc
      _ ≤ 20 * x / (Real.log x) ^ (9 : ℕ) +
          6 * x / (Real.log x) ^ (9 : ℕ) := add_le_add hfirst hsecond
      _ = 26 * x / (Real.log x) ^ (9 : ℕ) := by ring
  have hN : (N : ℝ) ≤ 6 * x := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ B * (1 + menonFinalRangeLadderEta x))
    have hprod : B * (1 + menonFinalRangeLadderEta x) ≤ 6 * x := by
      nlinarith [mul_le_mul hB hrTwo (by positivity : 0 ≤ 1 + menonFinalRangeLadderEta x)
        (by positivity : 0 ≤ 3 * x)]
    exact hfloor.trans hprod
  have hpiW : Real.pi * W ≤ 4 * x :=
    mul_le_mul Real.pi_lt_four.le hWx hW0 (by norm_num)
  have hexpN : Real.exp 1 * (N : ℝ) ≤ 18 * x := by
    calc
      Real.exp 1 * (N : ℝ) ≤ 3 * (6 * x) :=
        mul_le_mul Real.exp_one_lt_three.le hN (Nat.cast_nonneg N) (by norm_num)
      _ = 18 * x := by ring
  have hmean : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) ≤ 55 * x := by
    nlinarith
  have hA0 : 0 < A := lt_of_lt_of_le hx0 hAlo
  have hOmega : (1 + menonFinalRangeLadderEta x) / A ≤ 2 / x := by
    rw [div_le_div_iff₀ hA0 hx0]
    have hleft := mul_le_mul_of_nonneg_right hrTwo hx0.le
    have hright := mul_le_mul_of_nonneg_left hAlo (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hOmegaSq : ((1 + menonFinalRangeLadderEta x) / A) ^ 2 ≤ (2 / x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hOmega 2
  rw [menonHarmonicHighLadderErrorBudget]
  change ((1 + menonFinalRangeLadderEta x) / A) ^ 2 *
      ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
        ((A + B) * menonFinalRangeLadderEta x * (1 + Real.log (M : ℝ)) +
          6 * (M : ℝ))) ≤ _
  calc
    _ ≤ (2 / x) ^ 2 * ((55 * x) * (26 * x / (Real.log x) ^ (9 : ℕ))) := by
      gcongr
    _ = 5720 / (Real.log x) ^ (9 : ℕ) := by field_simp; ring
    _ ≤ 1 / (Real.log x) ^ (8 : ℕ) := by
      rw [div_le_div_iff₀ hlog9 (pow_pos hlog0 8)]
      rw [pow_succ]
      nlinarith [pow_pos hlog0 8]
    _ = (Real.log x) ^ (-(8 : ℝ)) := by
      simp [Real.rpow_neg hlog0.le, one_div]

set_option maxHeartbeats 1000000 in
/-- Exact full final-range harmonic ladder defect is logarithmically negligible.  No final-range
primes are discarded: truncated prefix and injective high suffix recombine to the original ladder. -/
theorem eventually_integral_menonFinalRange_fullLadderDefect_le_four_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect (menonFinalRangePrimes x) ⌈x⌉₊
          (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
          (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) w‖ ^ 2) ≤
        4 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadder_basic,
    eventually_menonTruncatedRangeLadderSteps_le_finalRangeLadderSteps,
    eventually_menonTruncatedRangeLadder_cover,
    eventually_menonFinalRangeTopNat_lt_truncatedPrimeTopNat_sq,
    eventually_menonTruncatedRange_ladderErrorBudget_le_log_rpow_neg_eight,
    eventually_menonFinalRange_highLadderErrorBudget_le_log_rpow_neg_eight] with
      x htrunc hfull hJL hcover hsep hlo hhi
  intro W hW hWx
  rcases htrunc with ⟨hxone, _, _, hQ, _, heta, _⟩
  rcases hsep with ⟨hU, hU2⟩
  have hA : 0 < ⌈x⌉₊ := Nat.one_le_ceil_iff.2 (lt_trans zero_lt_one hxone)
  have hPprime : ∀ p ∈ menonFinalRangePrimes x, p.Prime :=
    fun p hp => menonFinalRangePrimes_prime x hp
  have hPge : ∀ p ∈ menonFinalRangePrimes x,
      menonFinalRangeLadderBase x ≤ (p : ℝ) := by
    intro p hp
    have hpRange := mem_primesRange.1 hp
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hpRange.2.1.le
  have hbase := integral_Icc_normSq_harmonicLadderProductDefect_le_prefix_add_high
    (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x)
    (Q := menonFinalRangeLadderBase x) (eta := menonFinalRangeLadderEta x)
    (U := (menonTruncatedPrimeTopNat x : ℝ)) (W := W)
    (J := menonTruncatedRangeLadderSteps x) (L := menonFinalRangeLadderSteps x)
    hA hQ heta hW hJL hPprime hPge hcover (by exact_mod_cast hU) hU2
  calc
    _ ≤ 2 * menonHarmonicLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
          (menonTruncatedRangeLadderSteps x) +
        2 * menonHarmonicHighLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderEta x) (menonTruncatedPrimeTopNat x : ℝ) W := hbase
    _ ≤ 2 * (Real.log x) ^ (-(8 : ℝ)) + 2 * (Real.log x) ^ (-(8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlo W (by linarith) hWx) (by norm_num))
        (mul_le_mul_of_nonneg_left (hhi W (by linarith) hWx) (by norm_num))
    _ = 4 * (Real.log x) ^ (-(8 : ℝ)) := by ring

end

end RHTower.Sieve
