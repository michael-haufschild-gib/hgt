import GaloisForLFunctions.BezoutValuationIncidence.TheMoebiusPrefixEnergyAtLargeBandRatio

/-!
# The Möbius energy transfers at every superlinear horizon

For the Möbius sieve `s_N(k) = Σ_{d ∣ k, d ≤ N} μ(d)` and `E_N(M) = Σ_{k ≤ M} s_N(k)²`, the prefix
mean square reaches the cofinal slope `κ` (the limiting period variance) uniformly beyond every
large linear horizon (`exists_abs_sieveL2PrefixEnergy_div_sub_le`):

`∀ ε > 0, ∃ B₀ N₀, ∀ N ≥ N₀, ∀ M ≥ B₀ N, |E_N(M)/M − κ| ≤ ε`,

so `E_N(M)/M → κ` along every horizon with `M/N → ∞` (`tendsto_sieveL2PrefixEnergy_div`). Generic
level-`N` rows need windows of length `N^{2±o(1)}` for mean-square transfer; the Möbius row
transfers at every superlinear horizon, and the cofinal laws hold uniformly in the band ratio.

Mechanism. Put `B = ⌊M/N⌋` and `J = ⌊N^{1/16}⌋` (`fibreCutoff`).
* `B ≤ J`: the quotient-pair form of `E_N((B+1)N)` counts squarefree integers prime to `ab ≤ B²`
  with error `ab √X (2 + ζ(3/2) + log X)` (`abs_moebiusDilationPairPrefix_sub_le`), so
  `|E_N((B+1)N) − 1 − N P(B)| ≤ bandError B N ≪ B⁵ √N log N`; monotonicity in `M` puts `E_N(M)/M`
  between `P(B−1)/(B+1)` and `P(B)/B` up to `≪ J^{-3}`, and `P(B)/B → κ`.
* `B > J`: then `N ≤ B¹⁶`, and `TheMoebiusPrefixEnergyAtLargeBandRatio` gives
  `|E_N(M)/M − C(N)| ≪ 1/(1 + log B) + (1 + log B)²/√B`, while `C(N) → κ`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Coprime squarefree counts, quantitatively -/

/-- `{X/L} ≤ √X/d` whenever `d² ≤ L`. -/
theorem fract_div_le_sqrt_div {X L d : ℕ} (hd : 1 ≤ d) (hdL : d * d ≤ L) :
    Int.fract ((X : ℝ) / (L : ℝ)) ≤ Real.sqrt X / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL0 : 0 < L := by nlinarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hf0 := Int.fract_nonneg ((X : ℝ) / L)
  have hf1 := (Int.fract_lt_one ((X : ℝ) / L)).le
  have hfl : (0 : ℝ) ≤ ⌊(X : ℝ) / L⌋ := by exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  have hfx : Int.fract ((X : ℝ) / L) ≤ (X : ℝ) / (d * d) := by
    rw [← Int.self_sub_floor]
    have : (X : ℝ) / L ≤ (X : ℝ) / (d * d) := by
      apply div_le_div_of_nonneg_left hX0 (mul_pos hdR hdR)
      exact_mod_cast hdL
    linarith
  have hsq : Int.fract ((X : ℝ) / L) ^ 2 ≤ (X : ℝ) / (d * d) := by
    rw [sq]
    calc Int.fract ((X : ℝ) / L) * Int.fract ((X : ℝ) / L) ≤ 1 * ((X : ℝ) / (d * d)) :=
          mul_le_mul hf1 hfx hf0 zero_le_one
      _ = (X : ℝ) / (d * d) := one_mul _
  have h := Real.abs_le_sqrt hsq
  rw [abs_of_nonneg hf0, Real.sqrt_div hX0, Real.sqrt_mul_self hdR.le] at h
  exact h

/-- **Coprime squarefree counts.** For squarefree `m` and `X ≥ 1`:
`|#{n ≤ X : n squarefree, (n,m)=1} − D(m) X| ≤ τ(m) √X (2 + ζ(3/2) + log X)`. -/
theorem abs_coprimeSquarefreeCount_sub_le {m X : ℕ} (hm : Squarefree m) (hX : 1 ≤ X) :
    |coprimeSquarefreeCount m X - coprimeSquarefreeDensity m * X| ≤
      (m.divisors.card : ℝ) * Real.sqrt X *
        (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hXR
  have hsq : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hτ0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumv := summable_coprimeSquarefreeSeriesTerm m
  have hV := tsum_coprimeSquarefreeSeriesTerm hm
  have hv0 : coprimeSquarefreeSeriesTerm m 0 = 0 := by simp [coprimeSquarefreeSeriesTerm]
  have hrange : ∑ i ∈ range (X + 1), coprimeSquarefreeSeriesTerm m i =
      ∑ d ∈ Icc 1 X, coprimeSquarefreeSeriesTerm m d := by
    have h : range (X + 1) = insert 0 (Icc 1 X) := by
      ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [h, sum_insert (by simp), hv0, zero_add]
  have hsplitV := hsumv.sum_add_tsum_nat_add (X + 1)
  rw [hrange, hV] at hsplitV
  have h1 : ∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors,
      (moebius d : ℝ) * moebius e * ((X / Nat.lcm (d * d) e : ℕ) : ℝ) =
      X * ∑ d ∈ Icc 1 X, coprimeSquarefreeSeriesTerm m d -
        ∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e *
          Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    unfold coprimeSquarefreeSeriesTerm
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ => ?_
    rw [natCast_div_eq_sub_fract]
    ring
  have hdecomp : coprimeSquarefreeCount m X - coprimeSquarefreeDensity m * X =
      -(∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e *
          Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))) -
        X * ∑' i, coprimeSquarefreeSeriesTerm m (i + (X + 1)) := by
    rw [coprimeSquarefreeCount_eq_sum hm0, h1, ← hsplitV]
    ring
  have hA : |∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e *
      Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))| ≤
      (m.divisors.card : ℝ) * Real.sqrt X * (1 + Real.log X) := by
    have hpt : ∀ d ∈ Icc 1 X, ∀ e ∈ m.divisors, |(moebius d : ℝ) * moebius e *
        Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))| ≤ Real.sqrt X * ((d : ℝ))⁻¹ := by
      intro d hd e he
      have hd1 := (mem_Icc.mp hd).1
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      have hL0 : 0 < Nat.lcm (d * d) e := Nat.lcm_pos (Nat.mul_pos hd1 hd1) he0
      have hdL : d * d ≤ Nat.lcm (d * d) e := Nat.le_of_dvd hL0 (Nat.dvd_lcm_left _ _)
      have hμ : |(moebius d : ℝ) * moebius e| ≤ 1 := by
        rw [abs_mul]
        have h1 : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |(moebius e : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius d : ℝ), abs_nonneg (moebius e : ℝ)]
      rw [abs_mul, abs_of_nonneg (Int.fract_nonneg ((X : ℝ) / (Nat.lcm (d * d) e : ℕ)))]
      calc |(moebius d : ℝ) * moebius e| * Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))
          ≤ 1 * (Real.sqrt X / d) :=
            mul_le_mul hμ (fract_div_le_sqrt_div hd1 hdL) (Int.fract_nonneg _) zero_le_one
        _ = Real.sqrt X * ((d : ℝ))⁻¹ := by ring
    calc _ ≤ ∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors, |(moebius d : ℝ) * moebius e *
          Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))| :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ d ∈ Icc 1 X, ∑ _e ∈ m.divisors, Real.sqrt X * ((d : ℝ))⁻¹ :=
          sum_le_sum fun d hd => sum_le_sum fun e he => hpt d hd e he
      _ = (m.divisors.card : ℝ) * Real.sqrt X * ∑ d ∈ Icc 1 X, ((d : ℝ))⁻¹ := by
          simp only [sum_const, nsmul_eq_mul]
          rw [mul_sum]
          exact sum_congr rfl fun d _ => by ring
      _ ≤ (m.divisors.card : ℝ) * Real.sqrt X * (1 + Real.log X) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le X) (by positivity)
  have hT := abs_tsum_coprimeSquarefreeSeriesTerm_tail_le m hX
  have hXT : |(X : ℝ) * ∑' i, coprimeSquarefreeSeriesTerm m (i + (X + 1))| ≤
      (m.divisors.card : ℝ) * Real.sqrt X * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hX0.le]
    calc (X : ℝ) * |∑' i, coprimeSquarefreeSeriesTerm m (i + (X + 1))|
        ≤ X * ((m.divisors.card : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / Real.sqrt X) :=
          mul_le_mul_of_nonneg_left hT hX0.le
      _ = (m.divisors.card : ℝ) * (X / Real.sqrt X) * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          ring
      _ = (m.divisors.card : ℝ) * Real.sqrt X * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.div_sqrt]
  rw [hdecomp]
  calc _ ≤ |∑ d ∈ Icc 1 X, ∑ e ∈ m.divisors, (moebius d : ℝ) * moebius e *
          Int.fract ((X : ℝ) / (Nat.lcm (d * d) e : ℕ))| +
        |(X : ℝ) * ∑' i, coprimeSquarefreeSeriesTerm m (i + (X + 1))| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ ≤ (m.divisors.card : ℝ) * Real.sqrt X * (1 + Real.log X) +
          (m.divisors.card : ℝ) * Real.sqrt X * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
        add_le_add hA hXT
    _ ≤ _ := by
        have h0 : 0 ≤ (m.divisors.card : ℝ) * Real.sqrt X := by positivity
        nlinarith

/-- **Dilation pairs.** For coprime `a, b`:
`|Σ_{n ≤ X} μ(an)μ(bn) − X D(a,b)| ≤ ab √X (2 + ζ(3/2) + log X)`. -/
theorem abs_moebiusDilationPairPrefix_sub_le {a b : ℕ} (hab : Nat.Coprime a b) (X : ℕ) :
    |moebiusDilationPairPrefix a b X - X * moebiusDilationPairDensity a b| ≤
      ((a * b : ℕ) : ℝ) * Real.sqrt X * (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) := by
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlX : 0 ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hX)
  have hR0 : 0 ≤ ((a * b : ℕ) : ℝ) * Real.sqrt X *
      (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) :=
    mul_nonneg (by positivity) (by linarith)
  have hpref : moebiusDilationPairPrefix a b X =
      moebiusReal a * moebiusReal b * coprimeSquarefreeCount (a * b) X := by
    unfold moebiusDilationPairPrefix coprimeSquarefreeCount
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    unfold moebiusReal
    exact moebius_dilation_pair_eq_coprimeSquarefreeIndicator a b n
  rw [hpref, moebiusDilationPairDensity,
    show moebiusReal a * moebiusReal b * coprimeSquarefreeCount (a * b) X -
      X * (moebiusReal a * moebiusReal b * coprimeSquarefreeDensity (a * b)) =
      moebiusReal a * moebiusReal b * (coprimeSquarefreeCount (a * b) X -
        coprimeSquarefreeDensity (a * b) * X) by ring, abs_mul]
  by_cases hsf : Squarefree (a * b)
  · have hμ : |moebiusReal a * moebiusReal b| ≤ 1 := by
      unfold moebiusReal
      rw [abs_mul]
      have h1 : |((moebius a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have h2 : |((moebius b : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      nlinarith [abs_nonneg ((moebius a : ℤ) : ℝ), abs_nonneg ((moebius b : ℤ) : ℝ)]
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp [coprimeSquarefreeCount]
    have hcount := abs_coprimeSquarefreeCount_sub_le hsf hX
    have hτ : ((a * b).divisors.card : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (a * b)
    have hS0 : 0 ≤ Real.sqrt X * (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    calc |moebiusReal a * moebiusReal b| * |coprimeSquarefreeCount (a * b) X -
          coprimeSquarefreeDensity (a * b) * X|
        ≤ 1 * (((a * b).divisors.card : ℝ) * Real.sqrt X *
            (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X)) :=
          mul_le_mul hμ hcount (abs_nonneg _) zero_le_one
      _ ≤ ((a * b : ℕ) : ℝ) * Real.sqrt X *
            (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) := by
          rw [one_mul, mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hτ hS0
  · have h0 : moebiusReal a * moebiusReal b = 0 := by
      unfold moebiusReal
      rcases not_and_or.mp (fun h => hsf (Nat.squarefree_mul_iff.mpr ⟨hab, h⟩)) with h | h
      · rw [moebius_eq_zero_of_not_squarefree h]; simp
      · rw [moebius_eq_zero_of_not_squarefree h]; simp
    rw [h0, abs_zero, zero_mul]
    exact hR0

/-! ### The band identity, quantitatively -/

/-- The error of the band identity: `B² (2 B² √((B+1)N) (2 + ζ(3/2) + log((B+1)N)) + 2)`. -/
def bandError (B N : ℕ) : ℝ :=
  (B : ℝ) ^ 2 * (2 * (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
    (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log (((B + 1) * N : ℕ) : ℝ)) + 2)

theorem log_natCast_nonneg (x : ℕ) : 0 ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hx)

theorem log_natCast_le_log {x y : ℕ} (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using log_natCast_nonneg y
  · exact Real.log_le_log (by exact_mod_cast hx) (by exact_mod_cast hxy)

theorem bandError_nonneg (B N : ℕ) : 0 ≤ bandError B N := by
  unfold bandError
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := log_natCast_nonneg ((B + 1) * N)
  exact mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (Real.sqrt_nonneg _)) (by linarith)) (by norm_num))

theorem bandError_mono (B N : ℕ) : bandError B N ≤ bandError (B + 1) N := by
  unfold bandError
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle : (B + 1) * N ≤ (B + 1 + 1) * N := Nat.mul_le_mul_right N (Nat.le_succ _)
  have hs : Real.sqrt (((B + 1) * N : ℕ) : ℝ) ≤ Real.sqrt (((B + 1 + 1) * N : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hle)
  have hl : Real.log (((B + 1) * N : ℕ) : ℝ) ≤ Real.log (((B + 1 + 1) * N : ℕ) : ℝ) :=
    log_natCast_le_log hle
  have hl0 := log_natCast_nonneg ((B + 1) * N)
  have hB : (B : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ B
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hB2 : (B : ℝ) ^ 2 ≤ ((B + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ hB0 hB 2
  have hs0 := Real.sqrt_nonneg (((B + 1) * N : ℕ) : ℝ)
  have hin : 2 * (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
      (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log (((B + 1) * N : ℕ) : ℝ)) + 2 ≤
      2 * ((B + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (((B + 1 + 1) * N : ℕ) : ℝ) *
      (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log (((B + 1 + 1) * N : ℕ) : ℝ)) + 2 := by
    have hc0 : 0 ≤ 2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log (((B + 1) * N : ℕ) : ℝ) := by
      linarith
    have hstep := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hB2 (by norm_num : (0 : ℝ) ≤ 2))
      hs hs0 (by positivity)) (by linarith : 2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) +
        Real.log (((B + 1) * N : ℕ) : ℝ) ≤ 2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) +
        Real.log (((B + 1 + 1) * N : ℕ) : ℝ)) hc0 (by positivity)
    linarith
  have hin0 : 0 ≤ 2 * (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
      (2 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log (((B + 1) * N : ℕ) : ℝ)) + 2 :=
    add_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)
  exact mul_le_mul hB2 hin hin0 (by positivity)

/-- **Band identity with error.** `|E_N((B+1)N) − 1 − N P(B)| ≤ bandError B N`. -/
theorem abs_sieveL2PrefixEnergy_band_sub_le {N : ℕ} (hN : 1 ≤ N) (B : ℕ) :
    |sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal - 1 - N * cofinalMobiusQuadraticProfile B| ≤
      bandError B N := by
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hM : 1 ≤ (B + 1) * N := by nlinarith
  have hMR : (1 : ℝ) ≤ (((B + 1) * N : ℕ) : ℝ) := by exact_mod_cast hM
  have hlM := log_natCast_nonneg ((B + 1) * N)
  rw [sieveL2PrefixEnergy_moebiusReal_eq_quotient_pairs hN hM
    (Nat.mul_le_mul_right N (Nat.le_succ B)) le_rfl]
  unfold cofinalMobiusQuadraticProfile
  rw [show ∀ x y : ℝ, 1 + x - 1 - y = x - y by intros; ring, mul_sum, ← sum_sub_distrib]
  have hpt : ∀ q ∈ Icc 1 B, ∀ r ∈ Icc 1 B,
      |(moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r) ((B + 1) * N / Nat.lcm q r) -
        moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
          (max q r * N / Nat.lcm q r)) -
        N * ((((B : ℝ) + 1 - (max q r : ℕ)) / Nat.lcm q r) *
          moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r))| ≤
      2 * (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
        (2 + Z + Real.log (((B + 1) * N : ℕ) : ℝ)) + 2 := by
    intro q hq r hr
    obtain ⟨hq1, hqB⟩ := mem_Icc.mp hq
    obtain ⟨hr1, hrB⟩ := mem_Icc.mp hr
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq1
    have hcop : Nat.Coprime (r / Nat.gcd q r) (q / Nat.gcd q r) :=
      (Nat.coprime_div_gcd_div_gcd hg).symm
    have hl : 0 < Nat.lcm q r := Nat.lcm_pos hq1 hr1
    have hlR : (0 : ℝ) < Nat.lcm q r := by exact_mod_cast hl
    set a := r / Nat.gcd q r with ha
    set b := q / Nat.gcd q r with hb
    set D := moebiusDilationPairDensity a b with hD
    -- `|D| ≤ 1`
    have hD1 : |D| ≤ 1 := by
      rw [hD, moebiusDilationPairDensity]
      by_cases hsf : Squarefree (a * b)
      · obtain ⟨hd0, hd1⟩ := coprimeSquarefreeDensity_mem hsf
        unfold moebiusReal
        rw [abs_mul, abs_mul, abs_of_nonneg hd0]
        have h1 : |((moebius a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |((moebius b : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h12 : |((moebius a : ℤ) : ℝ)| * |((moebius b : ℤ) : ℝ)| ≤ 1 := by
          nlinarith [abs_nonneg ((moebius a : ℤ) : ℝ), abs_nonneg ((moebius b : ℤ) : ℝ)]
        nlinarith [abs_nonneg ((moebius a : ℤ) : ℝ), abs_nonneg ((moebius b : ℤ) : ℝ)]
      · have h0 : moebiusReal a * moebiusReal b = 0 := by
          unfold moebiusReal
          rcases not_and_or.mp (fun h => hsf (Nat.squarefree_mul_iff.mpr ⟨hcop, h⟩)) with h | h
          · rw [moebius_eq_zero_of_not_squarefree h]; simp
          · rw [moebius_eq_zero_of_not_squarefree h]; simp
        rw [h0, zero_mul, abs_zero]; exact zero_le_one
    -- `ab ≤ B²`
    have hab : ((a * b : ℕ) : ℝ) ≤ (B : ℝ) ^ 2 := by
      have h1 : a ≤ B := (Nat.div_le_self r _).trans hrB
      have h2 : b ≤ B := (Nat.div_le_self q _).trans hqB
      have : a * b ≤ B * B := Nat.mul_le_mul h1 h2
      rw [sq]; exact_mod_cast this
    -- the two prefixes
    have hX1 : (B + 1) * N / Nat.lcm q r ≤ (B + 1) * N := Nat.div_le_self _ _
    have hX2 : max q r * N / Nat.lcm q r ≤ (B + 1) * N :=
      (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right N ((max_le hqB hrB).trans (Nat.le_succ B)))
    have hbound : ∀ x : ℕ, x ≤ (B + 1) * N →
        |moebiusDilationPairPrefix a b x - x * D| ≤
          (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
            (2 + Z + Real.log (((B + 1) * N : ℕ) : ℝ)) := by
      intro x hx
      refine (abs_moebiusDilationPairPrefix_sub_le hcop x).trans ?_
      have hsx : Real.sqrt x ≤ Real.sqrt (((B + 1) * N : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hx)
      have hlx : Real.log x ≤ Real.log (((B + 1) * N : ℕ) : ℝ) := log_natCast_le_log hx
      have hlx0 := log_natCast_nonneg x
      apply mul_le_mul (mul_le_mul hab hsx (Real.sqrt_nonneg _) (by positivity)) (by linarith)
        (by linarith) (by positivity)
    have hfr : ∀ x y : ℕ, |((x / y : ℕ) : ℝ) - (x : ℝ) / y| ≤ 1 := by
      intro x y
      rw [natCast_div_eq_sub_fract, sub_sub_cancel_left, abs_neg,
        abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    have hsplit : (moebiusDilationPairPrefix a b ((B + 1) * N / Nat.lcm q r) -
        moebiusDilationPairPrefix a b (max q r * N / Nat.lcm q r)) -
        N * ((((B : ℝ) + 1 - (max q r : ℕ)) / Nat.lcm q r) * D) =
        (moebiusDilationPairPrefix a b ((B + 1) * N / Nat.lcm q r) -
          (((B + 1) * N / Nat.lcm q r : ℕ) : ℝ) * D) -
        (moebiusDilationPairPrefix a b (max q r * N / Nat.lcm q r) -
          ((max q r * N / Nat.lcm q r : ℕ) : ℝ) * D) +
        ((((B + 1) * N / Nat.lcm q r : ℕ) : ℝ) - (((B + 1) * N : ℕ) : ℝ) / Nat.lcm q r) * D -
        (((max q r * N / Nat.lcm q r : ℕ) : ℝ) - ((max q r * N : ℕ) : ℝ) / Nat.lcm q r) * D := by
      push_cast
      ring
    rw [hsplit]
    have e1 := hbound _ hX1
    have e2 := hbound _ hX2
    have e3 : |((((B + 1) * N / Nat.lcm q r : ℕ) : ℝ) - (((B + 1) * N : ℕ) : ℝ) / Nat.lcm q r) * D|
        ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ (hfr _ _) (abs_nonneg _) hD1
    have e4 : |(((max q r * N / Nat.lcm q r : ℕ) : ℝ) - ((max q r * N : ℕ) : ℝ) / Nat.lcm q r) * D|
        ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ (hfr _ _) (abs_nonneg _) hD1
    calc _ ≤ |moebiusDilationPairPrefix a b ((B + 1) * N / Nat.lcm q r) -
            (((B + 1) * N / Nat.lcm q r : ℕ) : ℝ) * D| +
          |moebiusDilationPairPrefix a b (max q r * N / Nat.lcm q r) -
            ((max q r * N / Nat.lcm q r : ℕ) : ℝ) * D| +
          |((((B + 1) * N / Nat.lcm q r : ℕ) : ℝ) - (((B + 1) * N : ℕ) : ℝ) / Nat.lcm q r) * D| +
          |(((max q r * N / Nat.lcm q r : ℕ) : ℝ) - ((max q r * N : ℕ) : ℝ) / Nat.lcm q r) * D| := by
          refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith
  calc _ ≤ ∑ q ∈ Icc 1 B, ∑ r ∈ Icc 1 B,
        (2 * (B : ℝ) ^ 2 * Real.sqrt (((B + 1) * N : ℕ) : ℝ) *
          (2 + Z + Real.log (((B + 1) * N : ℕ) : ℝ)) + 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
        rw [mul_sum, ← sum_sub_distrib]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r hr => hpt q hq r hr)
    _ = bandError B N := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        unfold bandError
        rw [← hZ]
        ring

/-! ### The small band ratio -/

/-- **Monotone sandwich.** For `B = ⌊M/N⌋ ≥ 1`:
`|E_N(M)/M − κ| ≤ |P(B)/B − κ| + |P(B−1)/(B+1) − κ| + (1 + bandError B N)/(BN)`. -/
theorem abs_sieveL2PrefixEnergy_div_sub_le_of_band {N M : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ M / N) :
    |sieveL2PrefixEnergy N M moebiusReal / M - cofinalMobiusSlope| ≤
      |cofinalMobiusQuadraticProfile (M / N) / (M / N : ℕ) - cofinalMobiusSlope| +
        |cofinalMobiusQuadraticProfile (M / N - 1) / (((M / N : ℕ) : ℝ) + 1) - cofinalMobiusSlope| +
        (1 + bandError (M / N) N) / (((M / N : ℕ) : ℝ) * N) := by
  set B := M / N with hBdef
  have hlo : B * N ≤ M := Nat.div_mul_le_self M N
  have hhi : M < (B + 1) * N := by
    have := Nat.lt_div_mul_add (a := M) (show 0 < N by omega)
    rw [hBdef]; linarith
  have hmono : ∀ M₁ M₂ : ℕ, M₁ ≤ M₂ →
      sieveL2PrefixEnergy N M₁ moebiusReal ≤ sieveL2PrefixEnergy N M₂ moebiusReal := by
    intro M₁ M₂ h
    unfold sieveL2PrefixEnergy
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ => sq_nonneg _
  have hE0 : ∀ M₁ : ℕ, 0 ≤ sieveL2PrefixEnergy N M₁ moebiusReal := fun M₁ =>
    sum_nonneg fun _ _ => sq_nonneg _
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBN : (0 : ℝ) < (B : ℝ) * N := mul_pos (by linarith) (by linarith)
  have hMR1 : (B : ℝ) * N ≤ M := by exact_mod_cast hlo
  have hMR2 : (M : ℝ) ≤ ((B : ℝ) + 1) * N := by
    have : M ≤ (B + 1) * N := hhi.le
    exact_mod_cast this
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hBN hMR1
  have hup := abs_sieveL2PrefixEnergy_band_sub_le hN B
  have hdn := abs_sieveL2PrefixEnergy_band_sub_le hN (B - 1)
  rw [show B - 1 + 1 = B by omega] at hdn
  have hΔ : bandError (B - 1) N ≤ bandError B N := by
    have := bandError_mono (B - 1) N
    rwa [show B - 1 + 1 = B by omega] at this
  have hΔ0 := bandError_nonneg B N
  set Δ := bandError B N
  set U := sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal
  set L := sieveL2PrefixEnergy N (B * N) moebiusReal
  set Em := sieveL2PrefixEnergy N M moebiusReal
  have hU : Em ≤ U := hmono _ _ hhi.le
  have hL : L ≤ Em := hmono _ _ hlo
  have hU0 : 0 ≤ U := hE0 _
  have hL0 : 0 ≤ L := hE0 _
  have hUb : U ≤ 1 + N * cofinalMobiusQuadraticProfile B + Δ := by
    have := (abs_le.mp hup).2; linarith
  have hLb : (N : ℝ) * cofinalMobiusQuadraticProfile (B - 1) - Δ ≤ L := by
    have := (abs_le.mp hdn).1; linarith
  -- upper side
  have hupper : Em / M ≤ cofinalMobiusQuadraticProfile B / B + (1 + Δ) / ((B : ℝ) * N) := by
    calc Em / M ≤ U / M := div_le_div_of_nonneg_right hU hM0.le
      _ ≤ U / ((B : ℝ) * N) := div_le_div_of_nonneg_left hU0 hBN hMR1
      _ ≤ (1 + N * cofinalMobiusQuadraticProfile B + Δ) / ((B : ℝ) * N) :=
          div_le_div_of_nonneg_right hUb hBN.le
      _ = cofinalMobiusQuadraticProfile B / B + (1 + Δ) / ((B : ℝ) * N) := by
          have hB0 : (B : ℝ) ≠ 0 := by linarith
          rw [div_add_div _ _ hB0 hBN.ne', div_eq_div_iff hBN.ne' (mul_ne_zero hB0 hBN.ne')]
          ring
  -- lower side
  have hlower : cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1) - (1 + Δ) / ((B : ℝ) * N) ≤
      Em / M := by
    have hB1N : (0 : ℝ) < ((B : ℝ) + 1) * N := mul_pos (by linarith) (by linarith)
    calc cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1) - (1 + Δ) / ((B : ℝ) * N)
        ≤ cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1) - Δ / (((B : ℝ) + 1) * N) := by
          apply sub_le_sub_left
          calc Δ / (((B : ℝ) + 1) * N) ≤ Δ / ((B : ℝ) * N) :=
                div_le_div_of_nonneg_left hΔ0 hBN (by nlinarith)
            _ ≤ (1 + Δ) / ((B : ℝ) * N) := div_le_div_of_nonneg_right (by linarith) hBN.le
      _ = ((N : ℝ) * cofinalMobiusQuadraticProfile (B - 1) - Δ) / (((B : ℝ) + 1) * N) := by
          have hB1 : (B : ℝ) + 1 ≠ 0 := by linarith
          rw [div_sub_div _ _ hB1 hB1N.ne', div_eq_div_iff (mul_ne_zero hB1 hB1N.ne') hB1N.ne']
          ring
      _ ≤ L / (((B : ℝ) + 1) * N) := div_le_div_of_nonneg_right hLb hB1N.le
      _ ≤ L / M := div_le_div_of_nonneg_left hL0 hM0 hMR2
      _ ≤ Em / M := div_le_div_of_nonneg_right hL hM0.le
  have hr0 : 0 ≤ (1 + Δ) / ((B : ℝ) * N) := div_nonneg (by linarith) hBN.le
  rw [abs_sub_le_iff]
  constructor
  · have := le_abs_self (cofinalMobiusQuadraticProfile B / B - cofinalMobiusSlope)
    have := abs_nonneg (cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1) - cofinalMobiusSlope)
    linarith
  · have := neg_abs_le (cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1) - cofinalMobiusSlope)
    have := abs_nonneg (cofinalMobiusQuadraticProfile B / B - cofinalMobiusSlope)
    linarith

/-- `log((B+1)N) ≤ 1 + 32 J` for `B ≤ J`, `J¹⁶ ≤ N < (J+1)¹⁶`. -/
theorem log_band_le {N B J : ℕ} (hBJ : B ≤ J) (hJN : J ^ 16 ≤ N) (hNJ : N < (J + 1) ^ 16)
    (hN1 : 1 ≤ N) : Real.log (((B + 1) * N : ℕ) : ℝ) ≤ 1 + 32 * J := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNJR : (N : ℝ) ≤ ((J : ℝ) + 1) ^ 16 := by exact_mod_cast hNJ.le
  clear hNJ
  have hBN : (B + 1) * N ≤ 2 * N * N := by
    have : B ≤ N := hBJ.trans ((Nat.le_self_pow (by norm_num) J).trans hJN)
    have : B + 1 ≤ 2 * N := by omega
    exact Nat.mul_le_mul_right N this
  have h1 : Real.log (((B + 1) * N : ℕ) : ℝ) ≤ Real.log (((2 * N * N : ℕ) : ℝ)) :=
    log_natCast_le_log hBN
  have h2 : Real.log (((2 * N * N : ℕ) : ℝ)) = Real.log 2 + 2 * Real.log N := by
    push_cast
    rw [Real.log_mul (mul_pos two_pos hN0).ne' hN0.ne', Real.log_mul (by norm_num) hN0.ne']
    ring
  have h3 : Real.log N ≤ 16 * J := by
    calc Real.log N ≤ Real.log (((J : ℝ) + 1) ^ 16) := Real.log_le_log hN0 hNJR
      _ = 16 * Real.log ((J : ℝ) + 1) := by rw [Real.log_pow]; norm_num
      _ ≤ 16 * J := by
          have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < J + 1 by linarith)
          linarith
  have h4 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  linarith

/-- `√((B+1)N) ≤ 2B √N` for `B ≥ 1`. -/
theorem sqrt_band_le {N B : ℕ} (hB : 1 ≤ B) :
    Real.sqrt (((B + 1) * N : ℕ) : ℝ) ≤ 2 * B * Real.sqrt N := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have e : (((B + 1) * N : ℕ) : ℝ) = ((B : ℝ) + 1) * N := by push_cast; ring
  rw [e, Real.sqrt_mul (by positivity)]
  have hB1 : (0 : ℝ) ≤ (B : ℝ) + 1 := by linarith
  have h1 : Real.sqrt ((B : ℝ) + 1) ≤ (B : ℝ) + 1 := by
    rw [Real.sqrt_le_left hB1, sq]; exact le_mul_of_one_le_right hB1 (by linarith)
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (N : ℝ))
  have h3 := mul_le_mul_of_nonneg_right (show (B : ℝ) + 1 ≤ 2 * B by linarith)
    (Real.sqrt_nonneg (N : ℝ))
  linarith

/-- `bandError B N ≤ 4 (35 + ζ(3/2)) B⁵ J √N + 2B²` for `1 ≤ B ≤ J`, `J¹⁶ ≤ N < (J+1)¹⁶`. -/
theorem bandError_le {N B J : ℕ} (hB : 1 ≤ B) (hBJ : B ≤ J) (hJN : J ^ 16 ≤ N)
    (hNJ : N < (J + 1) ^ 16) (hN1 : 1 ≤ N) :
    bandError B N ≤ 4 * (35 + ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) * (B : ℝ) ^ 5 * J *
      Real.sqrt N + 2 * (B : ℝ) ^ 2 := by
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlog := log_band_le hBJ hJN hNJ hN1
  clear hNJ
  have hsq := sqrt_band_le (N := N) hB
  have hlog0 := log_natCast_nonneg ((B + 1) * N)
  have hq0 := Real.sqrt_nonneg (((B + 1) * N : ℕ) : ℝ)
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hB.trans hBJ
  unfold bandError
  generalize ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) = Z at hZ0 ⊢
  generalize Real.log (((B + 1) * N : ℕ) : ℝ) = l at hlog hlog0 ⊢
  generalize Real.sqrt (((B + 1) * N : ℕ) : ℝ) = q at hsq hq0 ⊢
  have hfac : 2 + Z + l ≤ (35 + Z) * J := by
    have := le_mul_of_one_le_right hZ0 hJR
    linarith
  have hfac0 : 0 ≤ 2 + Z + l := by linarith
  have h1 : 2 * (B : ℝ) ^ 2 * q * (2 + Z + l) ≤
      2 * (B : ℝ) ^ 2 * (2 * B * Real.sqrt N) * ((35 + Z) * J) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hfac hfac0 (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (B : ℝ))
  linarith

/-- The final arithmetic: `(1 + bandError B N)/(BN) ≤ (143 + 4ζ(3/2))/J³`. -/
theorem bandError_div_le_of {N B J : ℕ} (hB : 1 ≤ B) (hBJ : B ≤ J) (hJN : J ^ 16 ≤ N)
    (hNJ : N < (J + 1) ^ 16) :
    (1 + bandError B N) / ((B : ℝ) * N) ≤
      (143 + 4 * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / (J : ℝ) ^ 3 := by
  have hJ1 : 1 ≤ J := hB.trans hBJ
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by omega)) hJN
  have hΔ := bandError_le hB hBJ hJN hNJ hN1
  clear hNJ
  have hZ0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  generalize ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) = Z at hZ0 hΔ ⊢
  generalize bandError B N = Δ at hΔ ⊢
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJ0 : (0 : ℝ) < J := by linarith
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBJR : (B : ℝ) ≤ J := by exact_mod_cast hBJ
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hJ8 : (J : ℝ) ^ 8 ≤ Real.sqrt N := by
    have h16 : ((J : ℝ) ^ 8) ^ 2 ≤ N := by
      rw [← pow_mul]; exact_mod_cast hJN
    exact (le_abs_self _).trans (Real.abs_le_sqrt h16)
  have hJ16 : (J : ℝ) ^ 16 ≤ N := by exact_mod_cast hJN
  have hB4 : (B : ℝ) ^ 4 ≤ (J : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hBJR 4
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hkey1 : 4 * (35 + Z) * (B : ℝ) ^ 5 * J * Real.sqrt N * (J : ℝ) ^ 3 ≤
      4 * (35 + Z) * (B : ℝ) * N := by
    have h : (B : ℝ) ^ 4 * (J : ℝ) ^ 4 * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := by
      calc (B : ℝ) ^ 4 * (J : ℝ) ^ 4 * Real.sqrt N ≤ (J : ℝ) ^ 4 * (J : ℝ) ^ 4 * Real.sqrt N :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB4 (by positivity))
              hsqN.le
        _ = (J : ℝ) ^ 8 * Real.sqrt N := by ring
        _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right hJ8 hsqN.le
    have h4 : 0 ≤ 4 * (35 + Z) * (B : ℝ) := mul_nonneg (by linarith) (by linarith)
    calc 4 * (35 + Z) * (B : ℝ) ^ 5 * J * Real.sqrt N * (J : ℝ) ^ 3
        = 4 * (35 + Z) * (B : ℝ) * ((B : ℝ) ^ 4 * (J : ℝ) ^ 4 * Real.sqrt N) := by ring
      _ ≤ 4 * (35 + Z) * (B : ℝ) * (Real.sqrt N * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h h4
      _ = 4 * (35 + Z) * (B : ℝ) * N := by rw [hsqsq]
  have hJ3nn : 0 ≤ (J : ℝ) ^ 3 := by positivity
  have hkey2 : (1 + 2 * (B : ℝ) ^ 2) * (J : ℝ) ^ 3 ≤ 3 * (B : ℝ) * N := by
    have hJ3 : (J : ℝ) ^ 3 * (J : ℝ) ^ 3 ≤ (J : ℝ) ^ 16 := by
      rw [← pow_add]; exact pow_le_pow_right₀ hJR (by norm_num)
    have hB2J : (B : ℝ) ^ 2 ≤ (J : ℝ) ^ 3 := by
      calc (B : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hBJR 2
        _ ≤ (J : ℝ) ^ 3 := pow_le_pow_right₀ hJR (by norm_num)
    have s1 : 1 + 2 * (B : ℝ) ^ 2 ≤ 3 * (B : ℝ) ^ 2 := by
      have := one_le_pow₀ (n := 2) hBR; linarith
    have s2 : 3 * (B : ℝ) ^ 2 * (J : ℝ) ^ 3 ≤ 3 * ((J : ℝ) ^ 3 * (J : ℝ) ^ 3) := by
      have := mul_le_mul_of_nonneg_right hB2J hJ3nn; linarith
    have s3 : (N : ℝ) ≤ (B : ℝ) * N := le_mul_of_one_le_left hN0.le hBR
    have := mul_le_mul_of_nonneg_right s1 hJ3nn
    linarith
  rw [div_le_div_iff₀ (mul_pos (by linarith) hN0) (pow_pos hJ0 3)]
  have := mul_le_mul_of_nonneg_right hΔ hJ3nn
  linarith

/-- Below the fibre cutoff the band error is `O(J⁻³)`: for `1 ≤ B ≤ J = ⌊N^{1/16}⌋`,
`(1 + bandError B N)/(BN) ≤ (143 + 4 ζ(3/2))/J³`. -/
theorem bandError_div_le {N B : ℕ} (hB : 1 ≤ B) (hBJ : B ≤ fibreCutoff N) :
    (1 + bandError B N) / ((B : ℝ) * N) ≤
      (143 + 4 * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) / (fibreCutoff N : ℝ) ^ 3 :=
  bandError_div_le_of hB hBJ (fibreCutoff_pow_le N) (lt_fibreCutoff_succ_pow N)

/-! ### The transfer -/

theorem tendsto_profile_div_succ :
    Tendsto (fun B : ℕ => cofinalMobiusQuadraticProfile (B - 1) / ((B : ℝ) + 1)) atTop
      (𝓝 cofinalMobiusSlope) := by
  have h := tendsto_cofinalMobiusQuadraticProfile_div
  have hr : Tendsto (fun B : ℕ => (B : ℝ) / ((B : ℝ) + 2)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun B : ℕ => 1 - 2 / ((B : ℝ) + 2)) atTop (𝓝 1) := by
      have : Tendsto (fun B : ℕ => 2 / ((B : ℝ) + 2)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun B : ℕ => (B : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h2).const_mul 2
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    refine h1.congr' (Eventually.of_forall fun B => ?_)
    have : (B : ℝ) + 2 ≠ 0 := by positivity
    rw [eq_div_iff this, sub_mul, div_mul_cancel₀ _ this]
    ring
  have hprod := (h.mul hr).comp (tendsto_sub_atTop_nat 1)
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  simp only [Function.comp]
  have hcast : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
    rw [Nat.cast_sub hB, Nat.cast_one]
  rw [hcast]
  rcases Nat.lt_or_ge B 2 with hB2 | hB2
  · have hB1 : B = 1 := by omega
    subst hB1
    simp [cofinalMobiusQuadraticProfile_zero]
  · have hB1R : (B : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ B := by exact_mod_cast hB2
      linarith
    rw [show (B : ℝ) - 1 + 2 = B + 1 by ring, div_mul_div_comm,
      mul_comm (cofinalMobiusQuadraticProfile (B - 1)) ((B : ℝ) - 1), mul_div_mul_left _ _ hB1R]

/-- **Superlinear transfer.** For every `ε > 0` there are `B₀, N₀` with
`|E_N(M)/M − κ| ≤ ε` for all `N ≥ N₀` and all `M ≥ B₀ N`. -/
theorem exists_abs_sieveL2PrefixEnergy_div_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ B₀ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, B₀ * N ≤ M →
      |sieveL2PrefixEnergy N M moebiusReal / M - cofinalMobiusSlope| ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_coprime_moebius_fract_le
  set E := Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) with hE
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hZ
  have hε3 : 0 < ε / 3 := by positivity
  -- profile ratios
  obtain ⟨B₁, hB₁⟩ := Metric.tendsto_atTop.mp tendsto_cofinalMobiusQuadraticProfile_div (ε / 3) hε3
  obtain ⟨B₂, hB₂⟩ := Metric.tendsto_atTop.mp tendsto_profile_div_succ (ε / 3) hε3
  -- the large-ratio bound in `B`
  have hg : Tendsto (fun B : ℕ => 256 * K * E ^ 2 / (1 + Real.log B) +
      256 * (1 + Real.log B) ^ 2 / Real.sqrt B) atTop (𝓝 0) := by
    have hl : Tendsto (fun B : ℕ => 1 + Real.log B) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun B : ℕ => 256 * K * E ^ 2 / (1 + Real.log B)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hl).const_mul (256 * K * E ^ 2)
    have h2 : Tendsto (fun B : ℕ => 256 * (1 + Real.log B) ^ 2 / Real.sqrt B) atTop (𝓝 0) := by
      have hq : Tendsto (fun B : ℕ => 16384 * ((B : ℝ) ^ (1 / 4 : ℝ))⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num :
          (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)).const_mul 16384
        simpa using this
      refine squeeze_zero' (Eventually.of_forall fun B => by positivity) ?_ hq
      filter_upwards [eventually_ge_atTop 1] with B hB
      have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
      have hB0 : (0 : ℝ) < B := by linarith
      have hq0 : 0 < (B : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hB0 _
      have hsq0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
      have hlog := one_add_log_sq_le_rpow_quarter hBR
      have hsq : (B : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt B := by
        rw [← Real.rpow_add hB0, Real.sqrt_eq_rpow]; norm_num
      rw [div_le_iff₀ hsq0, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hq0]
      calc 256 * (1 + Real.log B) ^ 2 * (B : ℝ) ^ (1 / 4 : ℝ)
          ≤ 256 * (64 * (B : ℝ) ^ (1 / 4 : ℝ)) * (B : ℝ) ^ (1 / 4 : ℝ) := by gcongr
        _ = 16384 * ((B : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ ≤ 16384 * Real.sqrt B := by gcongr
    simpa using h1.add h2
  obtain ⟨B₃, hB₃⟩ := Metric.tendsto_atTop.mp hg (ε / 3) hε3
  -- the period mean square and the fibre cutoff
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp tendsto_moebiusPeriodMeanSquare (ε / 3) hε3
  have hJt : Tendsto (fun N : ℕ => (143 + 4 * Z) / (fibreCutoff N : ℝ) ^ 3) atTop (𝓝 0) := by
    have h3 := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_fibreCutoff)
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h3).const_mul (143 + 4 * Z)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hJt (ε / 3) hε3
  refine ⟨max (max B₁ B₂) (max B₃ 256), max (max N₁ N₂) 1, fun N hN M hM => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans (le_of_max_le_left hN)
  have hNN₂ : N₂ ≤ N := (le_max_right _ _).trans (le_of_max_le_left hN)
  have hBM : max (max B₁ B₂) (max B₃ 256) ≤ M / N := (Nat.le_div_iff_mul_le (by omega)).mpr hM
  have hBB₁ : B₁ ≤ M / N := (le_max_left _ _).trans ((le_max_left _ _).trans hBM)
  have hBB₂ : B₂ ≤ M / N := (le_max_right _ _).trans ((le_max_left _ _).trans hBM)
  have hBB₃ : B₃ ≤ M / N := (le_max_left _ _).trans ((le_max_right _ _).trans hBM)
  have hB256 : 256 ≤ M / N := (le_max_right _ _).trans ((le_max_right _ _).trans hBM)
  by_cases hcase : M / N ≤ fibreCutoff N
  · -- small band ratio
    have hs := abs_sieveL2PrefixEnergy_div_sub_le_of_band hN1 (by omega : 1 ≤ M / N)
    have e1 := hB₁ (M / N) hBB₁
    have e2 := hB₂ (M / N) hBB₂
    have e3 := hN₂ N hNN₂
    rw [Real.dist_eq] at e1 e2 e3
    have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [sub_zero, abs_of_nonneg (div_nonneg (by linarith) (by positivity))] at e3
    have e4 := bandError_div_le (N := N) (by omega : 1 ≤ M / N) hcase
    linarith
  · -- large band ratio: `N < (J+1)^16 ≤ B^16`
    have hcase' := lt_of_not_ge hcase
    have hNB : N ≤ (M / N) ^ 16 :=
      (lt_fibreCutoff_succ_pow N).le.trans (Nat.pow_le_pow_left hcase' 16)
    have hl := abs_sieveL2PrefixEnergy_div_sub_le_of_le_pow hK0 hK hN1 hB256 hNB
    have e1 := hB₃ (M / N) hBB₃
    have e2 := hN₁ N hNN₁
    rw [Real.dist_eq] at e1 e2
    have hg0 : 0 ≤ 256 * K * E ^ 2 / (1 + Real.log (M / N : ℕ)) +
        256 * (1 + Real.log (M / N : ℕ)) ^ 2 / Real.sqrt (M / N : ℕ) := by
      have := log_natCast_nonneg (M / N)
      have hKE : 0 ≤ 256 * K * E ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hK0) (sq_nonneg _)
      exact add_nonneg (div_nonneg hKE (by linarith)) (by positivity)
    rw [sub_zero, abs_of_nonneg hg0] at e1
    calc |sieveL2PrefixEnergy N M moebiusReal / M - cofinalMobiusSlope|
        ≤ |sieveL2PrefixEnergy N M moebiusReal / M - moebiusPeriodMeanSquare N| +
          |moebiusPeriodMeanSquare N - cofinalMobiusSlope| := abs_sub_le _ _ _
      _ ≤ ε := by linarith

/-- **The Möbius energy transfers at every superlinear horizon.** If `M(N)/N → ∞`, then
`E_N(M(N))/M(N) → κ`. -/
theorem tendsto_sieveL2PrefixEnergy_div {M : ℕ → ℕ}
    (hM : Tendsto (fun N => M N / N) atTop atTop) :
    Tendsto (fun N => sieveL2PrefixEnergy N (M N) moebiusReal / M N) atTop
      (𝓝 cofinalMobiusSlope) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B₀, N₀, h⟩ := exists_abs_sieveL2PrefixEnergy_div_sub_le (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hM.eventually (eventually_ge_atTop B₀))
  refine ⟨max N₀ N₁, fun N hN => ?_⟩
  have h1 : B₀ ≤ M N / N := hN₁ N (le_of_max_le_right hN)
  have h2 : B₀ * N ≤ M N := (Nat.mul_le_mul_right N h1).trans (Nat.div_mul_le_self _ _)
  rw [Real.dist_eq]
  exact (h N (le_of_max_le_left hN) (M N) h2).trans_lt (half_lt_self hε)

end

end GaloisForLFunctions.BezoutValuationIncidence
