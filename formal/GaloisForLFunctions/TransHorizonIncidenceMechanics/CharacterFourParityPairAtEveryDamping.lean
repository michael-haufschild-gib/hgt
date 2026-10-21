import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# A parity pair at every damping: the character modulo four

**Bounded sign patterns pay the receiver.** Let `s : ℕ → ℝ` have partial sums bounded by `B` and put
`c(d) = s(d) d^{-ε}`. The hyperbola split of `Σ_{j ≤ n} Σ_{d | j} c(d) = Σ_{d ≤ n} c(d)⌊n/d⌋` at `D`
gives three pieces: the short moduli `d ≤ D`, the long moduli `D < d ≤ n` counted along the cofactor
`k ↦ k+1` as `Σ_k Σ_{D < d ≤ n/k} c(d)`, and the tail `n Σ_{d > D} c(d)/d`. Abel summation against the
antitone weights `d^{-ε}`, `d^{-1-ε}` bounds the last two by the partial sums of `s`, so

`|A_c(n)| ≤ 2BD + 4Bn(D+1)^{-1-ε}`,   and with `D = ⌊n^{1/(2+ε)}⌋`,   `|A_c(n)| ≤ 6B n^{1/(2+ε)}`.

Since `1/(2+ε) < 1/2`, the receiver energy is bounded at every damping `ε > 0`.

**The pair.** For `χ₄`, whose partial sums lie in `{0, 1}` (the additive period four), the weight
`c_χ(d) = χ₄(d) d^{-ε}` has Ramanujan coefficients `χ₄(e) e^{-1-ε} L_ε`, and the nonnegative weight
`c_+(d) = (L_ε/O_ε) 1_{odd}(d) d^{-ε}` has coefficients `χ₄(e)² e^{-1-ε} L_ε = χ₄(e) W_χ(e)`. The
twist `χ₄(e) = (-1)^{Ω₃(e)}` on odd moduli is the parity of the number of prime factors `≡ 3 (mod 4)`:
identical amplitudes, identical translation data, and opposite receiver growth at every
`0 < ε ≤ 1/2` — bounded for `c_χ` by its single-modulus additive cancellation, divergent for `c_+` by
the drift of its odd moduli.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Index bookkeeping -/

theorem dampedSign_sum_range_shift_eq_sub (s : ℕ → ℝ) (k K : ℕ) :
    ∑ i ∈ range K, s (i + k) = ∑ d ∈ range (k + K), s d - ∑ d ∈ range k, s d := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show k + (K + 1) = (k + K) + 1 by omega, Finset.sum_range_succ,
      show K + k = k + K by omega]
    ring

theorem dampedSign_sum_Ioc_eq_sum_range_shift (f : ℕ → ℝ) (D K : ℕ) :
    ∑ d ∈ Ioc D (D + K), f d = ∑ i ∈ range K, f (i + (D + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show D + (K + 1) = D + K + 1 by omega, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ,
      show K + (D + 1) = D + K + 1 by omega]

theorem dampedSign_sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (D : ℕ) :
    ∑ d ∈ range (D + 1), f d = f 0 + ∑ d ∈ Icc 1 D, f d := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

/-! ### Abel bounds for bounded sign patterns -/

/-- Abel's inequality on a block: bounded partial sums against `(i+k)^{-α}`. -/
theorem abs_sum_block_rpow_le {s : ℕ → ℝ} {B α : ℝ} (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {k : ℕ} (hk : 1 ≤ k) (K : ℕ) :
    |∑ i ∈ range K, ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)| ≤ 2 * B * (k : ℝ) ^ (-α) := by
  have h := abs_sum_range_mul_antitone_le (fun i => s (i + k))
    (fun i => ((i + k : ℕ) : ℝ) ^ (-α)) K (by linarith : 0 ≤ 2 * B)
    (fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun i j hij => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast (by omega : i + k ≤ j + k)) (by linarith))
    (fun K' _ => by
      rw [dampedSign_sum_range_shift_eq_sub]
      calc _ ≤ |∑ d ∈ range (k + K'), s d| + |∑ d ∈ range k, s d| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hS (k + K'), hS k])
  simpa using h

/-- Abel's inequality on an infinite tail. -/
theorem abs_tsum_tail_rpow_le {s : ℕ → ℝ} {B α : ℝ} (hB : 0 ≤ B) (hα : 1 < α)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)) ∧
      |∑' i : ℕ, ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)| ≤ 2 * B * (k : ℝ) ^ (-α) := by
  have hs1 : ∀ d, |s d| ≤ 2 * B := fun d => by
    have : s d = ∑ e ∈ range (d + 1), s e - ∑ e ∈ range d, s e := by rw [Finset.sum_range_succ]; ring
    rw [this]
    calc _ ≤ |∑ e ∈ range (d + 1), s e| + |∑ e ∈ range d, s e| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hS (d + 1), hS d]
  have hp : Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-α)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) k).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hsum : Summable (fun i : ℕ => ((i + k : ℕ) : ℝ) ^ (-α) * s (i + k)) := by
    refine (hp.mul_left (2 * B)).of_norm_bounded fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hs1 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨hsum, ?_⟩
  exact le_of_tendsto' hsum.hasSum.tendsto_sum_nat.abs
    fun K => abs_sum_block_rpow_le hB (by linarith) hS hk K

/-! ### The receiver of a bounded sign pattern -/

/-- The damped sign weight `s(d) d^{-ε}`. -/
def dampedSignWeight (s : ℕ → ℝ) (ε : ℝ) (d : ℕ) : ℝ := s d * (d : ℝ) ^ (-ε)

theorem dampedSignWeight_div {s : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    dampedSignWeight s ε d / d = (d : ℝ) ^ (-(1 + ε)) * s d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [dampedSignWeight, Nat.cast_zero, div_zero,
      Real.zero_rpow (show -(1 + ε) ≠ 0 by linarith), zero_mul]
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    rw [dampedSignWeight, show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hd0.ne']
    ring

theorem summable_dampedSignWeight_div {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) :
    Summable (fun d : ℕ => dampedSignWeight s ε d / d) := by
  have h := (abs_tsum_tail_rpow_le hB (by linarith : 1 < 1 + ε) hS (le_refl 1)).1
  refine ((summable_nat_add_iff 1).mp ?_)
  refine h.congr fun i => ?_
  rw [dampedSignWeight_div hε]

/-- **The hyperbola bound.** For partial sums bounded by `B` and every split `1 ≤ D ≤ n`,
`|A_c(n)| ≤ 2BD + 4Bn(D+1)^{-1-ε}`, with `c = s d^{-ε}` and its mean `m = Σ_d c(d)/d`. -/
theorem abs_weightCenteredPrefix_dampedSign_le {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      2 * B * D + 4 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
  set c := dampedSignWeight s ε
  have hs1 : ∀ d, |s d| ≤ 2 * B := fun d => by
    have : s d = ∑ e ∈ range (d + 1), s e - ∑ e ∈ range d, s e := by rw [Finset.sum_range_succ]; ring
    rw [this]
    calc _ ≤ |∑ e ∈ range (d + 1), s e| + |∑ e ∈ range d, s e| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hS (d + 1), hS d]
  have hsum := summable_dampedSignWeight_div hB hε hS
  -- the mean splits at `D`
  have hmean : ∑' d : ℕ, c d / d = ∑ d ∈ Icc 1 D, c d / d +
      ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [← hsum.sum_add_tsum_nat_add (D + 1), dampedSign_sum_range_succ_eq_add_Icc]
    simp [c, dampedSignWeight]
  -- the floor sum splits at `D`
  have hsplit : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) + ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    have h2 : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le D) hDn]
  -- long moduli counted along the cofactor
  have hlong : ∑ d ∈ Ioc D n, c d * ((n / d : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d := by
    have hcount : ∀ d, c d * ((n / d : ℕ) : ℝ) = ∑ _k ∈ Icc 1 (n / d), c d := fun d => by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]; simp
    simp_rw [hcount]
    refine sum_comm' fun d k => ?_
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hDd, hdn⟩, hk1, hkd⟩
      have hd0 : 0 < d := by omega
      have hkd' : k * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp hkd
      refine ⟨⟨hDd, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm k d])⟩,
        hk1, le_trans hkd (Nat.div_le_self n d)⟩
    · rintro ⟨⟨hDd, hdk⟩, hk1, hkn⟩
      have hd0 : 0 < d := by omega
      have hdk' : d * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hdk
      refine ⟨⟨hDd, le_trans hdk (Nat.div_le_self n k)⟩, hk1,
        (Nat.le_div_iff_mul_le hd0).mpr (by linarith [mul_comm k d])⟩
  -- piece (a): short moduli
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤ 2 * B * D := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ 2 * B := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hfl1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hfl2 : (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := n) (show 0 < d by omega)
        have h' : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      have hpow : (d : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd.1) (by linarith)
      have hc : |c d| ≤ 2 * B := by
        rw [show c d = s d * (d : ℝ) ^ (-ε) from rfl, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        calc |s d| * (d : ℝ) ^ (-ε) ≤ 2 * B * 1 :=
              mul_le_mul (hs1 d) hpow (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by linarith)
          _ = 2 * B := mul_one _
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) = c d * (((n / d : ℕ) : ℝ) - n / d) := by
        field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |c d| * |((n / d : ℕ) : ℝ) - n / d| ≤ 2 * B * 1 :=
            mul_le_mul hc hfr (abs_nonneg _) (by linarith)
        _ = 2 * B := mul_one _
    calc ∑ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ ∑ _d ∈ Icc 1 D, 2 * B :=
          sum_le_sum hterm
      _ = 2 * B * D := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  -- piece (b): long moduli
  have hb : |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| ≤
      2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
    have hblock : ∀ k ∈ Icc 1 n, |∑ d ∈ Ioc D (n / k), c d| ≤
        (if D + 1 ≤ n / k then 2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε) else 0) := by
      intro k _
      split_ifs with h
      · obtain ⟨K, hK⟩ : ∃ K, n / k = D + K := ⟨n / k - D, by omega⟩
        rw [hK, dampedSign_sum_Ioc_eq_sum_range_shift]
        have := abs_sum_block_rpow_le hB hε.le hS (k := D + 1) (by omega) K
        simpa [c, dampedSignWeight, mul_comm] using this
      · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hblock).trans ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (n : ℝ) / (D + 1) := by
      have hsub : filter (fun k => D + 1 ≤ n / k) (Icc 1 n) ⊆ Icc 1 (n / (D + 1)) := by
        intro k hk
        simp only [mem_filter, mem_Icc] at hk ⊢
        refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hk.2
        linarith [mul_comm k (D + 1)]
      calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) ≤ (Icc 1 (n / (D + 1))).card := by
            exact_mod_cast card_le_card hsub
        _ = ((n / (D + 1) : ℕ) : ℝ) := by rw [Nat.card_Icc]; simp
        _ ≤ (n : ℝ) / (D + 1) := by
            have := Nat.cast_div_le (α := ℝ) (m := n) (n := D + 1)
            push_cast at this; exact this
    have hD1 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    have hpow : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) = ((D + 1 : ℕ) : ℝ) ^ (-ε) / ((D + 1 : ℕ) : ℝ) := by
      rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hD1.ne']
    rw [hpow]
    have hP : 0 ≤ ((D + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hB2 : 0 ≤ 2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε) := by positivity
    calc ((filter (fun k => D + 1 ≤ n / k) (Icc 1 n)).card : ℝ) * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε))
        ≤ (n : ℝ) / (D + 1) * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_right hcard hB2
      _ = 2 * B * n * (((D + 1 : ℕ) : ℝ) ^ (-ε) / ((D + 1 : ℕ) : ℝ)) := by push_cast; ring
  -- piece (c): the tail
  have hc : |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| ≤
      2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
    have ht := (abs_tsum_tail_rpow_le hB (by linarith : 1 < 1 + ε) hS (k := D + 1) (by omega)).2
    have heq : ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) =
        ∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1)) :=
      tsum_congr fun i => dampedSignWeight_div hε _
    rw [heq, abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |∑' i : ℕ, ((i + (D + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (D + 1))|
        ≤ n * (2 * B * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε))) :=
          mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
      _ = 2 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by ring
  -- assemble
  have hA : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        ∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d -
          (n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit, hlong, hmean]
    ring
  rw [hA]
  calc _ ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
        |∑ k ∈ Icc 1 n, ∑ d ∈ Ioc D (n / k), c d| +
          |(n : ℝ) * ∑' i : ℕ, c (i + (D + 1)) / ((i + (D + 1) : ℕ) : ℝ)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Power saving.** `|A_c(n)| ≤ 6B n^{1/(2+ε)}` for every `n ≥ 1`. -/
theorem abs_weightCenteredPrefix_dampedSign_le_rpow {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      6 * B * (n : ℝ) ^ (1 / (2 + ε)) := by
  set θ := 1 / (2 + ε)
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set D := ⌊(n : ℝ) ^ θ⌋₊
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn1 hθ0.le
  have hD1 : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hx1
  have hDn : D ≤ n := Nat.floor_le_of_le (by
    calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hθ1
      _ = n := Real.rpow_one _)
  have hDle : (D : ℝ) ≤ (n : ℝ) ^ θ := Nat.floor_le (by positivity)
  have hDlt : (n : ℝ) ^ θ < ((D + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one _
  have hmain := abs_weightCenteredPrefix_dampedSign_le hB hε hS hD1 hDn
  have hxpos : 0 < (n : ℝ) ^ θ := by positivity
  have hpow : ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) ≤ ((n : ℝ) ^ θ) ^ (-(1 + ε)) :=
    Real.rpow_le_rpow_of_nonpos hxpos hDlt.le (by linarith)
  have hid : (n : ℝ) * ((n : ℝ) ^ θ) ^ (-(1 + ε)) = (n : ℝ) ^ θ := by
    rw [← Real.rpow_mul hn0.le]
    have h1 : (n : ℝ) * (n : ℝ) ^ (θ * -(1 + ε)) = (n : ℝ) ^ (1 + θ * -(1 + ε)) := by
      rw [Real.rpow_add hn0, Real.rpow_one]
    rw [h1]
    congr 1
    have : (2 + ε) ≠ 0 := by linarith
    simp only [θ]
    field_simp
    ring
  calc _ ≤ 2 * B * D + 4 * B * n * ((D + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := hmain
    _ ≤ 2 * B * (n : ℝ) ^ θ + 4 * B * (n * ((n : ℝ) ^ θ) ^ (-(1 + ε))) := by
        have h1 := mul_le_mul_of_nonneg_left hDle (by linarith : 0 ≤ 2 * B)
        have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4 * B * n)
        nlinarith
    _ = 6 * B * (n : ℝ) ^ θ := by rw [hid]; ring

/-- **Bounded sign patterns pay the receiver at every damping**, with the explicit constant
`36 B² Σ_n n^{2θ-2}`, `θ = 1/(2+ε)`, independent of the sign pattern. -/
theorem weightPronicEnergy_dampedSign_le {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) (T : ℕ) :
    weightPronicEnergy (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) T ≤
      36 * B ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2) := by
  set θ := 1 / (2 + ε)
  have hθ : 2 * θ - 2 < -1 := by
    have : θ < 1 / 2 := by
      simp only [θ]; rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * θ - 2)) := Real.summable_nat_rpow.mpr hθ
  unfold weightPronicEnergy
  have hterm : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤ 36 * B ^ 2 * (n : ℝ) ^ (2 * θ - 2) := by
    intro n hn
    rw [mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hA := abs_weightCenteredPrefix_dampedSign_le_rpow hB hε hS hn.1
    have hA2 : weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n ^ 2
        ≤ (6 * B * (n : ℝ) ^ θ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
    have hrp : ((n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (2 * θ - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.rpow_sub hn0, Real.rpow_two]
      norm_num
      ring_nf
    calc _ ≤ (6 * B * (n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hA2 (by positivity)
      _ ≤ (6 * B * (n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ = 36 * B ^ 2 * (((n : ℝ) ^ θ) ^ 2 / ((n : ℝ) * (n : ℝ))) := by ring
      _ = 36 * B ^ 2 * (n : ℝ) ^ (2 * θ - 2) := by rw [hrp]
  calc _ ≤ ∑ n ∈ Icc 1 T, 36 * B ^ 2 * (n : ℝ) ^ (2 * θ - 2) := sum_le_sum hterm
    _ = 36 * B ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (2 * θ - 2) := by rw [mul_sum]
    _ ≤ 36 * B ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * θ - 2) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)

theorem exists_weightPronicEnergy_dampedSign_le {s : ℕ → ℝ} {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ x, |∑ d ∈ range x, s d| ≤ B) :
    ∃ E : ℝ, ∀ T : ℕ,
      weightPronicEnergy (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) T ≤ E :=
  ⟨_, weightPronicEnergy_dampedSign_le hB hε hS⟩

/-! ### The character `χ₄` -/

/-- `χ₄` as a real function on `ℕ`. -/
def chiFour (d : ℕ) : ℝ := ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℝ)

theorem chiFour_eq (d : ℕ) :
    chiFour d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1 := by
  unfold chiFour
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> simp

theorem chiFour_mul (a b : ℕ) : chiFour (a * b) = chiFour a * chiFour b := by
  simp [chiFour, Nat.cast_mul, map_mul]

theorem chiFour_sq (d : ℕ) : chiFour d ^ 2 = if d % 2 = 1 then 1 else 0 := by
  rw [chiFour_eq]
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · simp [h]
  · rw [if_neg (by omega : ¬ d % 2 = 0), if_pos h]
    split_ifs <;> norm_num

/-- The partial sums of `χ₄` are `1` on the classes `2, 3 (mod 4)` and `0` otherwise. -/
theorem sum_range_chiFour (x : ℕ) :
    ∑ d ∈ range x, chiFour d = if x % 4 = 2 ∨ x % 4 = 3 then 1 else 0 := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ih, chiFour_eq]
    rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h | h | h | h
    · have h2 : x % 2 = 0 := by omega
      have h3 : (x + 1) % 4 = 1 := by omega
      simp [h, h2, h3]
    · have h2 : x % 2 = 1 := by omega
      have h3 : (x + 1) % 4 = 2 := by omega
      simp [h, h2, h3]
    · have h2 : x % 2 = 0 := by omega
      have h3 : (x + 1) % 4 = 3 := by omega
      simp [h, h2, h3]
    · have h2 : x % 2 = 1 := by omega
      have h3 : (x + 1) % 4 = 0 := by omega
      simp [h, h2, h3]

theorem abs_sum_range_chiFour_le (x : ℕ) : |∑ d ∈ range x, chiFour d| ≤ 1 := by
  rw [sum_range_chiFour]; split_ifs <;> norm_num

/-! ### The pair -/

/-- `L_ε = Σ_d χ₄(d) d^{-1-ε}`, the mean of the character weight. -/
def chiFourDampedMass (ε : ℝ) : ℝ := ∑' d : ℕ, dampedSignWeight chiFour ε d / d

/-- The odd indicator. -/
def oddIndicator (d : ℕ) : ℝ := if d % 2 = 1 then 1 else 0

/-- `O_ε = Σ_{d odd} d^{-1-ε}`. -/
def oddDampedMass (ε : ℝ) : ℝ := ∑' d : ℕ, dampedSignWeight oddIndicator ε d / d

/-- **The positive twin** `c_+(d) = (L_ε/O_ε) 1_{odd}(d) d^{-ε}`. -/
def oddDampedTwinWeight (ε : ℝ) (d : ℕ) : ℝ :=
  chiFourDampedMass ε / oddDampedMass ε * dampedSignWeight oddIndicator ε d

theorem oddIndicator_mul (a b : ℕ) : oddIndicator (a * b) = oddIndicator a * oddIndicator b := by
  unfold oddIndicator
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [Nat.mul_mod, ha, hb]

/-- The damped sign weight of a multiplicative sign factors on `c(ek)/(ek)`. -/
theorem dampedSignWeight_mul_div {s : ℕ → ℝ} (hs : ∀ a b, s (a * b) = s a * s b)
    {ε : ℝ} (e k : ℕ) :
    dampedSignWeight s ε (e * k) / ((e * k : ℕ) : ℝ) =
      (dampedSignWeight s ε e / e) * (dampedSignWeight s ε k / k) := by
  unfold dampedSignWeight
  rw [hs, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg e) (Nat.cast_nonneg k)]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem summable_oddIndicator_weight {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => dampedSignWeight oddIndicator ε d / d) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_norm_bounded fun d => ?_
  rw [dampedSignWeight_div hε, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  unfold oddIndicator
  split_ifs <;> simp [Real.rpow_nonneg]

theorem oddDampedMass_pos {ε : ℝ} (hε : 0 < ε) : 0 < oddDampedMass ε := by
  have h := (summable_oddIndicator_weight hε).le_tsum 1 (fun d _ => by
    rw [dampedSignWeight_div hε]
    unfold oddIndicator
    split_ifs <;> simp [Real.rpow_nonneg])
  have h1 : dampedSignWeight oddIndicator ε 1 / (1 : ℕ) = 1 := by
    simp [dampedSignWeight, oddIndicator]
  unfold oddDampedMass
  linarith

theorem chiFourDampedMass_pos {ε : ℝ} (hε : 0 < ε) : 0 < chiFourDampedMass ε := by
  have hsum := summable_dampedSignWeight_div (by norm_num : (0 : ℝ) ≤ 1) hε abs_sum_range_chiFour_le
  have htail := (abs_tsum_tail_rpow_le (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 < 1 + ε)
    abs_sum_range_chiFour_le (k := 5) (by norm_num)).2
  have hsplit := hsum.sum_add_tsum_nat_add 5
  have heq : ∑' i : ℕ, dampedSignWeight chiFour ε (i + 5) / ((i + 5 : ℕ) : ℝ) =
      ∑' i : ℕ, ((i + 5 : ℕ) : ℝ) ^ (-(1 + ε)) * chiFour (i + 5) :=
    tsum_congr fun i => dampedSignWeight_div hε _
  have hhead : ∑ d ∈ range 5, dampedSignWeight chiFour ε d / d = 1 - (3 : ℝ) ^ (-ε) / 3 := by
    norm_num [Finset.sum_range_succ, dampedSignWeight, chiFour_eq]
    ring
  have h3 : (3 : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h5 : (5 : ℝ) ^ (-(1 + ε)) ≤ 1 / 5 := by
    rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one (by norm_num)]
    have : (5 : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    linarith
  have hneg := (abs_le.mp htail).1
  simp only [Nat.cast_ofNat] at hneg
  rw [chiFourDampedMass, ← hsplit, hhead, heq]
  linarith

/-- The character weight's Ramanujan coefficients `W_χ(e) = (c_χ(e)/e) L_ε`. -/
theorem weightRamanujanCoeff_chiFour {ε : ℝ} (e : ℕ) :
    weightRamanujanCoeff (dampedSignWeight chiFour ε) e =
      dampedSignWeight chiFour ε e / e * chiFourDampedMass ε := by
  unfold weightRamanujanCoeff chiFourDampedMass
  simp_rw [dampedSignWeight_mul_div chiFour_mul e]
  exact tsum_mul_left

/-- **The twist on moduli:** `W_{c_+}(e) = χ₄(e) W_χ(e)`. -/
theorem weightRamanujanCoeff_oddTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    weightRamanujanCoeff (oddDampedTwinWeight ε) e =
      chiFour e * weightRamanujanCoeff (dampedSignWeight chiFour ε) e := by
  have hO := (oddDampedMass_pos hε).ne'
  set κ := chiFourDampedMass ε / oddDampedMass ε with hκ
  have hL : weightRamanujanCoeff (oddDampedTwinWeight ε) e =
      κ * (dampedSignWeight oddIndicator ε e / e * oddDampedMass ε) := by
    unfold weightRamanujanCoeff oddDampedMass
    have hterm : ∀ k : ℕ, oddDampedTwinWeight ε (e * k) / ((e * k : ℕ) : ℝ) =
        κ * (dampedSignWeight oddIndicator ε e / e * (dampedSignWeight oddIndicator ε k / k)) := by
      intro k
      rw [oddDampedTwinWeight, mul_div_assoc, dampedSignWeight_mul_div oddIndicator_mul e k]
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left]
  have hsq : chiFour e ^ 2 = oddIndicator e := chiFour_sq e
  rw [hL, weightRamanujanCoeff_chiFour]
  calc κ * (dampedSignWeight oddIndicator ε e / e * oddDampedMass ε)
      = (κ * oddDampedMass ε) * (dampedSignWeight oddIndicator ε e / e) := by ring
    _ = chiFourDampedMass ε * (dampedSignWeight oddIndicator ε e / e) := by
        rw [hκ, div_mul_cancel₀ _ hO]
    _ = chiFour e * (dampedSignWeight chiFour ε e / e * chiFourDampedMass ε) := by
        unfold dampedSignWeight
        rw [← hsq]
        ring

theorem abs_weightRamanujanCoeff_oddTwin {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    |weightRamanujanCoeff (oddDampedTwinWeight ε) e| =
      |weightRamanujanCoeff (dampedSignWeight chiFour ε) e| := by
  rw [weightRamanujanCoeff_oddTwin hε, abs_mul, weightRamanujanCoeff_chiFour]
  rcases Nat.mod_two_eq_zero_or_one e with h | h
  · simp [dampedSignWeight, chiFour_eq, h]
  · have : |chiFour e| = 1 := by
      rw [chiFour_eq, if_neg (by omega)]; split_ifs <;> norm_num
    rw [this, one_mul]

theorem oddDampedTwinWeight_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ oddDampedTwinWeight ε d := by
  unfold oddDampedTwinWeight dampedSignWeight oddIndicator
  have := div_pos (chiFourDampedMass_pos hε) (oddDampedMass_pos hε)
  split_ifs <;> positivity

theorem hasSum_oddDampedTwinWeight_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => oddDampedTwinWeight ε d / d) (chiFourDampedMass ε) := by
  have hO := (oddDampedMass_pos hε).ne'
  have h := ((summable_oddIndicator_weight hε).hasSum.mul_left
    (chiFourDampedMass ε / oddDampedMass ε))
  rw [← oddDampedMass, div_mul_cancel₀ _ hO] at h
  refine h.congr_fun fun d => ?_
  simp only [oddDampedTwinWeight, mul_div_assoc]

/-- The odd moduli in `(n, 2n]` carry the drift of the positive twin. -/
theorem oddTwin_drift_ge {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    chiFourDampedMass ε / oddDampedMass ε / 8 * n * (2 * (n : ℝ)) ^ (-ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), oddDampedTwinWeight ε d / d := by
  set κ := chiFourDampedMass ε / oddDampedMass ε
  have hκ : 0 < κ := div_pos (chiFourDampedMass_pos hε) (oddDampedMass_pos hε)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2n : (0 : ℝ) < 2 * n := by linarith
  -- the odd numbers `2j+1`, `(n+1)/2 ≤ j < n`, lie in `(n, 2n]`
  set J := Ico ((n + 1) / 2) n
  have hmaps : ∀ j ∈ J, 2 * j + 1 ∈ Ioc n (2 * n) := by
    intro j hj; rw [mem_Ico] at hj; rw [mem_Ioc]; constructor <;> omega
  have hinj : Set.InjOn (fun j => 2 * j + 1) J := fun a _ b _ h => by simp at h; omega
  have hterm : ∀ j ∈ J, κ * (2 * (n : ℝ)) ^ (-1 - ε) ≤
      oddDampedTwinWeight ε (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
    intro j hj
    have hd := hmaps j hj
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
    have hdle : ((2 * j + 1 : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have hodd : oddIndicator (2 * j + 1) = 1 := by simp [oddIndicator, Nat.add_mod]
    rw [oddDampedTwinWeight, dampedSignWeight, hodd, one_mul, mul_div_assoc,
      show ((2 * j + 1 : ℕ) : ℝ) ^ (-ε) / ((2 * j + 1 : ℕ) : ℝ) =
        ((2 * j + 1 : ℕ) : ℝ) ^ (-1 - ε) by
        rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one hd0.ne']]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)) hκ.le
  have himg : ∑ d ∈ J.image (fun j => 2 * j + 1), oddDampedTwinWeight ε d / (d : ℝ) =
      ∑ j ∈ J, oddDampedTwinWeight ε (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := sum_image hinj
  have hsub : ∑ j ∈ J, oddDampedTwinWeight ε (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ≤
      ∑ d ∈ Ioc n (2 * n), oddDampedTwinWeight ε d / d := by
    rw [← himg]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ =>
      div_nonneg (oddDampedTwinWeight_nonneg hε d) (Nat.cast_nonneg d)
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    exact hmaps j hj
  have hcard : (n : ℝ) / 4 ≤ J.card := by
    rw [Nat.card_Ico]
    have : n / 4 ≤ n - (n + 1) / 2 := by omega
    calc (n : ℝ) / 4 ≤ ((n / 4 : ℕ) : ℝ) + 1 := by
          have := Nat.lt_div_mul_add (a := n) (show 0 < 4 by norm_num)
          have h' : (n : ℝ) < ((n / 4 : ℕ) : ℝ) * 4 + 4 := by exact_mod_cast this
          linarith
      _ ≤ _ := by
          have h2 : n / 4 + 1 ≤ n - (n + 1) / 2 := by omega
          exact_mod_cast h2
  have hlow := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hlow
  have hpow : (2 * (n : ℝ)) ^ (-1 - ε) = (2 * (n : ℝ)) ^ (-ε) / (2 * n) := by
    rw [show -1 - ε = -ε - 1 by ring, Real.rpow_sub_one h2n.ne']
  have hP : 0 ≤ (2 * (n : ℝ)) ^ (-ε) := Real.rpow_nonneg h2n.le _
  have key : (n : ℝ) / 4 * (κ * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))) ≤
      ∑ d ∈ Ioc n (2 * n), oddDampedTwinWeight ε d / d := by
    rw [← hpow]
    exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans (hlow.trans hsub)
  have e1 : κ / 8 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) =
      (n : ℝ) * ((n : ℝ) / 4 * (κ * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)))) := by
    have := hn0.ne'
    field_simp
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left key hn0.le

/-- **The `χ₄` parity pair at every damping `0 < ε ≤ 1/2`.** The character weight
`c_χ = χ₄(d) d^{-ε}` and the positive odd weight `c_+` have Ramanujan coefficients related by the twist
`W_{c_+}(e) = χ₄(e) W_χ(e)` — identical amplitudes — while the first receiver energy is bounded and
the second diverges. -/
theorem chiFour_parityPair {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ e : ℕ, weightRamanujanCoeff (oddDampedTwinWeight ε) e =
        chiFour e * weightRamanujanCoeff (dampedSignWeight chiFour ε) e) ∧
    (∀ e : ℕ, |weightRamanujanCoeff (oddDampedTwinWeight ε) e| =
        |weightRamanujanCoeff (dampedSignWeight chiFour ε) e|) ∧
    (∀ d : ℕ, 0 ≤ oddDampedTwinWeight ε d) ∧
    (∃ E : ℝ, ∀ T : ℕ,
        weightPronicEnergy (dampedSignWeight chiFour ε) (chiFourDampedMass ε) T ≤ E) ∧
    Tendsto (fun T => weightPronicEnergy (oddDampedTwinWeight ε) (chiFourDampedMass ε) T)
      atTop atTop :=
  ⟨weightRamanujanCoeff_oddTwin hε, abs_weightRamanujanCoeff_oddTwin hε,
    oddDampedTwinWeight_nonneg hε,
    exists_weightPronicEnergy_dampedSign_le (by norm_num) hε abs_sum_range_chiFour_le,
    tendsto_weightPronicEnergy_of_drift (oddDampedTwinWeight_nonneg hε)
      (hasSum_oddDampedTwinWeight_div hε)
      (by have := div_pos (chiFourDampedMass_pos hε) (oddDampedMass_pos hε); positivity)
      hε2 2 fun n hn => oddTwin_drift_ge hε hn⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
