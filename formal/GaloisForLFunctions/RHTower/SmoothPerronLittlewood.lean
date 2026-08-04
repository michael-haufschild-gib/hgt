import GaloisForLFunctions.RHTower.TwistedMertensOrderLowerBound
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# Universal Littlewood law from a shifted smooth Perron formula

This module isolates the common analytic-to-arithmetic mechanism behind Littlewood bounds.
If a bounded coefficient sequence has a shifted smooth Perron representation on every line
`Re s = Θ + δ`, with the analytic factor growing more slowly than a freely chosen positive power
of height, then its sharp partial sums satisfy `O(N^(Θ+ε))` for every `ε > 0`.

The theorem is independent of the represented Dirichlet series.  Reciprocal Dirichlet
`L`-functions and reciprocal zeta supply separate concrete instances.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Universal smooth-Perron Littlewood law.** -/
theorem partialSumSeq_subpower_of_smoothPerron {b : ℕ → ℂ} {Θ : ℝ}
    (hb : ∀ n : ℕ, ‖b n‖ ≤ 1) (hΘ0 : 0 < Θ) (hΘ1 : Θ ≤ 1)
    (hshift : ∀ δ a : ℝ, 0 < δ → δ < 1 → 0 < a →
      ∃ (F : ℂ → ℂ) (Kb : ℝ), 0 ≤ Kb ∧
        (∀ y : ℝ, ‖F (((Θ + δ : ℝ) : ℂ) + (y : ℝ) * I)‖ ≤
          Kb * (2 + |y|) ^ a) ∧
        ∀ N H : ℝ, 0 < N → 0 < H →
          Integrable (fun y : ℝ => F (((Θ + δ : ℝ) : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              (((Θ + δ : ℝ) : ℂ) + (y : ℝ) * I)) ∧
          (2 * Real.pi : ℝ) • (∑' n : ℕ,
              b n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
            ∫ y : ℝ, F (((Θ + δ : ℝ) : ℂ) + (y : ℝ) * I) *
              mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                (((Θ + δ : ℝ) : ℂ) + (y : ℝ) * I)) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ,
      ‖partialSumSeq b M‖ ≤ A * ((M : ℝ) + 1) ^ (Θ + ε) := by
  intro ε hε
  by_cases hlarge : 1 ≤ Θ + ε
  · refine ⟨1, zero_lt_one, fun M => ?_⟩
    have hlin := norm_partialSumSeq_le hb M
    have hbase : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    calc
      ‖partialSumSeq b M‖ ≤ (M : ℝ) + 1 := hlin
      _ = 1 * ((M : ℝ) + 1) ^ (1 : ℝ) := by rw [one_mul, Real.rpow_one]
      _ ≤ 1 * ((M : ℝ) + 1) ^ (Θ + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hbase hlarge) zero_le_one
  have hrlt : Θ + ε < 1 := lt_of_not_ge hlarge
  have hεlt : ε < 1 := by linarith
  let δ : ℝ := ε / 8
  let a : ℝ := ε / 8
  let q : ℝ := ε / 4
  let c : ℝ := Θ + δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have haq : a < q := by dsimp [a, q]; linarith
  have hq0 : 0 ≤ q := (lt_trans ha haq).le
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c, δ]; linarith
  have hcr : c + q ≤ Θ + ε := by dsimp [c, δ, q]; linarith
  obtain ⟨C₀, C₁, hC₀, hC₁, hmass⟩ :=
    exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  obtain ⟨F, Kb, hKb, hFline0, hsource⟩ := hshift δ a hδ hδ1 ha
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let E : ℝ := 2 * (Kb * 3 ^ a) * (1 / c + P * (1 / (q - a))) * 2 ^ (c + q)
  let Aout : ℝ := E / (2 * Real.pi) + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    have hqa : 0 < q - a := sub_pos.mpr haq
    positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  have hAout : 0 < Aout := by dsimp [Aout]; positivity
  refine ⟨Aout, hAout, fun M => ?_⟩
  rcases M.eq_zero_or_pos with rfl | hM
  · have hzero := norm_partialSumSeq_le hb 0
    have hzero' : ‖partialSumSeq b 0‖ ≤ 1 := by simpa using hzero
    have hAout1 : 1 ≤ Aout := by
      dsimp [Aout]
      have hquot : 0 ≤ E / (2 * Real.pi) := by positivity
      linarith
    simpa using hzero'.trans hAout1
  let B : ℝ := (M : ℝ) + 1
  let r : ℝ := Θ + ε
  let H : ℝ := B ^ r
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hB : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg M]
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by simpa [r] using hrlt
  have hH1 : 1 ≤ H := by dsimp [H]; exact Real.one_le_rpow hB hr.le
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hHle : H ≤ B := by
    dsimp [H]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hr1.le
  have hX : (M : ℝ) + H ≤ 2 * B := by dsimp [B]; linarith
  have hX0 : 0 < (M : ℝ) + H := by positivity
  have hR : ((M : ℝ) + H) / H ≤ 2 * B := by
    calc
      ((M : ℝ) + H) / H ≤ (M : ℝ) + H := div_le_self (by positivity) hH1
      _ ≤ 2 * B := hX
  have hFline : ∀ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * I)‖ ≤
      Kb * (2 + |y|) ^ a := by
    intro y
    simpa only [c] using hFline0 y
  obtain ⟨hprod, hperron⟩ := hsource (M : ℝ) H hMreal hH
  have hmassLine := hmass (M : ℝ) H c a q Kb hMreal hH hc ha.le haq hq1 hKb
    F hFline hprod
  have hpowXc : ((M : ℝ) + H) ^ c ≤ 2 ^ c * B ^ r := by
    calc
      ((M : ℝ) + H) ^ c ≤ (2 * B) ^ c := Real.rpow_le_rpow (by positivity) hX hc.le
      _ = 2 ^ c * B ^ c := Real.mul_rpow (by norm_num) hB0.le
      _ ≤ 2 ^ c * B ^ r :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB (by dsimp [r, c, δ]; linarith))
          (by positivity)
  have hpowRX : (((M : ℝ) + H) / H) ^ q * ((M : ℝ) + H) ^ c
      ≤ 2 ^ (c + q) * B ^ r := by
    have hRq : (((M : ℝ) + H) / H) ^ q ≤ (2 * B) ^ q :=
      Real.rpow_le_rpow (by positivity) hR hq0
    have hXc : ((M : ℝ) + H) ^ c ≤ (2 * B) ^ c :=
      Real.rpow_le_rpow (by positivity) hX hc.le
    calc
      (((M : ℝ) + H) / H) ^ q * ((M : ℝ) + H) ^ c
          ≤ (2 * B) ^ q * (2 * B) ^ c :=
            mul_le_mul hRq hXc (by positivity) (by positivity)
      _ = (2 * B) ^ (c + q) := by rw [← Real.rpow_add (by positivity)]; ring
      _ = 2 ^ (c + q) * B ^ (c + q) := Real.mul_rpow (by norm_num) hB0.le
      _ ≤ 2 ^ (c + q) * B ^ r :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB (by simpa [r] using hcr))
          (by positivity)
  have hcenterTerm :
      2 * (Kb * 3 ^ a * (((M : ℝ) + H) ^ c / c))
        ≤ (2 * (Kb * 3 ^ a) * (1 / c) * 2 ^ (c + q)) * B ^ r := by
    have h2pow : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (c + q) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpow : ((M : ℝ) + H) ^ c ≤ 2 ^ (c + q) * B ^ r :=
      hpowXc.trans (mul_le_mul_of_nonneg_right h2pow (by positivity))
    calc
      2 * (Kb * 3 ^ a * (((M : ℝ) + H) ^ c / c))
          = 2 * (Kb * 3 ^ a) * (1 / c) * ((M : ℝ) + H) ^ c := by ring
      _ ≤ 2 * (Kb * 3 ^ a) * (1 / c) * (2 ^ (c + q) * B ^ r) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 * (Kb * 3 ^ a) * (1 / c) * 2 ^ (c + q)) * B ^ r := by ring
  have htailTerm :
      2 * (Kb * 3 ^ a * (P * (((M : ℝ) + H) / H) ^ q * ((M : ℝ) + H) ^ c)) *
          (1 / (q - a))
        ≤ (2 * (Kb * 3 ^ a) * (P * (1 / (q - a))) * 2 ^ (c + q)) * B ^ r := by
    calc
      2 * (Kb * 3 ^ a * (P * (((M : ℝ) + H) / H) ^ q * ((M : ℝ) + H) ^ c)) *
            (1 / (q - a))
          = 2 * (Kb * 3 ^ a) * (P * (1 / (q - a))) *
              ((((M : ℝ) + H) / H) ^ q * ((M : ℝ) + H) ^ c) := by ring
      _ ≤ 2 * (Kb * 3 ^ a) * (P * (1 / (q - a))) * (2 ^ (c + q) * B ^ r) :=
        mul_le_mul_of_nonneg_left hpowRX (by positivity)
      _ = (2 * (Kb * 3 ^ a) * (P * (1 / (q - a))) * 2 ^ (c + q)) * B ^ r := by ring
  have hmassPower :
      ∫ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight (M : ℝ) H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * I)‖ ≤ E * B ^ r := by
    refine hmassLine.trans ?_
    rw [show C₀ ^ (1 - q) * C₁ ^ q = P by rfl]
    have hadd := add_le_add hcenterTerm htailTerm
    refine hadd.trans_eq ?_
    dsimp [E]
    ring
  have hnormeq := congrArg norm hperron
  have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
      b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ))‖ =
      (2 * Real.pi) * ‖∑' n : ℕ,
        b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi]
  rw [hsmul] at hnormeq
  have hintegralNorm : ‖∫ y : ℝ, F ((c : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ => ((smoothWeight (M : ℝ) H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * I)‖ ≤ E * B ^ r :=
    (norm_integral_le_integral_norm _).trans hmassPower
  rw [← hnormeq] at hintegralNorm
  have hsmooth : ‖∑' n : ℕ,
      b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
      ≤ (E / (2 * Real.pi)) * B ^ r := by
    calc
      ‖∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
          ≤ (E * B ^ r) / (2 * Real.pi) :=
            (le_div_iff₀ hpi).2 (by simpa [mul_comm] using hintegralNorm)
      _ = (E / (2 * Real.pi)) * B ^ r := by ring
  have hcmp := RHTower.Sieve.norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
    hb hMreal hH
  rw [Nat.floor_natCast] at hcmp
  have hsharp : ‖partialSumSeq b M‖ ≤
      ‖∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ + (H + 1) := by
    rw [partialSumSeq]
    have htri := norm_sub_le
      (∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ))
      ((∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
        ∑ n ∈ Finset.range (M + 1), b n)
    have htri' : ‖∑ n ∈ Finset.range (M + 1), b n‖ ≤
        ‖∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ +
          ‖(∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
            ∑ n ∈ Finset.range (M + 1), b n‖ := by
      simpa using htri
    linarith
  have hHpow : H = B ^ r := rfl
  have honePow : 1 ≤ B ^ r := Real.one_le_rpow hB hr.le
  calc
    ‖partialSumSeq b M‖
        ≤ ‖∑' n : ℕ, b n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ + (H + 1) := hsharp
    _ ≤ (E / (2 * Real.pi)) * B ^ r + (B ^ r + 1) := by rw [hHpow]; linarith
    _ ≤ (E / (2 * Real.pi) + 2) * B ^ r := by nlinarith
    _ = Aout * ((M : ℝ) + 1) ^ (Θ + ε) := by rfl

end RHTower
