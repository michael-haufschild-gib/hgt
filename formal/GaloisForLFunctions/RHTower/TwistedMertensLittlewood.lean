import GaloisForLFunctions.RHTower.TwistedOrderLawTheta
import GaloisForLFunctions.RHTower.TwistedMobiusPerronShift
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# Littlewood bound for twisted Mertens sums

The existing zero-abscissa theory gives subpolynomial bounds for `1 / L(s, χ)` on every shifted
line, and the shifted Perron theorem identifies its Mellin integral with the smoothed twisted
Mertens sum.  Sharp support-length Mellin decay now bounds that integral at the correct cutoff
scale.  Unsmoothing therefore proves the classical Littlewood estimate

`M_χ(X) = O(X^(Θ_χ + ε))`

for every nontrivial primitive Dirichlet character.  This discharges the
`TwistedMertensSubpowerBound` interface in the companion order law.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {Q : ℕ} [NeZero Q]

/-- **Unconditional twisted Littlewood estimate at the zero abscissa.** -/
theorem twistedMertensSubpowerBound_zeroAbscissa {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) : TwistedMertensSubpowerBound χ (zeroAbscissa χ) := by
  intro ε hε
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  have hθ0 : 0 < zeroAbscissa χ := zeroAbscissa_pos hχ hprim
  have hθ1 : zeroAbscissa χ ≤ 1 := zeroAbscissa_le_one hχ hprim
  by_cases hlarge : 1 ≤ zeroAbscissa χ + ε
  · refine ⟨1, zero_lt_one, fun M => ?_⟩
    have hlin := norm_partialSumSeq_le hcoeff M
    have hbase : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    calc
      ‖partialSumSeq (↗χ * ↗μ) M‖ ≤ (M : ℝ) + 1 := hlin
      _ = 1 * ((M : ℝ) + 1) ^ (1 : ℝ) := by rw [one_mul, Real.rpow_one]
      _ ≤ 1 * ((M : ℝ) + 1) ^ (zeroAbscissa χ + ε) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hbase hlarge) zero_le_one
  have hrlt : zeroAbscissa χ + ε < 1 := lt_of_not_ge hlarge
  have hεlt : ε < 1 / 2 := by linarith [half_le_zeroAbscissa hχ hprim]
  let dlt : ℝ := ε / 8
  let a : ℝ := ε / 8
  let q : ℝ := ε / 4
  let c : ℝ := zeroAbscissa χ + dlt
  have hdlt : 0 < dlt := by dsimp [dlt]; positivity
  have hdlt1 : dlt < 1 := by dsimp [dlt]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have haq : a < q := by dsimp [a, q]; linarith
  have hq0 : 0 ≤ q := by exact (lt_trans ha haq).le
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c, dlt]; linarith
  have hcr : c + q ≤ zeroAbscissa χ + ε := by dsimp [c, dlt, q]; linarith
  obtain ⟨C₀, C₁, hC₀, hC₁, hmass⟩ :=
    exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
    exists_shift_data hχ hprim hdlt hdlt1 ha (2 : ℝ)
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let E : ℝ := 2 * (Kb * 3 ^ a) * (1 / c + P * (1 / (q - a))) * 2 ^ (c + q)
  let Aout : ℝ := E / (2 * Real.pi) + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    have : 0 < q - a := sub_pos.mpr haq
    positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  have hAout : 0 < Aout := by dsimp [Aout]; positivity
  refine ⟨Aout, hAout, fun M => ?_⟩
  rcases M.eq_zero_or_pos with rfl | hM
  · have hzero := norm_partialSumSeq_le hcoeff 0
    have hzero' : ‖partialSumSeq (↗χ * ↗μ) 0‖ ≤ 1 := by simpa using hzero
    have hAout1 : 1 ≤ Aout := by
      dsimp [Aout]
      have hquot : 0 ≤ E / (2 * Real.pi) := by positivity
      linarith
    simpa using hzero'.trans hAout1
  let B : ℝ := (M : ℝ) + 1
  let r : ℝ := zeroAbscissa χ + ε
  let H : ℝ := B ^ r
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hB : 1 ≤ B := by
    dsimp [B]
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
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
      ((M : ℝ) + H) / H ≤ (M : ℝ) + H :=
        div_le_self (by positivity) hH1
      _ ≤ 2 * B := hX
  let F : ℂ → ℂ := fun s => (DirichletCharacter.LFunction χ s)⁻¹
  have hline : ∀ y : ℝ, ((c : ℂ) + (y : ℝ) * I) ∈ verticalStrip c 2 :=
    fun y => line_mem_verticalStrip le_rfl hc2 y
  have hFline : ∀ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * I)‖ ≤ Kb * (2 + |y|) ^ a := by
    intro y
    simpa [F] using hFbd ((c : ℂ) + (y : ℝ) * I) (hline y)
  have hprod : Integrable fun y : ℝ => F ((c : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ => ((smoothWeight (M : ℝ) H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * I) :=
    integrable_mul_mellin_smoothWeight_line hMreal hH hc hFdiff.continuousOn hKb ha.le hFbd
      le_rfl hc2
  have hmassLine := hmass (M : ℝ) H c a q Kb hMreal hH hc ha.le haq hq1 hKb F hFline hprod
  have hpowXc : ((M : ℝ) + H) ^ c ≤ 2 ^ c * B ^ r := by
    calc
      ((M : ℝ) + H) ^ c ≤ (2 * B) ^ c := Real.rpow_le_rpow (by positivity) hX hc.le
      _ = 2 ^ c * B ^ c := Real.mul_rpow (by norm_num) hB0.le
      _ ≤ 2 ^ c * B ^ r := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB (by dsimp [r, c, dlt]; linarith)) (by positivity)
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
      _ ≤ 2 ^ (c + q) * B ^ r := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB (by simpa [r] using hcr)) (by positivity)
  have hcenterTerm :
      2 * (Kb * 3 ^ a * (((M : ℝ) + H) ^ c / c))
        ≤ (2 * (Kb * 3 ^ a) * (1 / c) * 2 ^ (c + q)) * B ^ r := by
    have h2pow : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (c + q) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpow : ((M : ℝ) + H) ^ c ≤ 2 ^ (c + q) * B ^ r :=
      hpowXc.trans (mul_le_mul_of_nonneg_right h2pow (by positivity))
    have hcInv : 0 ≤ 1 / c := by positivity
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
    have hqaInv : 0 ≤ 1 / (q - a) := by positivity
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
  have hperron := twistedMobius_perron_shift hχ hprim hdlt hdlt1 ha hMreal hH
    (σ := 2) (by norm_num) hc2
  have hnormeq := congrArg norm hperron
  have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
      (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ))‖ =
      (2 * Real.pi) * ‖∑' n : ℕ,
        (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi]
  rw [hsmul] at hnormeq
  have hintegralNorm : ‖∫ y : ℝ, F ((c : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ => ((smoothWeight (M : ℝ) H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * I)‖ ≤ E * B ^ r :=
    (norm_integral_le_integral_norm _).trans hmassPower
  rw [← hnormeq] at hintegralNorm
  have hsmooth : ‖∑' n : ℕ,
      (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
      ≤ (E / (2 * Real.pi)) * B ^ r := by
    calc
      ‖∑' n : ℕ, (↗χ * ↗μ) n *
          ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
          ≤ (E * B ^ r) / (2 * Real.pi) :=
            (le_div_iff₀ hpi).2 (by simpa [mul_comm] using hintegralNorm)
      _ = (E / (2 * Real.pi)) * B ^ r := by ring
  have hcmp := RHTower.Sieve.norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
    hcoeff hMreal hH
  rw [Nat.floor_natCast] at hcmp
  have hsharp : ‖partialSumSeq (↗χ * ↗μ) M‖ ≤
      ‖∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ +
        (H + 1) := by
    rw [partialSumSeq]
    have htri := norm_sub_le
      (∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ))
      ((∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
        ∑ n ∈ Finset.range (M + 1), (↗χ * ↗μ) n)
    have htri' : ‖∑ n ∈ Finset.range (M + 1), (↗χ * ↗μ) n‖ ≤
        ‖∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ +
          ‖(∑' n : ℕ, (↗χ * ↗μ) n * ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
            ∑ n ∈ Finset.range (M + 1), (↗χ * ↗μ) n‖ := by
      simpa using htri
    linarith
  have hHpow : H = B ^ r := rfl
  have honePow : 1 ≤ B ^ r := Real.one_le_rpow hB hr.le
  calc
    ‖partialSumSeq (↗χ * ↗μ) M‖
        ≤ ‖∑' n : ℕ, (↗χ * ↗μ) n *
            ((smoothWeight (M : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ + (H + 1) := hsharp
    _ ≤ (E / (2 * Real.pi)) * B ^ r + (B ^ r + 1) := by rw [hHpow]; linarith
    _ ≤ (E / (2 * Real.pi) + 2) * B ^ r := by nlinarith
    _ = Aout * ((M : ℝ) + 1) ^ (zeroAbscissa χ + ε) := by rfl

/-- **Unconditional companion order law `(R15)`.** -/
theorem limsup_mertens_eq_zeroAbscissa {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {j : ℕ} :
    Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) Filter.atTop
      = 2 * ((j : ℝ) + 1) * (1 + zeroAbscissa χ) - 1 :=
  limsup_mertens_eq_of_subpowerBound hχ hprim
    (twistedMertensSubpowerBound_zeroAbscissa hχ hprim)

end RHTower
