import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil

/-!
# The uncertainty law of a producer

A zero `ρ` of `ζ` with `β = Re ρ ∈ (0, 1]` kills the left side of the Mellin identity, so the window
factor `m (1 − B^{-ρ})` must be paid by the tail series. The tail has total pronic mass `T` (the
excess of the slope) and height at most the peak `w`. Interpolating between these two gives

`m ‖1 − B^{-ρ}‖ ≤ ‖ρ‖ (4 + 1/β) w^{1−β} T^β`.

This is convexity between the two ends of the stencil: `s = 1`, where `D_c′(1)` is the slope, and
`s = 0`, where `−D_c(0)` is the peak. Inserting the coefficient mass law gives, for `β ≥ ½` and rate
`ε ≤ 1` on an alphabet in `[1, K]`,

`1 ≤ 24 ‖ρ‖ (2K (1 + log K + (K + 1) ε))^{1−β} ε^β`.

No zero of `ζ` is used to prove this: it is an inequality every zero must satisfy against every
producer. Read against a family of producers it is a zero-free region.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The real step, cut off below `Y`. -/
def tailStep (Y : ℕ) (σ : ℝ) (j : ℕ) : ℝ := if Y ≤ j then realStep σ j else 0

theorem tailStep_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (Y j : ℕ) : 0 ≤ tailStep Y σ j := by
  rw [tailStep]
  split_ifs
  · exact realStep_nonneg hσ j
  · exact le_rfl

/-- The tail of the telescoping weight: `Σ_{j ≥ Y} ((j+1)^{-σ} − (j+2)^{-σ}) ≤ (Y+1)^{-σ}`. -/
theorem sum_range_tailStep_le {σ : ℝ} (hσ : 0 ≤ σ) (Y n : ℕ) :
    ∑ j ∈ range n, tailStep Y σ j ≤ ((Y : ℝ) + 1) ^ (-σ) := by
  have hinv : ∀ n : ℕ, ∑ j ∈ range n, tailStep Y σ j + (((max n Y : ℕ) : ℝ) + 1) ^ (-σ) =
      ((Y : ℝ) + 1) ^ (-σ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : Y ≤ n
      · have h1 : max n Y = n := max_eq_left h
        have h2 : max (n + 1) Y = n + 1 := max_eq_left (by omega)
        rw [h1] at ih
        rw [h2, tailStep, if_pos h, realStep, ← ih]
        push_cast
        rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
        ring
      · have h1 : max n Y = Y := max_eq_right (by omega)
        have h2 : max (n + 1) Y = Y := max_eq_right (by omega)
        rw [h1] at ih
        rw [h2, tailStep, if_neg h, add_zero]
        exact ih
  have h0 : 0 ≤ (((max n Y : ℕ) : ℝ) + 1) ^ (-σ) := by positivity
  linarith [hinv n]

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

theorem peak_pos (hP : IsProducer c m B) : (0 : ℝ) < peak c := by
  have h : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
  linarith [hP.m_pos]

/-- The pointwise split of the tail series into head mass and tail height. -/
theorem norm_tail_term_le (hP : IsProducer c m B) {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    {Y : ℕ} (j : ℕ) :
    ‖((tailWeight c m B j : ℝ) : ℂ) * abelStep s j‖ ≤
      ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) * excessTerm m B c j +
        (peak c : ℝ) * (tailStep Y s.re j / s.re)) := by
  have hG := hP.tailWeight_nonneg j
  have hw := hP.peak_pos
  have hE := hP.excessTerm_nonneg j
  have hs0 := norm_nonneg s
  have hYpow : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg Y) _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hG]
  by_cases hj : Y ≤ j
  · have hstep := norm_abelStep_le hσ0 j
    have hR := realStep_nonneg hσ0.le j
    have hRdiv : 0 ≤ realStep s.re j / s.re := div_nonneg hR hσ0.le
    calc tailWeight c m B j * ‖abelStep s j‖
        ≤ (peak c : ℝ) * (‖s‖ * (realStep s.re j / s.re)) :=
          mul_le_mul (hP.tailWeight_le_peak j) hstep (norm_nonneg _) hw.le
      _ = ‖s‖ * ((peak c : ℝ) * (tailStep Y s.re j / s.re)) := by
          rw [tailStep, if_pos hj]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hs0
          have : 0 ≤ 2 * (Y : ℝ) ^ (1 - s.re) * excessTerm m B c j := by positivity
          linarith
  · have hstep := norm_abelStep_le_rpow hσ0 j
    have hx : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hxY : (j : ℝ) + 1 ≤ Y := by
      have : j + 1 ≤ Y := by omega
      exact_mod_cast this
    have hpow : ((j : ℝ) + 1) ^ (1 - s.re) ≤ (Y : ℝ) ^ (1 - s.re) :=
      Real.rpow_le_rpow hx.le hxY (by linarith)
    have hsplit : ((j : ℝ) + 1) ^ (1 - s.re) = ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (-s.re - 1) := by
      rw [show (1 : ℝ) - s.re = 2 + (-s.re - 1) by ring, Real.rpow_add hx, Real.rpow_two]
    have hdecay : ((j : ℝ) + 1) ^ (-s.re - 1) ≤
        2 * (Y : ℝ) ^ (1 - s.re) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      rw [le_div_iff₀ (by positivity)]
      have hp : 0 ≤ ((j : ℝ) + 1) ^ (-s.re - 1) := by positivity
      have h2 : (j : ℝ) + 2 ≤ 2 * ((j : ℝ) + 1) := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      calc ((j : ℝ) + 1) ^ (-s.re - 1) * (((j : ℝ) + 1) * ((j : ℝ) + 2))
          ≤ ((j : ℝ) + 1) ^ (-s.re - 1) * (((j : ℝ) + 1) * (2 * ((j : ℝ) + 1))) := by gcongr
        _ = 2 * ((j : ℝ) + 1) ^ (1 - s.re) := by rw [hsplit]; ring
        _ ≤ 2 * (Y : ℝ) ^ (1 - s.re) := by gcongr
    have hG' : tailWeight c m B j / (((j : ℝ) + 1) * ((j : ℝ) + 2)) = excessTerm m B c j := by
      rw [tailWeight_eq]
      field_simp
    calc tailWeight c m B j * ‖abelStep s j‖
        ≤ tailWeight c m B j * (‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left hstep hG
      _ ≤ tailWeight c m B j * (‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) /
            (((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by gcongr
      _ = ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) *
            (tailWeight c m B j / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by ring
      _ = ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) * excessTerm m B c j +
            (peak c : ℝ) * (tailStep Y s.re j / s.re)) := by
          rw [hG', tailStep, if_neg hj]; simp

/-- **The tail bound.** For `0 < Re s ≤ 1`, `s ≠ 1`, and every `Y ≥ 1`,
`‖D_c(s) ζ(s) − m (1 − B^{-s})‖ ≤ ‖s‖ (2 Y^{1−σ} T + w Y^{-σ} / σ)`. -/
theorem norm_tail_le (hP : IsProducer c m B) {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    (hs1 : s ≠ 1) {Y : ℕ} (hY : 1 ≤ Y) :
    ‖dirichletPoly c s * riemannZeta s - (m : ℂ) * (1 - ((B : ℝ) : ℂ) ^ (-s))‖ ≤
      ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) * excess c m B + (peak c : ℝ) * ((Y : ℝ) ^ (-s.re) / s.re)) := by
  have htail := (hP.hasSum_tail hσ0 hs1).tendsto_sum_nat.norm
  refine le_of_tendsto' htail fun n => ?_
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hYpow : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - s.re) := Real.rpow_nonneg hYR.le _
  have hw := hP.peak_pos
  have hE : ∑ j ∈ range n, excessTerm m B c j ≤ excess c m B :=
    sum_le_hasSum _ (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess
  have hT : ∑ j ∈ range n, tailStep Y s.re j ≤ (Y : ℝ) ^ (-s.re) := by
    refine (sum_range_tailStep_le hσ0.le Y n).trans ?_
    exact Real.rpow_le_rpow_of_nonpos hYR (by linarith) (by linarith)
  calc ‖∑ j ∈ range n, ((tailWeight c m B j : ℝ) : ℂ) * abelStep s j‖
      ≤ ∑ j ∈ range n, ‖((tailWeight c m B j : ℝ) : ℂ) * abelStep s j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) * excessTerm m B c j +
          (peak c : ℝ) * (tailStep Y s.re j / s.re)) :=
        sum_le_sum fun j _ => hP.norm_tail_term_le hσ0 hσ1 j
    _ = ‖s‖ * (2 * (Y : ℝ) ^ (1 - s.re) * ∑ j ∈ range n, excessTerm m B c j +
          (peak c : ℝ) * ((∑ j ∈ range n, tailStep Y s.re j) / s.re)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum, sum_div]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * (Y : ℝ) ^ (1 - s.re))
        have h2 : (peak c : ℝ) * ((∑ j ∈ range n, tailStep Y s.re j) / s.re) ≤
            (peak c : ℝ) * ((Y : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hT hσ0.le) hw.le
        linarith

/-- At a zero the window is paid by the tail. -/
theorem window_le_of_zero (hP : IsProducer c m B) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ0 : 0 < ρ.re) (hβ1 : ρ.re ≤ 1) {Y : ℕ} (hY : 1 ≤ Y) :
    (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ ≤
      ‖ρ‖ * (2 * (Y : ℝ) ^ (1 - ρ.re) * excess c m B + (peak c : ℝ) * ((Y : ℝ) ^ (-ρ.re) / ρ.re)) := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hρ
  have h := hP.norm_tail_le hβ0 hβ1 hρ1 hY
  rw [hρ, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_natCast] at h
  exact h

/-- **The uncertainty law.** At a zero `ρ` with `0 < β ≤ 1`, if `T ≤ w`,
`m ‖1 − B^{-ρ}‖ ≤ ‖ρ‖ (4 + 1/β) w^{1−β} T^β`. -/
theorem uncertainty_law (hP : IsProducer c m B) {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hβ0 : 0 < ρ.re) (hβ1 : ρ.re ≤ 1) (hTw : excess c m B ≤ peak c) :
    (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ ≤
      ‖ρ‖ * ((4 + 1 / ρ.re) * ((peak c : ℝ) ^ (1 - ρ.re) * excess c m B ^ ρ.re)) := by
  set β := ρ.re with hβ
  set w : ℝ := (peak c : ℝ) with hwdef
  set T := excess c m B with hTdef
  have hT : 0 < T := hP.excess_pos
  have hw : 0 < w := hP.peak_pos
  set y : ℝ := w / T with hy
  have hy1 : 1 ≤ y := by rw [hy, one_le_div hT]; exact hTw
  have hy0 : 0 < y := by linarith
  set Y : ℕ := ⌈y⌉₊ with hYdef
  have hYy : y ≤ Y := Nat.le_ceil y
  have hYle : (Y : ℝ) ≤ 2 * y := by
    have := Nat.ceil_lt_add_one hy0.le
    linarith
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := hy1.trans hYy
    exact_mod_cast this
  have hYR : (0 : ℝ) < Y := by linarith
  have hexp : 0 ≤ 1 - β := by linarith
  have hhead : (Y : ℝ) ^ (1 - β) ≤ 2 * y ^ (1 - β) := by
    calc (Y : ℝ) ^ (1 - β) ≤ (2 * y) ^ (1 - β) := Real.rpow_le_rpow hYR.le hYle hexp
      _ = (2 : ℝ) ^ (1 - β) * y ^ (1 - β) := Real.mul_rpow (by norm_num) hy0.le
      _ ≤ 2 ^ (1 : ℝ) * y ^ (1 - β) := by
          gcongr
          · norm_num
          · linarith
      _ = 2 * y ^ (1 - β) := by rw [Real.rpow_one]
  have htail : (Y : ℝ) ^ (-β) ≤ y ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hy0 hYy (by linarith)
  have hmass1 : y ^ (1 - β) * T = w ^ (1 - β) * T ^ β := by
    rw [hy, Real.div_rpow hw.le hT.le]
    have hTT : T ^ (1 - β) * T ^ β = T := by
      rw [← Real.rpow_add hT, show 1 - β + β = 1 by ring, Real.rpow_one]
    have hne : T ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
    field_simp
    linarith [hTT]
  have hmass2 : w * y ^ (-β) = w ^ (1 - β) * T ^ β := by
    rw [hy, Real.div_rpow hw.le hT.le, Real.rpow_neg hw.le, Real.rpow_neg hT.le]
    have hwT : w ^ β ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
    have hww : w ^ (1 - β) = w / w ^ β := by
      rw [Real.rpow_sub hw, Real.rpow_one]
    rw [hww]
    have hTb : T ^ β ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
    field_simp
  have hkey := hP.window_le_of_zero hρ hβ0 hβ1 hY1
  have hfinal : 2 * (Y : ℝ) ^ (1 - β) * T + w * ((Y : ℝ) ^ (-β) / β) ≤
      (4 + 1 / β) * (w ^ (1 - β) * T ^ β) := by
    have h1 : 2 * (Y : ℝ) ^ (1 - β) * T ≤ 4 * (w ^ (1 - β) * T ^ β) := by
      rw [← hmass1]
      nlinarith
    have h2 : w * ((Y : ℝ) ^ (-β) / β) ≤ (1 / β) * (w ^ (1 - β) * T ^ β) := by
      rw [← hmass2, mul_div_assoc', div_le_iff₀ hβ0]
      have : w * (Y : ℝ) ^ (-β) ≤ w * y ^ (-β) := mul_le_mul_of_nonneg_left htail hw.le
      calc w * (Y : ℝ) ^ (-β) ≤ w * y ^ (-β) := this
        _ = 1 / β * (w * y ^ (-β)) * β := by field_simp
    linarith
  exact hkey.trans (mul_le_mul_of_nonneg_left hfinal (norm_nonneg _))

/-- `1 − 2^{-β} ≥ 1/4` for `β ≥ 1/2`, so the window factor is bounded below. -/
theorem quarter_le_norm_window (hP : IsProducer c m B) {ρ : ℂ} (hβ : 1 / 2 ≤ ρ.re) :
    1 / 4 ≤ ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ := by
  refine le_trans ?_ (hP.one_sub_rpow_le_norm ρ)
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hP.two_le_B
  have h1 : (B : ℝ) ^ (-ρ.re) ≤ (2 : ℝ) ^ (-ρ.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hB2 (by linarith)
  have h2 : (2 : ℝ) ^ (-ρ.re) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hs : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    have hs2 : (4 : ℝ) / 3 ≤ √2 := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  linarith

/-- **The rate law.** A zero `ρ` with `½ ≤ β ≤ 1` and a producer of rate `ε ≤ 1` on an alphabet in
`[1, K]` satisfy `1 ≤ 24 ‖ρ‖ (2K (1 + log K + (K + 1) ε))^{1−β} ε^β`. -/
theorem rate_law (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K)
    (hr : rate c m B ≤ 1) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hβ : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) :
    1 ≤ 24 * ‖ρ‖ * ((2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B)) ^ (1 - ρ.re) *
      rate c m B ^ ρ.re) := by
  set β := ρ.re with hβdef
  set ε := rate c m B with hεdef
  have hβ0 : 0 < β := by linarith
  have hε : 0 < ε := hP.rate_pos
  have hm := hP.m_pos
  have hT0 := hP.excess_pos
  have hTle : excess c m B ≤ (m : ℝ) * ε := hP.excess_le
  have hw0 := hP.peak_pos
  have hwm : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
  have hTw : excess c m B ≤ peak c := by nlinarith
  have hlaw := hP.uncertainty_law hρ hβ0 hβ1 hTw
  have hwin := hP.quarter_le_norm_window (ρ := ρ) hβ
  set W : ℝ := 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * ε) with hW
  have hwW : (peak c : ℝ) ≤ (m : ℝ) * W := by
    have h1 := peak_le_coeffMass c
    have h2 := hP.coeffMass_div_le hK
    rw [div_le_iff₀ hm] at h2
    linarith
  have hW0 : 0 < W := by
    have : (0 : ℝ) < (m : ℝ) * W := lt_of_lt_of_le hw0 hwW
    exact (mul_pos_iff_of_pos_left hm).mp this
  have hexp : 0 ≤ 1 - β := by linarith
  have hpow1 : (peak c : ℝ) ^ (1 - β) ≤ ((m : ℝ) * W) ^ (1 - β) :=
    Real.rpow_le_rpow hw0.le hwW hexp
  have hpow2 : excess c m B ^ β ≤ ((m : ℝ) * ε) ^ β := Real.rpow_le_rpow hT0.le hTle hβ0.le
  have hsplit : ((m : ℝ) * W) ^ (1 - β) * ((m : ℝ) * ε) ^ β = (m : ℝ) * (W ^ (1 - β) * ε ^ β) := by
    rw [Real.mul_rpow hm.le hW0.le, Real.mul_rpow hm.le hε.le]
    have hmm : (m : ℝ) ^ (1 - β) * (m : ℝ) ^ β = m := by
      rw [← Real.rpow_add hm, show 1 - β + β = 1 by ring, Real.rpow_one]
    calc (m : ℝ) ^ (1 - β) * W ^ (1 - β) * ((m : ℝ) ^ β * ε ^ β)
        = ((m : ℝ) ^ (1 - β) * (m : ℝ) ^ β) * (W ^ (1 - β) * ε ^ β) := by ring
      _ = _ := by rw [hmm]
  have hmass : (peak c : ℝ) ^ (1 - β) * excess c m B ^ β ≤ (m : ℝ) * (W ^ (1 - β) * ε ^ β) := by
    rw [← hsplit]
    exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
  have hconst : 4 + 1 / β ≤ 6 := by
    have : 1 / β ≤ 2 := by
      rw [div_le_iff₀ hβ0]; linarith
    linarith
  have hprod : 0 ≤ W ^ (1 - β) * ε ^ β := by positivity
  have hρ0 := norm_nonneg ρ
  have hupper : (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ ≤ ‖ρ‖ * (6 * ((m : ℝ) * (W ^ (1 - β) * ε ^ β))) := by
    refine hlaw.trans (mul_le_mul_of_nonneg_left ?_ hρ0)
    exact mul_le_mul hconst hmass (by positivity) (by norm_num)
  have hlower : (m : ℝ) * (1 / 4) ≤ (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ :=
    mul_le_mul_of_nonneg_left hwin hm.le
  have hcancel : (m : ℝ) * 1 ≤ (m : ℝ) * (24 * ‖ρ‖ * (W ^ (1 - β) * ε ^ β)) := by
    nlinarith
  exact le_of_mul_le_mul_left hcancel hm

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
