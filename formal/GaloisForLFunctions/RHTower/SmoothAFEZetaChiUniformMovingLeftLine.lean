import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedTwoHeadTruncation
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiLeftPowerBound

/-!
# Uniform power growth on moving left lines

One constant controls `χ(1/2-d+it)` for every displacement in a compact
interval.  Compactness handles bounded height; the explicit left-strip Gamma
estimate supplies `max(1,|t|)^d` outside it.
-/

noncomputable section

namespace RHTower

open Complex Set

theorem exists_norm_zetaChi_moving_left_line_le_rpow
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 ≤ d → d ≤ d₀ → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K * (max 1 |t|) ^ d := by
  let S : Set (ℝ × ℝ) := Icc 0 d₀ ×ˢ Icc (-1) 1
  let f : ℝ × ℝ → ℂ := fun p =>
    zetaChi (((1 / 2 - p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f S := by
    intro p hp
    have hp0 : 0 ≤ p.1 := hp.1.1
    have hgamma : Gammaℝ
        (1 - (((1 / 2 - p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)) ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      norm_num
      linarith
    have hinner : ContinuousAt (fun q : ℝ × ℝ =>
        (((1 / 2 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p := by
      fun_prop
    have hz : ContinuousAt zetaChi
        (((1 / 2 - p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I) :=
      (zetaChi_analyticAt hgamma).continuousAt
    have hcomp : ContinuousAt
        (zetaChi ∘ fun q : ℝ × ℝ =>
          (((1 / 2 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.comp
        (f := fun q : ℝ × ℝ =>
          (((1 / 2 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I))
        (g := zetaChi) hz hinner
    simpa [f, Function.comp_def] using hcomp.continuousWithinAt
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  let C₀ : ℝ := max 0 C
  let B : ℝ := 4 + Real.pi
  let A₀ : ℝ := Real.exp (d₀ * B)
  let K : ℝ := max C₀ A₀
  have hB : 0 < B := by dsimp only [B]; linarith [Real.pi_pos]
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  have hK : 0 ≤ K := hA₀.le.trans (le_max_right _ _)
  refine ⟨K, hK, fun d hd0 hdd₀ t => ?_⟩
  rw [norm_zetaChi_real_add_im_eq_abs]
  let q : ℝ := max 1 |t|
  change ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ ≤
    K * q ^ d
  by_cases ht : |t| ≤ 1
  · have hmem : (d, |t|) ∈ S :=
      ⟨⟨hd0, hdd₀⟩, ⟨by linarith [abs_nonneg t], ht⟩⟩
    have hcompact :
        ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ ≤ C₀ :=
      (hC (d, |t|) hmem).trans (le_max_right _ _)
    have hq : q = 1 := max_eq_left ht
    rw [hq, Real.one_rpow, mul_one]
    exact hcompact.trans (le_max_left _ _)
  · have ht1 : 1 < |t| := lt_of_not_ge ht
    have ht0 : 0 < |t| := zero_lt_one.trans ht1
    have hleft := norm_zetaChi_le_left_line
      (σ := 1 / 2 - d) (t := |t|)
      (by linarith) (by linarith) ht0
    have hbracket :
        (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) +
            (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) -
            Real.log Real.pi ≤
          Real.log |t| + B := by
      have hlog :
          (1 / 2 : ℝ) * Real.log
              ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) ≤ Real.log |t| := by
        have hle : ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) ≤ |t| ^ 2 := by
          nlinarith
        have hpos : 0 < (1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2 := by positivity
        have h := Real.log_le_log hpos hle
        rw [Real.log_pow] at h
        push_cast at h
        linarith
      have hinv : (1 : ℝ) / (|t| / 2) ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hpi : Real.pi / (2 * (|t| / 2)) ≤ Real.pi := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
      have hlogpi : 0 ≤ Real.log Real.pi :=
        Real.log_nonneg (by linarith [Real.pi_gt_three])
      dsimp only [B]
      linarith
    have hexp :
        Real.exp ((1 / 2 - (1 / 2 - d)) *
          ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) +
            (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) -
            Real.log Real.pi)) ≤
          Real.exp (d * (Real.log |t| + B)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hbracket hd0]
    have hsplit : Real.exp (d * (Real.log |t| + B)) =
        |t| ^ d * Real.exp (d * B) := by
      rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
      congr 1
      ring
    have hAd : Real.exp (d * B) ≤ A₀ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hdd₀ hB.le
    have hmax : q = |t| := max_eq_right ht1.le
    rw [hmax]
    calc
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖
          ≤ Real.exp ((1 / 2 - (1 / 2 - d)) *
            ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (|t| / 2) ^ 2) +
              (1 / (|t| / 2) ^ 2 + Real.pi / (2 * (|t| / 2))) -
              Real.log Real.pi)) := hleft
      _ ≤ Real.exp (d * (Real.log |t| + B)) := hexp
      _ = |t| ^ d * Real.exp (d * B) := hsplit
      _ ≤ |t| ^ d * A₀ := by
        exact mul_le_mul_of_nonneg_left hAd (Real.rpow_nonneg (abs_nonneg t) d)
      _ ≤ K * |t| ^ d := by
        have hAK : A₀ ≤ K := le_max_right _ _
        nlinarith [Real.rpow_nonneg (abs_nonneg t) d]

end RHTower
