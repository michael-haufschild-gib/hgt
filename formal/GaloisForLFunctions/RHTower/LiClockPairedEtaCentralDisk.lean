import GaloisForLFunctions.RHTower.DQPTEtaDeriv
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A source-only denominator floor for paired eta near the center

Every odd-even pair is positive at the real center `1 / 2`, and its first
pair already exceeds `1 / 4`. The installed paired-eta derivative bound is
at most `16` on the larger closed disk of radius `1 / 4`. The complex convex
mean-value estimate therefore gives a strict real-part floor of `1 / 8` on
the closed disk of radius `1 / 128`.

The two installed definitions of paired eta agree literally, including at
points where their defining sums are not summable. The denominator floor
and its norm and nonvanishing consequences are exported for `pairedEtaCore`.
-/

open Complex Set Metric

namespace RHTower
noncomputable section

open DQPT

local notation "c" => ((1 / 2 : ℝ) : ℂ)

private theorem etaPair_center_re_gt_quarter : (1 / 4 : ℝ) < (etaPair c).re := by
  let a : ℕ → ℝ := fun n => (2 * n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) -
    (2 * n + 2 : ℝ) ^ (-(1 / 2 : ℝ))
  have ha : Summable a := by
    rw [← Complex.summable_ofReal]
    apply (summable_etaTerm c (by norm_num)).congr
    intro n
    rw [etaTerm_ofReal]
  have hle : a 0 ≤ ∑' n, a n :=
    ha.le_tsum 0 (fun n _ => (etaRealTerm_pos (1 / 2) (by norm_num) n).le)
  have hs0 := Real.sqrt_nonneg 2
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hslarge : (4 / 3 : ℝ) < Real.sqrt 2 := by nlinarith
  have hi : (Real.sqrt 2)⁻¹ < (3 / 4 : ℝ) := by
    rw [← one_div]
    apply (div_lt_iff₀ hspos).2
    nlinarith
  have ha0 : (1 / 4 : ℝ) < a 0 := by
    simp only [a, Nat.cast_zero, mul_zero, zero_add, Real.one_rpow]
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    linarith
  have heq : etaPair c = ((∑' n, a n : ℝ) : ℂ) := by
    rw [etaPair, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [etaTerm_ofReal]
  rw [heq, Complex.ofReal_re]
  exact ha0.trans_le hle

private theorem etaPair_quarter_disk_increment_le {s : ℂ}
    (hs : ‖s - c‖ ≤ (1 / 4 : ℝ)) :
    ‖etaPair s - etaPair c‖ ≤ 16 * ‖s - c‖ := by
  have hgeom (z : ℂ) (hz : z ∈ closedBall c (1 / 4)) :
      (1 / 4 : ℝ) ≤ z.re ∧ ‖z‖ ≤ (3 / 4 : ℝ) := by
    have hn : ‖z - c‖ ≤ (1 / 4 : ℝ) := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre : |z.re - 1 / 2| ≤ (1 / 4 : ℝ) := by
      have h := Complex.abs_re_le_norm (z - c)
      simp only [Complex.sub_re, Complex.ofReal_re] at h
      exact h.trans hn
    have hc : ‖c‖ = (1 / 2 : ℝ) := by norm_num [Complex.norm_real, Real.norm_eq_abs]
    have hnorm := norm_sub_norm_le z c
    rw [hc] at hnorm
    constructor
    · linarith [(abs_le.mp hre).1]
    · linarith
  have hp (z : ℂ) (hz : z ∈ closedBall c (1 / 4)) : 0 < z.re :=
    lt_of_lt_of_le (by norm_num) (hgeom z hz).1
  have hb (z : ℂ) (hz : z ∈ closedBall c (1 / 4)) :
      ‖∑' n : ℕ, dqptEtaTermDeriv z n‖ ≤ (16 : ℝ) := by
    obtain ⟨hre, hn⟩ := hgeom z hz
    have hq : ‖z‖ / z.re ^ 2 ≤ (12 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos (hp z hz))).2
      nlinarith
    have hi : 1 / z.re ≤ (4 : ℝ) := by
      apply (div_le_iff₀ (hp z hz)).2
      linarith
    exact (dqpt_norm_etaPairDeriv_le (hp z hz)).trans (by linarith)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hasDerivAt_etaPair (hp z hz)).hasDerivWithinAt)
    hb (convex_closedBall c (1 / 4)) (mem_closedBall_self (by norm_num))
    (show s ∈ closedBall c (1 / 4) by simpa only [mem_closedBall, dist_eq_norm] using hs)

/-- The paired arithmetic source has a strict real-part floor on the closed central disk. -/
theorem liClockEtaPair_re_gt_one_eighth_of_norm_sub_half_le {s : ℂ}
    (hs : ‖s - ((1 / 2 : ℝ) : ℂ)‖ ≤ (1 / 128 : ℝ)) :
    (1 / 8 : ℝ) < (etaPair s).re := by
  have h := etaPair_quarter_disk_increment_le (hs.trans (by norm_num))
  have hn : ‖etaPair s - etaPair c‖ ≤ (1 / 8 : ℝ) := h.trans (by nlinarith)
  have hre := Complex.abs_re_le_norm (etaPair s - etaPair c)
  simp only [Complex.sub_re] at hre
  have hdelta := (abs_le.mp (hre.trans hn)).1
  linarith [etaPair_center_re_gt_quarter]

/-- Exact identification of the two installed odd-even eta sums, with no domain premise. -/
theorem liClockPairedEtaCore_eq_etaPair (s : ℂ) :
    RiemannGaussian.pairedEtaCore s = etaPair s := by
  unfold RiemannGaussian.pairedEtaCore etaPair
  apply tsum_congr
  intro n
  simp [RiemannGaussian.pairedEtaCoreSummand, etaTerm]

/-- The source-only central real-part floor in the `pairedEtaCore` normalization. -/
theorem liClockPairedEtaCore_re_gt_one_eighth_of_norm_sub_half_le {s : ℂ}
    (hs : ‖s - ((1 / 2 : ℝ) : ℂ)‖ ≤ (1 / 128 : ℝ)) :
    (1 / 8 : ℝ) < (RiemannGaussian.pairedEtaCore s).re := by
  rw [liClockPairedEtaCore_eq_etaPair]
  exact liClockEtaPair_re_gt_one_eighth_of_norm_sub_half_le hs

/-- A strict norm floor for central eta denominators. -/
theorem liClockPairedEtaCore_norm_gt_one_eighth_of_norm_sub_half_le {s : ℂ}
    (hs : ‖s - ((1 / 2 : ℝ) : ℂ)‖ ≤ (1 / 128 : ℝ)) :
    (1 / 8 : ℝ) < ‖RiemannGaussian.pairedEtaCore s‖ :=
  (liClockPairedEtaCore_re_gt_one_eighth_of_norm_sub_half_le hs).trans_le
    (abs_le.mp (Complex.abs_re_le_norm (RiemannGaussian.pairedEtaCore s))).2

/-- The complete paired arithmetic source is nonzero throughout the closed central disk. -/
theorem liClockPairedEtaCore_ne_zero_of_norm_sub_half_le {s : ℂ}
    (hs : ‖s - ((1 / 2 : ℝ) : ℂ)‖ ≤ (1 / 128 : ℝ)) :
    RiemannGaussian.pairedEtaCore s ≠ 0 := by
  intro hz
  have h := liClockPairedEtaCore_re_gt_one_eighth_of_norm_sub_half_le hs
  norm_num [hz] at h

end
end RHTower
