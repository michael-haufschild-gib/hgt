import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSharpIntervalHandoff

/-!
# Wide-smoothed interval handoff for Menon's Case II

The exact half-width interval kernel has a prohibitively large quadratic-decay constant.  This
module keeps the physical lower edge but uses a common, freely chosen smoothing width at both
endpoints.  The difference agrees with the sharp twisted von Mangoldt interval up to the two
literal transition windows, while its support remains inside the enlarged Heath--Brown cutoff.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Difference of the two common-width Mellin kernels. -/
def menonWideIntervalMellinKernel
    (a b H sigma y : ℝ) : ℂ :=
  mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight b H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I) -
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight a H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I)

/-- The common-width interval kernel is continuous on every positive vertical line. -/
theorem continuous_menonWideIntervalMellinKernel
    {a b H sigma : ℝ} (hH : 0 < H) (hsigma : 0 < sigma) :
    Continuous (menonWideIntervalMellinKernel a b H sigma) := by
  exact (continuous_mellin_smoothWeight_line
      (N := b) (H := H) hH hsigma).sub
    (continuous_mellin_smoothWeight_line
      (N := a) (H := H) hH hsigma)

/-- A twisted von Mangoldt smooth prefix differs from its sharp prefix only on the transition
window, with the exact logarithmic coefficient cost. -/
theorem norm_tsum_vonMangoldtTwist_smoothWeight_sub_partialSum_le_width
    (tau : ℝ) {N : ℕ} {H : ℝ} (hH : 0 < H) (hNH : 1 ≤ (N : ℝ) + H) :
    ‖(∑' n : ℕ, vonMangoldtTwist tau n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (N : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
        ∑ n ∈ Finset.range (N + 1), vonMangoldtTwist tau n‖ ≤
      (H + 1) * Real.log ((N : ℝ) + H) := by
  have h := norm_tsum_mul_smoothWeight_sub_partialSum_le_width
    (a := vonMangoldtTwist tau)
    (show (0 : ℝ) ≤ (N : ℝ) by positivity) hH (Real.log_nonneg hNH)
    (fun n hn hnm =>
      norm_vonMangoldtTwist_le_log tau hNH (by simpa using hn) hnm)
  simpa using h

/-- The difference of two common-width smooth prefixes approximates the literal interval `(a,b]`.
Only the two transition-window masses are lost. -/
theorem norm_tsum_vonMangoldtTwist_wideInterval_sub_sum_Ioc_le
    (tau : ℝ) {a b : ℕ} (hab : a ≤ b) {H : ℝ} (hH : 0 < H)
    (haH : 1 ≤ (a : ℝ) + H) (hbH : 1 ≤ (b : ℝ) + H) :
    ‖((∑' n : ℕ, vonMangoldtTwist tau n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (b : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
        (∑' n : ℕ, vonMangoldtTwist tau n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight
            (a : ℝ) H (n : ℝ) : ℝ) : ℂ))) -
        ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖ ≤
      (H + 1) * Real.log ((b : ℝ) + H) +
        (H + 1) * Real.log ((a : ℝ) + H) := by
  let SB : ℂ := ∑' n : ℕ, vonMangoldtTwist tau n *
    ((GaloisForLFunctions.HTGeometry.smoothWeight
      (b : ℝ) H (n : ℝ) : ℝ) : ℂ)
  let SA : ℂ := ∑' n : ℕ, vonMangoldtTwist tau n *
    ((GaloisForLFunctions.HTGeometry.smoothWeight
      (a : ℝ) H (n : ℝ) : ℝ) : ℂ)
  let PB : ℂ := ∑ n ∈ Finset.range (b + 1), vonMangoldtTwist tau n
  let PA : ℂ := ∑ n ∈ Finset.range (a + 1), vonMangoldtTwist tau n
  have hB : ‖SB - PB‖ ≤ (H + 1) * Real.log ((b : ℝ) + H) := by
    simpa only [SB, PB] using
      norm_tsum_vonMangoldtTwist_smoothWeight_sub_partialSum_le_width
        tau hH hbH
  have hA : ‖SA - PA‖ ≤ (H + 1) * Real.log ((a : ℝ) + H) := by
    simpa only [SA, PA] using
      norm_tsum_vonMangoldtTwist_smoothWeight_sub_partialSum_le_width
        tau hH haH
  have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) := by
    intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  have hset : Finset.range (b + 1) \ Finset.range (a + 1) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hsharp : PB - PA = ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n := by
    dsimp only [PB, PA]
    rw [← Finset.sum_sdiff_eq_sub hsub, hset]
  rw [← hsharp]
  have hid : (SB - SA) - (PB - PA) = (SB - PB) - (SA - PA) := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hB hA)

private theorem summable_mul_smoothWeight_wide
    (f : ℕ → ℂ) {N H : ℝ} (hH : 0 < H) :
    Summable fun n : ℕ => f n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈N + H⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hge : N + H ≤ (n : ℝ) := by
    have h1 : (N + H : ℝ) ≤ (⌈N + H⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈N + H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_lt hn
    push_cast at h2
    linarith
  rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH hge]
  simp

/-- Exact Perron identity for a common-width smoothed interval.  The enlarged cutoff absorbs both
transition windows, while deleting boxes wholly below `a` remains coefficient-exact. -/
theorem smul_tsum_vonMangoldtTwist_wideInterval_eq_integral_windowRelevantAggregate
    (L X k a b : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b) (tau : ℝ)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H sigma : ℝ} (hH : 0 < H) (hsupport : (b : ℝ) + H ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) •
        ((∑' n : ℕ, vonMangoldtTwist tau n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight
              (b : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
          (∑' n : ℕ, vonMangoldtTwist tau n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight
              (a : ℝ) H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
          menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t (a : ℝ)
  let phase : ℕ → ℂ := fun n => (n : ℂ) ^ (-((tau : ℂ) * Complex.I))
  let WB : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight
      (b : ℝ) H (n : ℝ) : ℝ) : ℂ)
  let WA : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight
      (a : ℝ) H (n : ℝ) : ℝ) : ℂ)
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have haPos : 0 < a := by exact_mod_cast haR
  have hbPos : 0 < b := haPos.trans_le hab
  have hXNat : 1 ≤ X := by
    have hbX : b ≤ X := by
      have hbR : (b : ℝ) ≤ (X : ℝ) := by linarith
      exact_mod_cast hbR
    exact (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
  have hpoint : ∀ n : ℕ,
      complexCoeff F n * phase n * (WB n - WA n) =
        vonMangoldtTwist tau n * (WB n - WA n) := by
    intro n
    by_cases hna : n ≤ a
    · have hnb : n ≤ b := hna.trans hab
      have hwa := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one
        hH (show (n : ℝ) ≤ (a : ℝ) by exact_mod_cast hna)
      have hwb := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one
        hH (show (n : ℝ) ≤ (b : ℝ) by exact_mod_cast hnb)
      have hz : WB n - WA n = 0 := by
        dsimp only [WB, WA]
        rw [hwa, hwb]
        norm_num
      rw [hz, mul_zero, mul_zero]
    · have han : a < n := Nat.lt_of_not_ge hna
      by_cases hnX : n ≤ X
      · have hcoeff :=
          complexCoeff_heathBrownWindowRelevantEligiblePacket_eq_vonMangoldt
            L X k hXL hT0 hscale (n := n)
              (by exact_mod_cast han) hnX
        have hcoeff' : complexCoeff F n = ((vonMangoldt n : ℝ) : ℂ) := by
          simpa only [F, complexCoeff_apply] using hcoeff
        rw [hcoeff']
        rfl
      · have hXn : X < n := Nat.lt_of_not_ge hnX
        have hbn : (b : ℝ) + H ≤ (n : ℝ) := by
          have hcast : (X : ℝ) < (n : ℝ) := by exact_mod_cast hXn
          exact hsupport.trans hcast.le
        have han' : (a : ℝ) + H ≤ (n : ℝ) := by
          have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
          linarith
        have hwb := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH hbn
        have hwa := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH han'
        have hz : WB n - WA n = 0 := by
          dsimp only [WB, WA]
          rw [hwb, hwa]
          norm_num
        rw [hz, mul_zero, mul_zero]
  have hsumPB : Summable fun n : ℕ => complexCoeff F n * phase n * WB n := by
    simpa only [mul_assoc] using
      summable_mul_smoothWeight_wide
        (fun n => complexCoeff F n * phase n) (N := (b : ℝ)) hH
  have hsumPA : Summable fun n : ℕ => complexCoeff F n * phase n * WA n := by
    simpa only [mul_assoc] using
      summable_mul_smoothWeight_wide
        (fun n => complexCoeff F n * phase n) (N := (a : ℝ)) hH
  have hsumVB : Summable fun n : ℕ => vonMangoldtTwist tau n * WB n :=
    summable_mul_smoothWeight_wide _ hH
  have hsumVA : Summable fun n : ℕ => vonMangoldtTwist tau n * WA n :=
    summable_mul_smoothWeight_wide _ hH
  have hpacketDiff :
      (∑' n : ℕ, complexCoeff F n * phase n * WB n) -
          (∑' n : ℕ, complexCoeff F n * phase n * WA n) =
        (∑' n : ℕ, vonMangoldtTwist tau n * WB n) -
          (∑' n : ℕ, vonMangoldtTwist tau n * WA n) := by
    rw [← hsumPB.tsum_sub hsumPA, ← hsumVB.tsum_sub hsumVA]
    apply tsum_congr
    intro n
    simpa only [mul_sub] using hpoint n
  have hB := tsum_windowRelevantPacket_twist_smoothWeight_eq_integral
    L X k T0 t (a : ℝ) tau (N := (b : ℝ)) (H := H) (sigma := sigma)
      (by exact_mod_cast hbPos) hH hsigma
  have hA := tsum_windowRelevantPacket_twist_smoothWeight_eq_integral
    L X k T0 t (a : ℝ) tau (N := (a : ℝ)) (H := H) (sigma := sigma)
      haR hH hsigma
  rw [← hpacketDiff, smul_sub, hB, hA]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with y
    simp only [menonWideIntervalMellinKernel]
    ring
  · simpa only [F, phase, WB, WA] using
      integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
        L X k hXNat T0 t (a : ℝ) tau haR (by exact_mod_cast hbPos) hH
          (by linarith : 0 < sigma)
  · simpa only [F, phase, WB, WA] using
      integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
        L X k hXNat T0 t (a : ℝ) tau haR haR hH
          (by linarith : 0 < sigma)

/-- A sharp twisted von Mangoldt interval larger than the two transition-window errors forces a
large common-width vertical integral of the window-relevant Heath--Brown aggregate. -/
theorem norm_integral_windowRelevantAggregate_wide_gt_of_vonMangoldtTwist_Ioc_gt
    (L X k a b : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b) (tau : ℝ)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H B sigma : ℝ} (hH : 0 < H) (haH : 1 ≤ (a : ℝ) + H)
    (hbH : 1 ≤ (b : ℝ) + H) (hsupport : (b : ℝ) + H ≤ X)
    (hsigma : 1 < sigma)
    (hlarge : B +
        ((H + 1) * Real.log ((b : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) <
      ‖∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖) :
    B < ‖∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
        menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ := by
  let S : ℂ :=
    (∑' n : ℕ, vonMangoldtTwist tau n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (b : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
    (∑' n : ℕ, vonMangoldtTwist tau n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (a : ℝ) H (n : ℝ) : ℝ) : ℂ))
  let P : ℂ := ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n
  let E : ℝ := (H + 1) * Real.log ((b : ℝ) + H) +
    (H + 1) * Real.log ((a : ℝ) + H)
  have herr : ‖S - P‖ ≤ E := by
    simpa only [S, P, E] using
      norm_tsum_vonMangoldtTwist_wideInterval_sub_sum_Ioc_le
        tau hab hH haH hbH
  have hnorm := norm_sub_norm_le P S
  have hS : B < ‖S‖ := by
    have hlarge' : B + E < ‖P‖ := by simpa only [P, E] using hlarge
    have hrev : ‖P - S‖ = ‖S - P‖ := norm_sub_rev _ _
    rw [hrev] at hnorm
    linarith
  have hid := smul_tsum_vonMangoldtTwist_wideInterval_eq_integral_windowRelevantAggregate
    L X k a b hXL hab tau T0 t hT0 hscale hH hsupport hsigma
  have hpi : (1 : ℝ) ≤ ‖(2 * Real.pi : ℝ)‖ := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hsmul : ‖S‖ ≤ ‖(2 * Real.pi : ℝ) • S‖ := by
    rw [norm_smul]
    exact le_mul_of_one_le_left (norm_nonneg S) hpi
  rw [show (2 * Real.pi : ℝ) • S =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
          menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y by
        simpa only [S] using hid] at hsmul
  exact hS.trans_le hsmul

end RHTower.Sieve
