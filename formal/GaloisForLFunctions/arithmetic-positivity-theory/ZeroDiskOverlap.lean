import GaloisForLFunctions.RHTower.XiGlobalPacketDensity
import Mathlib.Analysis.Complex.Basic

/-! Multiplicity-exact disk overlap for the actual Xi divisor. The logarithmic
loss comes from the unconditional zero-count theorem, with no sign assumption. -/

open Complex Set Metric
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

/-- The enlarged strip containing every radius-`1/4` zero disk. -/
def zeroSamplingStrip : Set ℂ := {s | -1/4 ≤ s.re ∧ s.re ≤ 5/4}

/-- Every divisor copy contributes separately to the finite disk overlap. -/
def zeroDiskOverlap (F : Finset XiZeroCopy) (s : ℂ) : ℝ := by
  classical
  exact ∑ q ∈ F, if s ∈ Metric.ball (q.1 : ℂ) (1/4) then 1 else 0

theorem zeroDiskOverlap_nonneg (F : Finset XiZeroCopy) (s : ℂ) :
    0 ≤ zeroDiskOverlap F s := by
  classical
  apply Finset.sum_nonneg
  intro q hq
  split_ifs <;> positivity

private theorem zero_disk_mem_strip (q : XiZeroCopy) {s : ℂ}
    (hs : s ∈ Metric.ball (q.1 : ℂ) (1/4)) : s ∈ zeroSamplingStrip := by
  have hz := xi_divisor_support_re_mem_open_unit q.1
  have hd : ‖s-(q.1 : ℂ)‖ < (1/4 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hr := abs_le.mp (Complex.abs_re_le_norm (s-(q.1 : ℂ)))
  simp only [Complex.sub_re] at hr
  constructor <;> linarith

theorem zeroDiskOverlap_le_packet (F : Finset XiZeroCopy) (s : ℂ) :
    zeroDiskOverlap F s ≤ ((xiUnitHeightPacket s.im).card : ℝ) := by
  classical
  have he : zeroDiskOverlap F s =
      ((F.filter (fun q => s ∈ Metric.ball (q.1 : ℂ) (1/4))).card : ℝ) := by
    simp only [zeroDiskOverlap, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [he]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro q hq
  have hd : ‖s-(q.1 : ℂ)‖ < (1/4 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using (Finset.mem_filter.mp hq).2
  rw [mem_xiUnitHeightPacket]
  have hi := Complex.abs_im_le_norm (s-(q.1 : ℂ))
  simp only [Complex.sub_im] at hi
  rw [abs_sub_comm]
  linarith

/-- A single logarithmic bound controls every finite multiplicity-exact overlap,
and the overlap vanishes outside the enlarged strip. -/
theorem exists_zeroDiskOverlap_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset XiZeroCopy) (s : ℂ),
      zeroDiskOverlap F s ≤
        zeroSamplingStrip.indicator (fun z : ℂ => C*(1+Real.log (2+|z.im|))) s := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_xiUnitHeightPacket_global_log_bound
  refine ⟨C,hC,fun F s => ?_⟩
  by_cases hs : s ∈ zeroSamplingStrip
  · rw [Set.indicator_of_mem hs]
    exact (zeroDiskOverlap_le_packet F s).trans (hbound s.im)
  · rw [Set.indicator_of_notMem hs]
    have he : zeroDiskOverlap F s = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact if_neg (fun h => hs (zero_disk_mem_strip q h))
    rw [he]

end
end GaloisForLFunctions.ArithmeticPositivityTheory
