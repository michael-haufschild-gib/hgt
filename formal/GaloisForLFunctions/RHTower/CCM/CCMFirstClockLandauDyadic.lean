import GaloisForLFunctions.RHTower.CCM.CCMFirstClockLandauHalving

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Dyadic Landau abscissa after `n` universal halving steps. -/
def ccmFirstClockDyadicThreshold (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

theorem ccmFirstClockDyadicThreshold_pos (n : ℕ) :
    0 < ccmFirstClockDyadicThreshold n := by
  unfold ccmFirstClockDyadicThreshold
  positivity

theorem ccmFirstClockDyadicThreshold_le_one_half (n : ℕ) :
    ccmFirstClockDyadicThreshold n ≤ 1 / 2 := by
  unfold ccmFirstClockDyadicThreshold
  rw [pow_succ]
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem ccmFirstClockDyadicThreshold_succ (n : ℕ) :
    ccmFirstClockDyadicThreshold (n + 1) =
      ccmFirstClockDyadicThreshold n / 2 := by
  unfold ccmFirstClockDyadicThreshold
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  ring

/-- Iterated universal Landau descent: every dyadic positive abscissa is reached. -/
theorem ccmFirstClockTailMomentsAbove_dyadic
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    ∀ n : ℕ, CCMFirstClockTailMomentsAbove
      (ccmFirstClockDyadicThreshold n) := by
  intro n
  induction n with
  | zero =>
      simpa [ccmFirstClockDyadicThreshold] using
        ccmFirstClockTailMomentsAbove_one_half
  | succ n ih =>
      rw [ccmFirstClockDyadicThreshold_succ]
      exact ccmFirstClockTailMomentsAbove_half hsource
        (ccmFirstClockDyadicThreshold_pos n)
        (ccmFirstClockDyadicThreshold_le_one_half n) ih

/-- **CCM positive-abscissa completeness law.** Published first-clock source
nonnegativity forces the literal infinite tail to possess every strictly positive
Laplace moment. -/
theorem ccmFirstClockTailMomentsAbove_zero
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    CCMFirstClockTailMomentsAbove 0 := by
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < a :=
    exists_pow_lt_of_lt_one ha (by norm_num)
  have hthreshold : ccmFirstClockDyadicThreshold n < a := by
    unfold ccmFirstClockDyadicThreshold
    rw [pow_succ]
    have hpowpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    nlinarith
  exact ccmFirstClockTailMomentsAbove_dyadic hsource n a hthreshold

end

end RHTower
