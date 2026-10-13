import GaloisForLFunctions.RHTower.PaperWoldMovingRectangle

/-! # Exact vanishing criterion for moving composite observations

No convergence assumption on the exponent sequence is required. The norm
defect vanishes exactly when exponent distance times logarithmic window size
vanishes. All operators retain the original composite arithmetic matrix.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

private theorem exponential_loss_tendsto_iff {α : Type*} (l : Filter α) (f : α → ℝ) :
    Tendsto (fun a => 1 - Real.exp (-(f a))) l (𝓝 0) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro h
    have he : Tendsto (fun a => Real.exp (-(f a))) l (𝓝 1) := by
      simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
    have hl := he.log (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Real.log_exp, Real.log_one, neg_neg, neg_zero] using hl.neg
  · intro h
    have he := (Real.continuous_exp.tendsto (-(0 : ℝ))).comp h.neg
    simpa only [Function.comp_def, neg_zero, Real.exp_zero, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub he

/-- Uniform two-sided bounds give an exact criterion for every coupled sequence. -/
theorem paperWoldCompositePrefixDefect_norm_tendsto_zero_iff
    (t : ℕ → {t : ℝ // t ≤ 1 / 2}) (M : ℕ → ℕ) :
    Tendsto (fun N => ‖paperWoldCompositePrefixDefect (t N) (M N)‖) atTop (𝓝 0) ↔
    Tendsto (fun N => paperWoldCompositeObservationClock (t N) (M N)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hl : Tendsto
        (fun N => 1 - Real.exp (-(paperWoldCompositeObservationClock (t N) (M N) / 2)))
        atTop (𝓝 0) := by
      apply squeeze_zero
        (fun N => sub_nonneg.mpr (Real.exp_le_one_iff.mpr
          (by linarith [paperWoldCompositeObservationClock_nonneg (t N) (M N)])))
        (fun N => ?_) (by simpa only [mul_zero] using h.const_mul 16)
      have := paperWoldCompositePrefixDefect_clock_lower (t N) (M N)
      linarith
    have hhalf := (exponential_loss_tendsto_iff atTop _).mp hl
    convert hhalf.mul_const 2 using 1 <;> simp
  · intro h
    have hl := (exponential_loss_tendsto_iff atTop
      (fun N => 3 * paperWoldCompositeObservationClock (t N) (M N))).mpr
        (by simpa only [mul_zero] using h.const_mul 3)
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun N => paperWoldCompositePrefixDefect_clock_upper (t N) (M N))
      (by simpa only [mul_zero] using hl.const_mul 5)

/-- The criterion concerns operator-norm convergence of the complete finite observations. -/
theorem paperWoldCompositePrefixDefect_tendsto_zero_iff
    (t : ℕ → {t : ℝ // t ≤ 1 / 2}) (M : ℕ → ℕ) :
    Tendsto (fun N => paperWoldCompositePrefixDefect (t N) (M N)) atTop (𝓝 0) ↔
    Tendsto (fun N => (1 - 2 * (t N : ℝ)) * Real.log ((M N : ℝ) + 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, paperWoldCompositePrefixDefect_norm_tendsto_zero_iff]
  rfl

theorem paperWoldCompositeObservationClock_approach (N M : ℕ) :
    paperWoldCompositeObservationClock (paperWoldCompositeApproachParameter N) M =
      2 * (Real.log ((M : ℝ) + 1) / ((N : ℝ) + 1)) := by
  rw [paperWoldCompositeObservationClock, paperWoldCompositeDampingTime_coe]
  change (1 - 2 * (1 / 2 - ((N : ℝ) + 1)⁻¹)) * Real.log ((M : ℝ) + 1) = _
  ring

/-- Along the literal approach, precisely the subexponential logarithmic windows vanish. -/
theorem paperWoldCompositeApproach_prefix_tendsto_zero_iff (M : ℕ → ℕ) :
    Tendsto (fun N => paperWoldCompositePrefixDefect (paperWoldCompositeApproachParameter N) (M N))
      atTop (𝓝 0) ↔
    Tendsto (fun N => Real.log ((M N : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, paperWoldCompositePrefixDefect_norm_tendsto_zero_iff]
  simp only [paperWoldCompositeObservationClock_approach]
  constructor
  · intro h
    convert h.div_const 2 using 1 <;> simp
  · intro h
    simpa only [mul_zero] using h.const_mul 2

/-- Exact finite vanishing is already classified by the same clock. -/
theorem paperWoldCompositePrefixDefect_eq_zero_iff (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    paperWoldCompositePrefixDefect t M = 0 ↔ paperWoldCompositeObservationClock t M = 0 := by
  constructor
  · intro h
    have hlo := paperWoldCompositePrefixDefect_clock_lower t M
    rw [h, norm_zero] at hlo
    have he : Real.exp 0 ≤ Real.exp (-(paperWoldCompositeObservationClock t M / 2)) := by
      rw [Real.exp_zero]
      linarith
    have := Real.exp_le_exp.mp he
    linarith [paperWoldCompositeObservationClock_nonneg t M]
  · intro h
    apply norm_eq_zero.mp
    have hu := paperWoldCompositePrefixDefect_clock_upper t M
    simp only [h, mul_zero, neg_zero, Real.exp_zero, sub_self] at hu
    exact le_antisymm hu (norm_nonneg _)

/-- A nontrivial original prefix vanishes precisely at the critical exponent. -/
theorem paperWoldCompositePrefixDefect_eq_zero_classification
    (t : {t : ℝ // t ≤ 1 / 2}) (M : ℕ) :
    paperWoldCompositePrefixDefect t M = 0 ↔ (t : ℝ) = 1 / 2 ∨ M = 0 := by
  rw [paperWoldCompositePrefixDefect_eq_zero_iff, paperWoldCompositeObservationClock,
    paperWoldCompositeDampingTime_coe, mul_eq_zero]
  have ht : 1 - 2 * (t : ℝ) = 0 ↔ (t : ℝ) = 1 / 2 := by
    constructor <;> intro h <;> linarith
  have hM : Real.log ((M : ℝ) + 1) = 0 ↔ M = 0 := by
    rw [Real.log_eq_zero]
    constructor
    · rintro (h | h | h)
      · linarith [Nat.cast_nonneg (α := ℝ) M]
      · exact_mod_cast (show (M : ℝ) = 0 by linarith)
      · linarith [Nat.cast_nonneg (α := ℝ) M]
    · intro h
      simp [h]
  rw [ht, hM]

end
end RHTower
