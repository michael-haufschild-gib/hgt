import GaloisForLFunctions.HTGeometry.MagnitudePolynomialExponentialDomination
import GaloisForLFunctions.HTGeometry.RatioShiftGrowth

/-!
# Shift-stable superlacunary domination universality

Superlacunary growth is stable under subtracting any fixed nonnegative shift.  Combining that
stability with polynomial-versus-exponential domination shows that every shifted magnitude
eventually dominates every fixed positive polynomial scale.  Natural shifts give the uniform
growth law needed after any fixed formal differentiation order.
-/

open Filter

namespace GaloisForLFunctions

/-- Eventual positivity and a divergent successive ratio already force the sequence itself to tend
to infinity; no separate divergence hypothesis is needed. -/
theorem tendsto_atTop_of_eventually_pos_ratio_tendsto_atTop {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    Tendsto b atTop atTop := by
  have hquot :=
    tendsto_div_natCast_atTop_of_ratio_tendsto_atTop hpos hratio
  refine tendsto_atTop_mono' atTop ?_ hquot
  filter_upwards [hpos, eventually_ge_atTop 1] with n hbn hn
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnReal
  rw [div_le_iff₀ hnPos]
  nlinarith

/-- Every fixed nonnegative shift of a positive superlacunary magnitude eventually dominates each
fixed positive polynomial scale through its exponential. -/
theorem exists_const_mul_pow_lt_exp_sub_div_of_ratio {b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {c : ℝ} (hc : 0 ≤ c)
    (A : ℝ) (hA : 0 < A) (C E R : ℕ) (hC : 0 < C) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀,
      A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
        Real.exp ((b m - c) / ((R : ℝ) + 1)) := by
  have hpos : ∀ᶠ n in atTop, 0 < b n - c :=
    (hb.eventually_gt_atTop c).mono (fun _ hn => sub_pos.mpr hn)
  exact exists_const_mul_pow_lt_exp_div_of_ratio hpos
    (ratio_sub_nonneg_const_tendsto_atTop hb hratio hc) A hA C E R hC

/-- **Shift-stable superlacunary domination universality law.**  A nonnegative constant shift
simultaneously preserves positivity at infinity, the divergent successive ratio, and domination
of every fixed positive polynomial scale. -/
theorem shiftStableSuperlacunaryDominationUniversality {b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {c : ℝ} (hc : 0 ≤ c) :
    (∀ᶠ n in atTop, 0 < b n - c) ∧
      Tendsto (fun n => (b (n + 1) - c) / (b n - c)) atTop atTop ∧
      ∀ (A : ℝ), 0 < A → ∀ (C E R : ℕ), 0 < C →
        ∃ M₀ : ℕ, ∀ m ≥ M₀,
          A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
            Real.exp ((b m - c) / ((R : ℝ) + 1)) := by
  refine ⟨(hb.eventually_gt_atTop c).mono (fun _ hn => sub_pos.mpr hn),
    ratio_sub_nonneg_const_tendsto_atTop hb hratio hc, ?_⟩
  intro A hA C E R hC
  exact exists_const_mul_pow_lt_exp_sub_div_of_ratio hb hratio hc A hA C E R hC

/-- Divergence of the source need not be assumed: eventual positivity and the divergent successive
ratio alone force the complete shift-stable domination law. -/
theorem eventuallyPositiveShiftStableSuperlacunaryDominationUniversality {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {c : ℝ} (hc : 0 ≤ c) :
    (∀ᶠ n in atTop, 0 < b n - c) ∧
      Tendsto (fun n => (b (n + 1) - c) / (b n - c)) atTop atTop ∧
      ∀ (A : ℝ), 0 < A → ∀ (C E R : ℕ), 0 < C →
        ∃ M₀ : ℕ, ∀ m ≥ M₀,
          A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
            Real.exp ((b m - c) / ((R : ℝ) + 1)) :=
  shiftStableSuperlacunaryDominationUniversality
    (tendsto_atTop_of_eventually_pos_ratio_tendsto_atTop hpos hratio) hratio hc

/-- Every fixed natural support shift, hence every fixed formal differentiation order, inherits the
full shifted domination law. -/
theorem naturalShiftSuperlacunaryDominationUniversality {b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    (j : ℕ) :
    (∀ᶠ n in atTop, 0 < b n - j) ∧
      Tendsto (fun n => (b (n + 1) - j) / (b n - j)) atTop atTop ∧
      ∀ (A : ℝ), 0 < A → ∀ (C E R : ℕ), 0 < C →
        ∃ M₀ : ℕ, ∀ m ≥ M₀,
          A * ((C : ℝ) * ((m : ℝ) + 1)) ^ E <
            Real.exp ((b m - j) / ((R : ℝ) + 1)) := by
  simpa using
    (shiftStableSuperlacunaryDominationUniversality hb hratio
      (show (0 : ℝ) ≤ (j : ℝ) by positivity))

end GaloisForLFunctions
