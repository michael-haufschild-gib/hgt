import GaloisForLFunctions.RHTower.WeilLogShiftFactorialCoefficientCriterion
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Factorial normalization into continuous functions vanishing at infinity

Summable signed coefficients define a continuous paired-kernel potential
vanishing along the cocompact filter. Intrinsic coefficient regularity turns
this into an exact normalization criterion for arbitrary recovery histories.
-/

open Filter Topology Real Zeta23
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

open WeilExcess

theorem continuous_pairedLogKernel (n : ℕ) : Continuous (fun y : ℝ => pairedLogKernel y n) :=
  (continuous_riemannAutocorr.comp (continuous_id.add continuous_const)).add
    (continuous_riemannAutocorr.comp (continuous_id.sub continuous_const))

/-- Each individual paired kernel vanishes as the real shift leaves compact sets. -/
theorem tendsto_pairedLogKernel_cocompact (n : ℕ) :
    Tendsto (fun y : ℝ => pairedLogKernel y n) (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    have heq : (fun y : ℝ => ‖y‖) = (fun y : ℝ => |y|) := funext Real.norm_eq_abs
    rw [← heq]
    exact tendsto_norm_cocompact_atTop
  have hshift (d : ℝ) : Tendsto (fun y : ℝ => |y + d|) (cocompact ℝ) atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [habs.eventually_ge_atTop (b + |d|)] with y hy
    have ht : |y| ≤ |y + d| + |d| := by simpa using abs_sub (y + d) d
    linarith only [hy, ht]
  obtain ⟨C, _, hC⟩ := exists_riemannAutocorr_le
  have hR (d : ℝ) : Tendsto (fun y : ℝ => riemannAutocorr (y + d)) (cocompact ℝ) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun y => riemannAutocorr_nonneg (y + d))
      (Eventually.of_forall fun y => hC (y + d)) ?_
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((hshift d).const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul C
    simpa only [Function.comp_def, mul_zero] using h
  simpa only [pairedLogKernel, sub_eq_add_neg, add_zero] using
    (hR (log n)).add (hR (-log n))

private theorem norm_kernelPotential_term_le (v : ℕ → ℝ) (y : ℝ) (n : ℕ) :
    ‖v n * pairedLogKernel y n‖ ≤ ‖v n‖ * (2 * riemannAutocorr 0) := by
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (pairedLogKernel_pos y n)]
  exact mul_le_mul_of_nonneg_left (pairedLogKernel_le_two_mul_riemannAutocorr_zero y n)
    (abs_nonneg (v n))

/-- Summable coefficients give absolute convergence at every real shift. -/
theorem summable_pairedLogPotential_of_summable (v : ℕ → ℝ) (hv : Summable v) (y : ℝ) :
    Summable (fun n : ℕ => v n * pairedLogKernel y n) :=
  (hv.norm.mul_right (2 * riemannAutocorr 0)).of_norm_bounded
    (fun n => norm_kernelPotential_term_le v y n)

/-- The summable coefficient majorant is uniform on the entire shift line. -/
theorem continuous_pairedLogPotential_of_summable (v : ℕ → ℝ) (hv : Summable v) :
    Continuous (fun y : ℝ => ∑' n : ℕ, v n * pairedLogKernel y n) := by
  exact continuous_tsum (fun n => continuous_const.mul (continuous_pairedLogKernel n))
    (hv.norm.mul_right (2 * riemannAutocorr 0)) (fun n y => norm_kernelPotential_term_le v y n)

/-- Dominated convergence upgrades coefficient summability to vanishing at infinity. -/
theorem tendsto_pairedLogPotential_cocompact_of_summable (v : ℕ → ℝ) (hv : Summable v) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, v n * pairedLogKernel y n) (cocompact ℝ) (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => ∑' n : ℕ, v n * pairedLogKernel y n)
      (cocompact ℝ) (𝓝 (∑' _n : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (hv.norm.mul_right (2 * riemannAutocorr 0)) (fun n => ?_)
      (Eventually.of_forall fun y n => norm_kernelPotential_term_le v y n)
    simpa only [mul_zero] using (tendsto_pairedLogKernel_cocompact n).const_mul (v n)
  simpa only [tsum_zero] using h

/-- The actual paired-kernel sum as a continuous function vanishing at infinity. -/
def pairedLogPotentialC0 (v : ℕ → ℝ) (hv : Summable v) : C₀(ℝ, ℝ) where
  toFun y := ∑' n : ℕ, v n * pairedLogKernel y n
  continuous_toFun := continuous_pairedLogPotential_of_summable v hv
  zero_at_infty' := tendsto_pairedLogPotential_cocompact_of_summable v hv

/-- Factorial regularity at one shift is exactly existence of a single
normalization summable at every shift with a continuous, vanishing sum. -/
theorem weilLogShiftHasFactorialMajorant_iff_exists_vanishing_normalization
    (v : ℕ → ℝ) (c : ℝ) :
    WeilLogShiftHasFactorialMajorant (fun n => v n * pairedLogKernel c n) ↔
      ∃ (m : ℕ) (B : ℝ) (F : C₀(ℝ, ℝ)), 0 < B ∧
        (∀ y : ℝ, Summable (fun n : ℕ =>
          exp (-(B * n)) * (v n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m)) ∧
        ∀ y : ℝ, F y = ∑' n : ℕ,
          exp (-(B * n)) * (v n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m := by
  constructor
  · intro hv
    obtain ⟨m, B, hB, hs⟩ :=
      (weilLogShiftHasFactorialMajorant_iff_summable_coefficient_normalization v c).mp hv
    let w : ℕ → ℝ := fun n => exp (-(B * n)) * v n / (n.factorial : ℝ) ^ m
    have hw : Summable w := hs
    refine ⟨m, B, pairedLogPotentialC0 w hw, hB, ?_, ?_⟩
    · intro y
      exact (summable_pairedLogPotential_of_summable w hw y).congr
        (fun n => by dsimp only [w]; ring)
    · intro y
      change (∑' n : ℕ, w n * pairedLogKernel y n) = _
      apply tsum_congr
      intro n
      dsimp only [w]
      ring
  · rintro ⟨m, B, _, _, hs, _⟩
    exact weilLogShiftHasFactorialMajorant_of_summable_normalization
      (fun n => v n * pairedLogKernel c n) m B (hs c)

/-- Native recovery regularity admits the same vanishing continuous
normalization, without requiring the recovery history to be bounded. -/
theorem weilLogShiftRecoveryMoment_factorial_iff_vanishing_normalization
    (h : ℕ → ℝ) (c : ℝ) :
    WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment c h) ↔
      ∃ (m : ℕ) (B : ℝ) (F : C₀(ℝ, ℝ)), 0 < B ∧
        (∀ y : ℝ, Summable (fun n : ℕ => exp (-(B * n)) *
          weilLogShiftRecoveryMoment y h n / (n.factorial : ℝ) ^ m)) ∧
        ∀ y : ℝ, F y = ∑' n : ℕ, exp (-(B * n)) *
          weilLogShiftRecoveryMoment y h n / (n.factorial : ℝ) ^ m :=
  weilLogShiftHasFactorialMajorant_iff_exists_vanishing_normalization
    (weilDeviation (weilLogShiftRecoveryInverse h)) c

end RHTower
