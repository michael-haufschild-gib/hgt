import GaloisForLFunctions.RHTower.CHMDFiniteDivisorPairing

/-! # Compact tests belong to the literal-source decay class -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

theorem compact_expMomentSource {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ExpMomentSource f := by
  refine ⟨hf, fun c => ?_⟩
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul hf.norm).integrable_of_hasCompactSupport
    hc.norm.mul_left

theorem compact_exp_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C * Real.exp (-|x|) := by
  have hs : HasCompactSupport (fun x => f x * Real.exp |x|) := hc.mul_right
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous
    (hf.mul (Real.continuous_exp.comp continuous_abs))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun x => ?_⟩
  have hb : |f x| * Real.exp |x| ≤ C := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hC x
  calc
    |f x| = (|f x| * Real.exp |x|) * Real.exp (-|x|) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ C * Real.exp (-|x|) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

theorem compact_expDecayTest {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ExpDecayTest f := by
  obtain ⟨C, hC, hb⟩ := compact_exp_bound hf.continuous hc
  obtain ⟨D, hD, hd⟩ := compact_exp_bound (hf.continuous_deriv (by norm_num)) hc.deriv
  refine ⟨hf, 1/2, C+D, by norm_num, add_nonneg hC hD, fun x => ?_⟩
  norm_num only [show (1/2 : ℝ)+1/2 = 1 by norm_num, one_mul]
  constructor <;> nlinarith [hb x, hd x, Real.exp_pos (-|x|)]

theorem compact_source_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ∃ A, LipschitzWith A f := by
  obtain ⟨C, hC⟩ := hc.deriv.exists_bound_of_continuous (hf.continuous_deriv (by norm_num))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨⟨C, hC0⟩, lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by norm_num)) ?_⟩
  intro x
  exact hC x

theorem compact_source_thetaBound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_phiDoobInv hc).exists_bound_of_continuous
    (continuous_phiDoobInv hf)
  refine ⟨M, fun x => ?_⟩
  have h := hM x
  rw [Real.norm_eq_abs, phiDoobInv, abs_div, abs_of_pos (riemannKernelReal_pos x),
    div_le_iff₀ (riemannKernelReal_pos x)] at h
  exact h

end RHTower.CHMDDoobGraph
