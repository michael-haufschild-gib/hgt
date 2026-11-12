import GaloisForLFunctions.MatomakiRadziwill.LadderExceptional
import GaloisForLFunctions.RHTower.Sieve.LogPolyWindowHMRecip

/-!
# Halász–Montgomery for a cofactor polynomial on a set of frequencies

For the cofactor range `(lo, 4lo]`, `lo ≥ 1`, and a measurable `E ⊆ [−W, W]`, `W ≥ 1`
(`setIntegral_normSq_blockR_le_HM`):

`∫_E |R_v|² ≤ (2π)^{-1} · hmMassRecip(⌊4lo⌋, 2πW, 2π|E|) · 4/lo`,

where `hmMassRecip N T e = 2N + K(N,T)·e + 48πN log(2 + 2T)` and `K ≪ √T log T`
(`Sieve.setIntegral_normSq_logPoly_le_HM_window_recip`).  The coefficients `f(m)/((ω(m)+1)m)` are at
most `1/lo` on the range, which holds `≤ 4lo` integers.  The gain over the mean value theorem is the
factor `|E|`: on a set of measure `≪ lo/√W` the cofactor costs only a logarithm.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem hmMassRecip_nonneg (N : ℕ) {T e : ℝ} (hT : 1 ≤ T) (he : 0 ≤ e) : 0 ≤ hmMassRecip N T e := by
  unfold hmMassRecip
  have h1 := plainKernelFarConst_nonneg N hT
  have h2 : 0 ≤ Real.log (2 + 2 * T) := Real.log_nonneg (by linarith)
  have := Real.pi_pos
  positivity

/-- **Halász–Montgomery for a cofactor polynomial.** -/
theorem setIntegral_normSq_blockR_le_HM {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (Pr : Finset ℕ)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (v : ℕ) (hlo : 1 ≤ cofLo X H v)
    {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hW : 1 ≤ W) (hEs : E ⊆ Icc (-W) W) :
    (∫ w in E, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹ * (hmMassRecip ⌊4 * cofLo X H v⌋₊ (2 * Real.pi * W)
          (2 * Real.pi * volume.real E) * (4 / cofLo X H v)) := by
  classical
  set lo := cofLo X H v with hlodef
  set D := cof rest X H v with hDdef
  have hlo0 : 0 < lo := by linarith
  set a : ℕ → ℂ := fun m => if m ∈ D then coefC f Pr m else 0 with ha
  have ha1 : ∀ m, ‖a m‖ ≤ 1 / lo := by
    intro m
    simp only [ha]
    split_ifs with hm
    · have hm' := (mem_cof.mp hm).1
      exact (norm_coefC_le hf Pr m).trans (one_div_le_one_div_of_le hlo0 hm'.le)
    · rw [norm_zero]; positivity
  have hcongr : ∀ w, blockR f Pr rest X H v w = logPoly a D w := fun w =>
    logPoly_congr (fun m hm => (if_pos hm).symm) w
  have hN : 1 ≤ ⌊4 * lo⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hDsub : D ⊆ Icc 1 ⌊4 * lo⌋₊ := by
    intro m hm
    have hm' := mem_cof.mp hm
    rw [Finset.mem_Icc]
    have h1 : (1 : ℝ) ≤ m := le_trans hlo hm'.1.le
    exact ⟨by exact_mod_cast h1, Nat.le_floor hm'.2.1⟩
  have hbase := setIntegral_normSq_logPoly_le_HM_window_recip a hN hDsub hEm hW hEs
    (by positivity : (0 : ℝ) ≤ 1 / lo) ha1
  simp_rw [hcongr]
  have hcard : (1 / lo) ^ 2 * (D.card : ℝ) ≤ 4 / lo := by
    have h := card_cof_le rest X H v
    rw [← hlodef, ← hDdef] at h
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hlo0]
    nlinarith
  have hmass := hmMassRecip_nonneg ⌊4 * lo⌋₊ (T := 2 * Real.pi * W) (e := 2 * Real.pi * volume.real E)
    (by nlinarith [Real.pi_gt_three]) (by have := Real.pi_pos; positivity)
  calc (∫ w in E, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹ * (hmMassRecip ⌊4 * lo⌋₊ (2 * Real.pi * W) (2 * Real.pi * volume.real E)
          * ((1 / lo) ^ 2 * (D.card : ℝ))) := hbase
    _ ≤ (2 * Real.pi)⁻¹ * (hmMassRecip ⌊4 * lo⌋₊ (2 * Real.pi * W)
          (2 * Real.pi * volume.real E) * (4 / lo)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard hmass) ?_
        have := Real.pi_pos
        positivity

end

end GaloisForLFunctions.MatomakiRadziwill
