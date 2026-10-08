import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# A real-part bound controls a finite Euler product on a smaller polydisc

The C49 proof uses one analytic disc through each point of a finite
polydisc. This avoids choosing compatible phases of local maxima.
The source notch inequality is a separate obligation: this analytic
lemma does not assume that arbitrary Weil deviations are multiplicative.
-/

noncomputable section

open Complex Metric Set

namespace RHTower.WeilSingularArithmetic

/-- The normalized half-disc estimate, including the constant case. -/
theorem norm_half_le_of_re_le {f : ℂ → ℂ} {C : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hzero : f 0 = 1)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (f z).re ≤ C) :
    ‖f (1 / 2)‖ ≤ 2 * C - 1 := by
  have hC : 1 ≤ C := by simpa [hzero] using hre 0 (by simp)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hM : 0 < C - 1 + ε / 2 := by linarith
  have h := Complex.borelCaratheodory_zero (f := fun z => f z - 1)
    (R := 1) (z := 1 / 2) hM (hf.sub_const 1) (fun z hz => by
      change (f z).re - 1 ≤ C - 1 + ε / 2
      linarith [hre z hz]) (by norm_num) (by norm_num [mem_ball_zero_iff])
    (by simp [hzero])
  norm_num at h
  have hn := norm_le_norm_sub_add (f (1 / 2)) (1 : ℂ)
  norm_num at hn
  linarith

/-- A finite product with bounded real part has a uniform product-norm
bound on the half polydisc. No bound on the number of factors is lost. -/
theorem prod_norm_half_le_of_re_prod_le {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) {C : ℝ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) (ball 0 1))
    (hzero : ∀ i, F i 0 = 1)
    (hre : ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) → (∏ i, F i (z i)).re ≤ C)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∏ i, ‖F i (z i / 2)‖ ≤ 2 * C - 1 := by
  have hmap (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) (i : ι) :
      w * z i ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hz i) (norm_nonneg w)).trans_lt
      (by simpa using mem_ball_zero_iff.mp hw)
  have hd : DifferentiableOn ℂ (fun w => ∏ i, F i (w * z i)) (ball 0 1) := by
    apply DifferentiableOn.fun_finsetProd
    intro i _
    exact (hF i).comp (differentiableOn_id.mul_const (z i)) (fun w hw => hmap w hw i)
  have h := norm_half_le_of_re_le hd (by simp [hzero]) (fun w hw =>
    hre (fun i => w * z i) (fun i => mem_ball_zero_iff.mp (hmap w hw i)))
  rw [norm_prod] at h
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

end RHTower.WeilSingularArithmetic
