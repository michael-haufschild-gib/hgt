import Mathlib

/-!
# A linear derivative bound forces exponential type

If an entire function satisfies `‖F′ z‖ ≤ K(1 + ‖F z‖)` at every point, then along every ray from
the origin the modulus obeys Grönwall's integral inequality, so

```text
‖F z‖ ≤ (1 + ‖F 0‖)·exp(K‖z‖).
```

In particular `F` has order at most one and finite exponential type.  The bound is the exact
analytic content of the tame alternative of an autonomous algebraic differential relation: whenever
the Newton exponent of the relation does not exceed one, the derivative is linearly dominated by the
function and the solution cannot grow faster than an exponential.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Exponential type from a linear derivative bound.**  Grönwall's inequality along the ray
through `z` turns `‖F′‖ ≤ K(1 + ‖F‖)` into `‖F z‖ ≤ (1 + ‖F 0‖)e^{K‖z‖}`. -/
theorem norm_le_mul_exp_of_norm_deriv_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {K : ℝ}
    (hK : 0 < K) (hbd : ∀ z : ℂ, ‖deriv F z‖ ≤ K * (1 + ‖F z‖)) (z : ℂ) :
    ‖F z‖ ≤ (1 + ‖F 0‖) * Real.exp (K * ‖z‖) := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · have h1 : (1 : ℝ) ≤ Real.exp (K * ‖(0 : ℂ)‖) := by
      rw [norm_zero, mul_zero, Real.exp_zero]
    nlinarith [norm_nonneg (F 0), h1]
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  set γ : ℝ → ℂ := fun t => t • z with hγ
  have hγderiv : ∀ t : ℝ, HasDerivAt γ z t := by
    intro t
    simpa [hγ] using (hasDerivAt_id t).smul_const z
  set f : ℝ → ℂ := F ∘ γ with hf
  have hfderiv : ∀ t : ℝ, HasDerivAt f (z • deriv F (γ t)) t := fun t =>
    (hF.differentiableAt (x := γ t)).hasDerivAt.scomp t (hγderiv t)
  have hfcont : ContinuousOn f (Set.Icc 0 1) := by
    refine Continuous.continuousOn ?_
    exact hF.continuous.comp (by fun_prop)
  set L : ℝ := K * ‖z‖ with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le (f := f)
    (f' := fun t => z • deriv F (γ t)) (δ := ‖F 0‖) (K := L) (ε := L) (a := 0) (b := 1)
    hfcont (fun t _ => (hfderiv t).hasDerivWithinAt) (by simp [hf, hγ])
    (fun t _ => by
      have hn : ‖z • deriv F (γ t)‖ = ‖z‖ * ‖deriv F (γ t)‖ := by
        rw [norm_smul]
      have hft : ‖f t‖ = ‖F (γ t)‖ := by rw [hf]; rfl
      rw [hn, hft, hL]
      have hb := hbd (γ t)
      nlinarith [hb, hzn, norm_nonneg (F (γ t))])
    1 (Set.right_mem_Icc.mpr zero_le_one)
  have hfz : f 1 = F z := by
    rw [hf, hγ]
    simp
  rw [hfz, sub_zero, gronwallBound_of_K_ne_0 (ne_of_gt hL0)] at hmain
  have hdiv : L / L = 1 := div_self (ne_of_gt hL0)
  rw [hdiv] at hmain
  simp only [mul_one, one_mul] at hmain
  rw [hL] at hmain
  linarith [hmain]

end GaloisForLFunctions.HTGeometry
