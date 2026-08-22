import Mathlib

/-!
# Entire series on a complex normed space

Two elementary but reusable facts.  The Cauchy estimate bounds the differential of a holomorphic
scalar function by its sup norm on a ball divided by the radius, in any complex normed space; and a
series of entire functions with ball-uniform bounds is entire, because those bounds control the
differentials of the terms.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

/-- **Cauchy estimate for the differential.**  A holomorphic scalar function bounded by `C` on a
ball of radius `ρ` around `x` has differential of norm at most `C / ρ` at `x`. -/
theorem norm_fderiv_le_of_forall_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) {x : E} {ρ C : ℝ} (hρ : 0 < ρ)
    (hbd : ∀ y : E, ‖y - x‖ ≤ ρ → ‖f y‖ ≤ C) :
    ‖fderiv ℂ f x‖ ≤ C / ρ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbd x (by simp [hρ.le]))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    set r : ℝ := ρ / ‖v‖ with hr
    have hrpos : 0 < r := by positivity
    have hgd : Differentiable ℂ (f ∘ fun s : ℂ => x + s • v) := hf.comp (by fun_prop)
    have h1 : HasDerivAt (fun s : ℂ => x + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hderiv : HasDerivAt (f ∘ fun s : ℂ => x + s • v) (fderiv ℂ f x v) 0 := by
      have h2 := hf.differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
      rwa [zero_smul, add_zero] at h2
    have hsphere : ∀ s ∈ Metric.sphere (0 : ℂ) r, ‖(f ∘ fun s : ℂ => x + s • v) s‖ ≤ C := by
      intro s hs
      refine hbd _ (le_of_eq ?_)
      have hsn : ‖s‖ = r := by simpa using hs
      rw [add_sub_cancel_left, norm_smul, hsn, hr]
      field_simp
    have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hgd.diffContOnCl hsphere
    rw [hderiv.deriv] at hb
    refine hb.trans (le_of_eq ?_)
    rw [hr]
    field_simp

/-- **A normally convergent series of entire functions on a complex normed space is entire.**  On
every ball the Cauchy estimate turns a uniform bound on the terms into a summable bound on their
differentials, which is exactly the hypothesis of term-by-term differentiation. -/
theorem differentiable_tsum_of_ball_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℕ → E → ℂ} (hf : ∀ j, Differentiable ℂ (f j)) {M : ℝ → ℕ → ℝ}
    (hM : ∀ R : ℝ, Summable (M R))
    (hbd : ∀ (R : ℝ) (j : ℕ) (y : E), ‖y‖ ≤ R + 1 → ‖f j y‖ ≤ M R j) :
    Differentiable ℂ fun y => ∑' j, f j y := by
  intro x
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  have hmem : x ∈ Metric.ball (0 : E) R := by
    simp [Metric.mem_ball, hR]
  have hzero : (0 : E) ∈ Metric.ball (0 : E) R := by simp [hRpos]
  have hderivbd : ∀ (j : ℕ) (y : E), y ∈ Metric.ball (0 : E) R →
      ‖fderiv ℂ (f j) y‖ ≤ M R j := by
    intro j y hy
    have hy' : ‖y‖ < R := by simpa [Metric.mem_ball] using hy
    have := norm_fderiv_le_of_forall_norm_le (hf j) (x := y) (ρ := 1) (C := M R j) one_pos
      (fun z hz => hbd R j z (by
        have : ‖z‖ ≤ ‖y‖ + 1 := by
          have := norm_add_le (z - y) y
          simpa using le_trans (by simpa using this) (by linarith [hz])
        linarith))
    simpa using this
  have hsum0 : Summable fun j => f j (0 : E) :=
    Summable.of_norm_bounded (hM R) fun j => hbd R j 0 (by simp; positivity)
  have := hasFDerivAt_tsum_of_isPreconnected (u := M R) (f := f)
    (f' := fun j y => fderiv ℂ (f j) y) (hM R) Metric.isOpen_ball
    (convex_ball (0 : E) R).isPreconnected (fun j y hy => (hf j y).hasFDerivAt)
    hderivbd hzero hsum0 hmem
  exact this.differentiableAt

end GaloisForLFunctions.HTGeometry
