import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field

/-!
# Derivative decay from one-sided inverse-square curvature

A finite function limit and an actual second derivative bounded below by -C/y²
force the actual first derivative to zero. Correcting the derivative by C/y gives
monotonicity; unit forward and backward secants retain explicit correction terms.
No derivative limit is inferred from a value envelope alone.
-/

open Set Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergOneSidedCurvatureDecay
noncomputable section

/-- The inverse-square correction converts the actual derivative into a monotone function. -/
theorem corrected_derivative_monotone {v a2 : ℝ → ℝ} {A C : ℝ} (hA : 0 < A)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (ha2 : ∀ y ∈ Ici A, -C / y ^ (2 : ℕ) ≤ a2 y) :
    MonotoneOn (fun y => v y - C / y) (Ici A) := by
  have hd (y : ℝ) (hy : y ∈ Ici A) :
      HasDerivAt (fun t => v t - C / t) (a2 y + C / y ^ (2 : ℕ)) y := by
    have h := (hv y hy).sub ((hasDerivAt_const y C).div (hasDerivAt_id y) (hA.trans_le hy).ne')
    apply h.congr_deriv
    simp only [id_eq, zero_mul, mul_one, zero_sub]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici A)
  · intro y hy; exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy; exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [(hd y (interior_subset hy)).deriv]
    have h := ha2 y (interior_subset hy)
    rw [neg_div] at h
    linarith

/-- Actual unit secants force derivative decay under a one-sided inverse-square curvature bound. -/
theorem derivative_tendsto_zero {u v a2 : ℝ → ℝ} {A C L : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hu : ∀ y ∈ Ici A, HasDerivAt u (v y) y)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (ha2 : ∀ y ∈ Ici A, -C / y ^ (2 : ℕ) ≤ a2 y)
    (hlim : Tendsto u atTop (𝓝 L)) : Tendsto v atTop (𝓝 0) := by
  have hmono := corrected_derivative_monotone hA hv ha2
  have hupper : ∀ᶠ y : ℝ in atTop, v y ≤ u (y + 1) - u y + C / y := by
    filter_upwards [eventually_ge_atTop A] with y hy
    have hs := (convex_Icc y (y + 1)).mul_sub_le_image_sub_of_le_deriv
      (f := u)
      (by intro s hs; exact (hu s (hy.trans hs.1)).continuousAt.continuousWithinAt)
      (by intro s hs
          exact (hu s (hy.trans (interior_subset hs).1)).differentiableAt.differentiableWithinAt)
      (C := v y - C / y)
      (by intro s hs
          have hss : s ∈ Icc y (y + 1) := interior_subset hs
          have hAs := hy.trans hss.1
          rw [(hu s hAs).deriv]
          have hm := hmono hy hAs hss.1
          have hc := div_nonneg hC (hA.trans_le hAs).le
          linarith)
      y (by constructor <;> linarith) (y + 1) (by constructor <;> linarith) (by linarith)
    nlinarith
  have hlower : ∀ᶠ y : ℝ in atTop, u y - u (y - 1) - C / (y - 1) ≤ v y := by
    filter_upwards [eventually_ge_atTop (A + 1)] with y hy
    have hAy : A ≤ y := by linarith
    have hprev : 0 < y - 1 := by linarith
    have hs := (convex_Icc (y - 1) y).image_sub_le_mul_sub_of_deriv_le
      (f := u)
      (by intro s hs; exact (hu s (show A ≤ s by linarith [hs.1])).continuousAt.continuousWithinAt)
      (by intro s hs
          have hss : s ∈ Icc (y - 1) y := interior_subset hs
          exact (hu s (show A ≤ s by linarith [hss.1])).differentiableAt.differentiableWithinAt)
      (C := v y - C / y + C / (y - 1))
      (by intro s hs
          have hss : s ∈ Icc (y - 1) y := interior_subset hs
          have hAs : A ≤ s := by linarith [hss.1]
          rw [(hu s hAs).deriv]
          have hm := hmono hAs hAy hss.2
          have hc := div_le_div_of_nonneg_left hC hprev hss.1
          linarith)
      (y - 1) (by constructor <;> linarith) y (by constructor <;> linarith) (by linarith)
    have hc := div_nonneg hC (hA.trans_le hAy).le
    nlinarith
  have hp : Tendsto (fun y : ℝ => y + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hm : Tendsto (fun y : ℝ => y - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1) tendsto_id
  have hcup : Tendsto (fun y : ℝ => C / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hclow : Tendsto (fun y : ℝ => C / (y - 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hm
  have hU : Tendsto (fun y => u (y + 1) - u y + C / y) atTop (𝓝 0) := by
    simpa only [sub_self, zero_add, Function.comp_apply] using ((hlim.comp hp).sub hlim).add hcup
  have hL : Tendsto (fun y => u y - u (y - 1) - C / (y - 1)) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_apply] using (hlim.sub (hlim.comp hm)).sub hclow
  exact hL.squeeze' hU hlower hupper

end
end GaloisForLFunctions.RHTower.SelbergOneSidedCurvatureDecay
