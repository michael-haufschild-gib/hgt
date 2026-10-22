import GaloisForLFunctions.RHTower.Suzuki.SuzukiDslopeBoundaryLimit

noncomputable section

/-!
# `F_γ` is a Hardy function of the half-plane

Rotating by `w ↦ i w` carries the upper half-plane to the right half-plane, where the corpus's
analytic Hardy predicate lives.  The rotated `F_γ` satisfies all three of its clauses: holomorphy
transports along the rotation, and the line hypotheses come from the height-free Cauchy profile,
transported across the parametrisation `rayLine σ ξ = σ + 2πξ i` — whose `2π` rescales the mass by
`(2π)^{-1}` and turns the bound `2C²π` into `C²`.

Paley--Wiener therefore applies to `F_γ`, giving it a datum on the positive ray.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- `F_γ` rotated to the right half-plane. -/
def suzukiRotatedDslope (γ : ℂ) (w : ℂ) : ℂ := dslope suzukiHalfInner γ (I * w)

theorem suzukiRotatedDslope_rayLine (γ : ℂ) (σ ξ : ℝ) :
    suzukiRotatedDslope γ (rayLine σ ξ)
      = dslope suzukiHalfInner γ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I) := by
  rw [suzukiRotatedDslope, rayLine]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (ξ : ℂ)) * Complex.I_sq

theorem isHalfPlaneHardy_suzukiRotatedDslope (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) {C : ℝ} (hC1 : 1 ≤ C)
    (hCb : ∀ z : ℂ, 0 ≤ z.im → ‖dslope suzukiHalfInner γ z‖ ≤ C) :
    IsHalfPlaneHardy (suzukiRotatedDslope γ) (C ^ (2 : ℕ)) := by
  have hpi := Real.pi_pos
  have htwopi : (2 * Real.pi) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have him : (0 : ℝ) ≤ (I * w).im := by
      have : (I * w).im = w.re := by simp [Complex.mul_im]
      rw [this]
      exact le_of_lt hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hd := differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ him
    exact hd.comp w ((differentiableAt_id).const_mul I)
  · intro σ hσ
    have hbase := memLp_dslope_line hRH hγ hC1 hCb (le_of_lt hσ)
    have hint : Integrable
        (fun x : ℝ => ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)) volume :=
      (memLp_two_iff_integrable_sq_norm
        (continuous_dslope_line hRH hγ (le_of_lt hσ)).aestronglyMeasurable).mp hbase
    have hcomp : Integrable
        (fun ξ : ℝ => ‖dslope suzukiHalfInner γ
          (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)) volume := by
      have hfun : (fun ξ : ℝ => ‖dslope suzukiHalfInner γ
            (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ))
          = (fun x : ℝ => ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ))
            ∘ (fun ξ : ℝ => -(2 * Real.pi) * ξ) := by
        funext ξ
        congr 3
        push_cast
        ring
      rw [hfun]
      exact hint.comp_mul_left' (neg_ne_zero.mpr htwopi)
    refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hc : Continuous fun ξ : ℝ => suzukiRotatedDslope γ (rayLine σ ξ) := by
        have hcl : Continuous fun ξ : ℝ =>
            dslope suzukiHalfInner γ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I) := by
          have hbase := continuous_dslope_line hRH hγ (le_of_lt hσ)
          exact hbase.comp (by fun_prop)
        exact hcl.congr fun ξ => (suzukiRotatedDslope_rayLine γ σ ξ).symm
      exact hc
    · refine hcomp.congr ?_
      filter_upwards with ξ
      rw [suzukiRotatedDslope_rayLine]
  · intro σ hσ
    have hval : ∀ ξ : ℝ, ‖suzukiRotatedDslope γ (rayLine σ ξ)‖ ^ (2 : ℕ)
        = ‖dslope suzukiHalfInner γ
            (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ) := by
      intro ξ
      rw [suzukiRotatedDslope_rayLine]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hval)]
    have hchange : (∫ ξ : ℝ, ‖dslope suzukiHalfInner γ
          (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ))
        = |(-(2 * Real.pi))⁻¹| •
          ∫ x : ℝ, ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ) := by
      rw [← MeasureTheory.Measure.integral_comp_mul_left
        (fun x : ℝ => ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ))
        (-(2 * Real.pi))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show ‖dslope suzukiHalfInner γ
          (((-(2 * Real.pi * ξ) : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)
        = ‖dslope suzukiHalfInner γ
          (((-(2 * Real.pi) * ξ : ℝ) : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)
      congr 4
      ring
    rw [hchange]
    have hbnd := integral_norm_sq_dslope_line_le hRH hγ hC1 hCb (le_of_lt hσ)
    have habs : |(-(2 * Real.pi))⁻¹| = (2 * Real.pi)⁻¹ := by
      rw [abs_inv, abs_neg, abs_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)]
    rw [habs, smul_eq_mul]
    have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    calc (2 * Real.pi)⁻¹ * ∫ x : ℝ,
          ‖dslope suzukiHalfInner γ ((x : ℂ) + ((σ : ℝ) : ℂ) * I)‖ ^ (2 : ℕ)
        ≤ (2 * Real.pi)⁻¹ * (2 * C ^ (2 : ℕ) * Real.pi) := by
          exact mul_le_mul_of_nonneg_left hbnd (le_of_lt hinv)
      _ = C ^ (2 : ℕ) := by field_simp

end RHTower
