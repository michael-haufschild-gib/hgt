import GaloisForLFunctions.HTGeometry.BohrAlmostPeriodic
import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative

/-!
# Boundedness is not recurrence

The recurrence hypothesis of the finite-phase law is not implied by boundedness and holomorphy on
the strip.  The function `1/(s+2)` is holomorphic and bounded by `1/2` on every vertical strip
contained in the right half plane, and on each vertical line it *tends to zero*.  By the vanishing
lemma an almost-periodic function with that limit is identically zero, so `1/(s+2)` is not almost
periodic on any line.

Its translate family is nevertheless normal for the compact-open topology — the classical Montel
argument for a bounded family.  What fails is the return property: uniform convergence on the whole
closed substrip.  That is the load-bearing hypothesis of the law, and it is strictly stronger than
compact-open normality.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- A bounded holomorphic function on the closed right half plane. -/
noncomputable def shiftedInverse (s : ℂ) : ℂ := (s + 2)⁻¹

theorem shiftedInverse_denom_norm_ge {s : ℂ} (hs : 0 ≤ s.re) : 2 ≤ ‖s + 2‖ := by
  have hre : (s + 2).re = s.re + 2 := by simp
  have h := Complex.abs_re_le_norm (s + 2)
  rw [hre, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re + 2)] at h
  linarith

theorem shiftedInverse_denom_ne_zero {s : ℂ} (hs : 0 ≤ s.re) : s + 2 ≠ 0 := by
  intro h
  have := shiftedInverse_denom_norm_ge hs
  rw [h, norm_zero] at this
  linarith

/-- The function is bounded by `1/2` on the closed right half plane. -/
theorem norm_shiftedInverse_le_half {s : ℂ} (hs : 0 ≤ s.re) : ‖shiftedInverse s‖ ≤ 1 / 2 := by
  rw [shiftedInverse, norm_inv]
  have h := shiftedInverse_denom_norm_ge hs
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

/-- It is holomorphic on every vertical strip inside the right half plane. -/
theorem differentiableOn_shiftedInverse {R : ℝ} (h : R ≤ σ) :
    DifferentiableOn ℂ shiftedInverse (verticalStrip σ R) := by
  intro z hz
  have hre : 0 ≤ z.re := by
    have := hz
    rw [verticalStrip, Set.mem_setOf_eq] at this
    have habs := abs_lt.mp this
    linarith [habs.1]
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((differentiable_id.add_const (2 : ℂ)).differentiableAt).inv
    (shiftedInverse_denom_ne_zero hre)

/-- On every vertical line in the right half plane it tends to zero. -/
theorem tendsto_shiftedInverse_line (_hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => shiftedInverse ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  have hnorm : Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I + 2).im‖
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖ := Complex.abs_im_le_norm _
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I + 2).im = t := by simp
    rwa [hval, Real.norm_eq_abs, abs_of_nonneg ht] at him
  have hinv := hnorm.inv_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hinv.congr fun t => ?_
  rw [shiftedInverse, norm_inv]
  rfl

/-- **Bounded and holomorphic, but not recurrent.**  The function is not Bohr almost periodic on any
vertical line in the right half plane. -/
theorem not_isBohrAlmostPeriodic_shiftedInverse_line (hσ : 0 ≤ σ) :
    ¬ HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => shiftedInverse ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  intro hap
  have hzero := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hap
    (tendsto_shiftedInverse_line hσ)
  have h0 := hzero 0
  rw [shiftedInverse] at h0
  have hne : ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I + 2) ≠ 0 := by
    refine shiftedInverse_denom_ne_zero ?_
    simp [hσ]
  exact (inv_ne_zero hne) h0

end GaloisForLFunctions
