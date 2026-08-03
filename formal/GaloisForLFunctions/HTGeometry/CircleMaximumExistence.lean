import GaloisForLFunctions.HTGeometry.CircleMaximumCriticality
import GaloisForLFunctions.HTGeometry.MaximumTermWindowMoments

/-!
# The maximum-modulus point of a circle, and what it supplies

The Wiman--Valiron estimate is stated at a point of the circle where the modulus is largest.  Such a
point exists — the modulus is continuous and the circle is compact — and it automatically supplies
the three side conditions the estimate asks for: the value is at least the maximum term, the
logarithmic derivative is real there, and the normalised coefficients sum to a positive multiple of
a unit.

Nothing here is about power series in particular; it is the passage from "there is a maximum" to the
data a maximum carries.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ} {r : ℝ}

/-- **A maximum of the modulus on a circle.** -/
theorem exists_max_on_circle (ha : EntireCoeffs a) (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ = r ∧ ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ ‖coeffFun a z‖ := by
  have hcont : Continuous fun θ : ℝ => ‖coeffFun a (circleMap 0 r θ)‖ :=
    ((differentiable_coeffFun ha).continuous.comp (continuous_circleMap 0 r)).norm
  have hne : (Set.Icc (0 : ℝ) (2 * Real.pi)).Nonempty :=
    ⟨0, Set.left_mem_Icc.mpr (by positivity)⟩
  obtain ⟨θ₀, hθ₀mem, hθ₀max⟩ := isCompact_Icc.exists_isMaxOn hne hcont.continuousOn
  refine ⟨circleMap 0 r θ₀, ?_, ?_⟩
  · rw [norm_circleMap_zero, abs_of_pos hr]
  · intro θ
    obtain ⟨θ', hθ'mem, hθ'eq⟩ :=
      (periodic_circleMap 0 r).exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hθ'eq]
    exact hθ₀max ⟨hθ'mem.1, le_of_lt hθ'mem.2⟩

/-- At a maximum of the modulus on the circle the value dominates the maximum term. -/
theorem maxTerm_le_norm_of_max_on_circle (ha : EntireCoeffs a) (hr : 0 < r) {z : ℂ}
    (_hz : ‖z‖ = r) (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ ‖coeffFun a z‖) :
    maxTerm a r ≤ ‖coeffFun a z‖ := by
  refine ciSup_le fun n => ?_
  have hwin := sum_window_le_sqrt_card_mul_bound ha hr.le (norm_nonneg _) hmax {n}
  rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, Real.sqrt_one, one_mul] at hwin
  exact hwin

/-- **The direction of the normalised sum.**  A nonzero complex number is its modulus times a
unit. -/
theorem exists_unit_dir {W : ℂ} (hW : W ≠ 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ W = ((‖W‖ : ℝ) : ℂ) * u := by
  refine ⟨W / ((‖W‖ : ℝ) : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hW)]
    exact div_self (ne_of_gt (norm_pos_iff.mpr hW))
  · rw [mul_div_cancel₀]
    exact_mod_cast (norm_ne_zero_iff.mpr hW)

/-- **Criticality at a maximum of the modulus.**  A global maximum along the circle is a local
maximum of the squared modulus in the angular parameter, so the logarithmic derivative is real. -/
theorem im_mul_deriv_div_eq_zero_of_max_on_circle (ha : EntireCoeffs a) (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ = r) (hfz : coeffFun a z ≠ 0)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ ‖coeffFun a z‖) :
    (z * deriv (coeffFun a) z / coeffFun a z).im = 0 := by
  refine im_mul_deriv_div_eq_zero_of_isLocalMax (differentiable_coeffFun ha) hfz ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hpath : ∃ θ : ℝ, circlePath z t = circleMap 0 r θ := by
    have hw0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact absurd hz.symm (ne_of_gt hr)
    refine ⟨Complex.arg z + t, ?_⟩
    rw [circlePath, circleMap, zero_add, ← hz]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [← mul_assoc]
    congr 1
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  obtain ⟨θ, hθ⟩ := hpath
  have hle : ‖coeffFun a (circlePath z t)‖ ≤ ‖coeffFun a (circlePath z 0)‖ := by
    rw [hθ, circlePath_zero]
    exact hmax θ
  have hnn : (0 : ℝ) ≤ ‖coeffFun a (circlePath z t)‖ := norm_nonneg _
  exact pow_le_pow_left₀ hnn hle 2

end GaloisForLFunctions.HTGeometry
