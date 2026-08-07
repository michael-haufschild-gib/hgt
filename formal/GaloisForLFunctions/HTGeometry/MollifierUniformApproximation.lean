import GaloisForLFunctions.HTGeometry.MollifierPositionCommutator

/-!
# Mollification approximates within the modulus of continuity

A unit-mass mollifier supported within `ε` of the origin averages a profile against shifts of size
at most `ε`.  Writing the difference as

`u(x) − (ρ * u)(x) = ∫ ρ(t) [u(x) − u(x−t)] dt`

and using that `ρ` is a probability density supported in `[−ε, ε]`, the difference is bounded by the
profile's modulus of continuity at scale `ε`.  So a profile with a uniform modulus is uniformly
approximated by its mollifications, at a rate set by that modulus alone.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The mollification kernel against a continuous profile is integrable. -/
theorem integrable_mollifyKernel {ρ u : ℝ → ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (x : ℝ) : Integrable fun t => ρ t * u (x - t) := by
  have hcont : Continuous fun t : ℝ => ρ t * u (x - t) :=
    hρ.mul (hu.comp (continuous_const.sub continuous_id))
  exact hcont.integrable_of_hasCompactSupport hcρ.mul_right

/-- Averaging a constant against a unit-mass density returns the constant. -/
theorem integral_density_mul_const {ρ : ℝ → ℝ}
    (hmass : (∫ t, ρ t) = 1) (c : ℝ) : (∫ t, ρ t * c) = c := by
  rw [MeasureTheory.integral_mul_const, hmass, one_mul]

/-- **Mollification approximates within the modulus of continuity.**  A unit-mass density supported
in `[−ε, ε]` moves a profile by at most its modulus at scale `ε`, uniformly in the base point. -/
theorem abs_sub_mollify_le {ρ u : ℝ → ℝ} {ε M : ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (hnn : ∀ t, 0 ≤ ρ t) (hint : Integrable ρ)
    (hmass : (∫ t, ρ t) = 1) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hmod : ∀ y t : ℝ, |t| ≤ ε → |u y - u (y - t)| ≤ M) (x : ℝ) :
    |u x - mollify ρ u x| ≤ M := by
  have hik : Integrable fun t => ρ t * u (x - t) := integrable_mollifyKernel hρ hu hcρ x
  have hconst : Integrable fun t => ρ t * u x := hint.mul_const (u x)
  have hsplit : (∫ t, ρ t * (u x - u (x - t)))
      = (∫ t, ρ t * u x) - ∫ t, ρ t * u (x - t) := by
    rw [← MeasureTheory.integral_sub hconst hik]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * (u x - u (x - t)) = ρ t * u x - ρ t * u (x - t)
    ring
  have hrw : u x - mollify ρ u x = ∫ t, ρ t * (u x - u (x - t)) := by
    rw [hsplit, integral_density_mul_const hmass (u x)]
    rfl
  have hptwise : ∀ t : ℝ, ‖ρ t * (u x - u (x - t))‖ ≤ ρ t * M := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn t)]
    rcases le_or_gt |t| ε with ht | ht
    · exact mul_le_mul_of_nonneg_left (hmod x t ht) (hnn t)
    · rw [hsupp t ht]
      simp
  have hdom : Integrable fun t => ρ t * M := hint.mul_const M
  have hsub : Integrable fun t => ρ t * (u x - u (x - t)) := by
    refine (hconst.sub hik).congr (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * u x - ρ t * u (x - t) = ρ t * (u x - u (x - t))
    ring
  have hbound : ‖∫ t, ρ t * (u x - u (x - t))‖ ≤ ∫ t, ρ t * M := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    exact MeasureTheory.integral_mono hsub.norm hdom hptwise
  rw [hrw, ← Real.norm_eq_abs]
  refine le_trans hbound ?_
  rw [integral_density_mul_const hmass M]

end GaloisForLFunctions.HTGeometry
