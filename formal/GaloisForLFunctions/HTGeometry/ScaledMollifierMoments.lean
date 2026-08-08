import GaloisForLFunctions.HTGeometry.MollifierPositionCommutator

/-!
# Moments of a scaled mollifier

For `ρ_ε(t) = ε⁻¹ ρ(t/ε)` the first-moment kernel is `k_ε(t) = (t/ε) ρ(t/ε)`, so it is the *same*
profile read at scale `ε`.  Two consequences, which are the card's `(20)`:

* its mass scales, `‖k_ε‖₁ = ε ‖k₁‖₁`, so it vanishes as the mollifier concentrates;
* its derivative's mass does **not**, `‖k_ε′‖₁ = ‖k₁′‖₁`, because the `ε⁻¹` from differentiating and
  the `ε` from the substitution cancel.

That pairing — a vanishing zero-order defect against a bounded first-order one — is what makes the
mollified equation converge without losing the derivative term.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The mollifier `ρ` read at scale `ε`. -/
noncomputable def scaledMollifier (ρ : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ := ε⁻¹ * ρ (t / ε)

/-- The derivative of the first-moment kernel `u ↦ u ρ(u)`. -/
noncomputable def firstMomentDeriv (ρ ρ' : ℝ → ℝ) (u : ℝ) : ℝ := ρ u + u * ρ' u

theorem integral_scaledMollifier {ρ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    (∫ t, scaledMollifier ρ ε t) = ∫ u, ρ u := by
  unfold scaledMollifier
  rw [integral_const_mul, Measure.integral_comp_div ρ ε, abs_of_pos hε, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hε.ne', one_mul]

theorem firstMomentKernel_scaled {ρ : ℝ → ℝ} {ε : ℝ} (t : ℝ) :
    firstMomentKernel (scaledMollifier ρ ε) t = firstMomentKernel ρ (t / ε) := by
  rw [firstMomentKernel, firstMomentKernel, scaledMollifier, ← mul_assoc]
  congr 1

/-- **`(20)`, mass half.**  The first moment of a scaled mollifier is linear in the scale. -/
theorem integral_abs_firstMomentKernel_scaled {ρ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    (∫ t, |firstMomentKernel (scaledMollifier ρ ε) t|)
      = ε * ∫ u, |firstMomentKernel ρ u| := by
  have hrw : (fun t => |firstMomentKernel (scaledMollifier ρ ε) t|)
      = fun t => |firstMomentKernel ρ (t / ε)| := by
    funext t
    rw [firstMomentKernel_scaled]
  rw [hrw, Measure.integral_comp_div (fun u => |firstMomentKernel ρ u|) ε, abs_of_pos hε,
    smul_eq_mul]

theorem hasDerivAt_firstMomentKernel {ρ ρ' : ℝ → ℝ} (hρ : ∀ u, HasDerivAt ρ (ρ' u) u) (u : ℝ) :
    HasDerivAt (firstMomentKernel ρ) (firstMomentDeriv ρ ρ' u) u := by
  have hid : HasDerivAt (fun u : ℝ => u) 1 u := hasDerivAt_id u
  have hmul := hid.mul (hρ u)
  refine hmul.congr_deriv ?_
  rw [firstMomentDeriv]
  ring

theorem hasDerivAt_firstMomentKernel_scaled {ρ ρ' : ℝ → ℝ} {ε : ℝ}
    (hρ : ∀ u, HasDerivAt ρ (ρ' u) u) (t : ℝ) :
    HasDerivAt (firstMomentKernel (scaledMollifier ρ ε))
      (ε⁻¹ * firstMomentDeriv ρ ρ' (t / ε)) t := by
  have hfun : firstMomentKernel (scaledMollifier ρ ε) = fun t => firstMomentKernel ρ (t / ε) := by
    funext s
    exact firstMomentKernel_scaled s
  rw [hfun]
  have hb : HasDerivAt (fun t : ℝ => t / ε) ε⁻¹ t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const ε⁻¹
  have hcomp0 : HasDerivAt (firstMomentKernel ρ ∘ fun t : ℝ => t / ε)
      (firstMomentDeriv ρ ρ' (t / ε) * ε⁻¹) t :=
    (hasDerivAt_firstMomentKernel hρ (t / ε)).comp t hb
  have hcomp : HasDerivAt (fun t : ℝ => firstMomentKernel ρ (t / ε))
      (firstMomentDeriv ρ ρ' (t / ε) * ε⁻¹) t := hcomp0
  refine hcomp.congr_deriv ?_
  ring

/-- **`(20)`, derivative half.**  The mass of the derivative of the first-moment kernel is scale
invariant: the `ε⁻¹` from differentiating cancels the `ε` from the substitution. -/
theorem integral_abs_firstMomentDeriv_scaled {ρ ρ' : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    (∫ t, |ε⁻¹ * firstMomentDeriv ρ ρ' (t / ε)|)
      = ∫ u, |firstMomentDeriv ρ ρ' u| := by
  have hrw : (fun t => |ε⁻¹ * firstMomentDeriv ρ ρ' (t / ε)|)
      = fun t => ε⁻¹ * |firstMomentDeriv ρ ρ' (t / ε)| := by
    funext t
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
  rw [hrw, integral_const_mul, Measure.integral_comp_div (fun u => |firstMomentDeriv ρ ρ' u|) ε,
    abs_of_pos hε, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]

end GaloisForLFunctions.HTGeometry
