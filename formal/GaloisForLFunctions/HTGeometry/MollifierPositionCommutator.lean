import Mathlib

/-!
# The position commutator of a mollifier

Convolution commutes with a translation-invariant operator but not with multiplication by the
coordinate.  Its exact defect is one more convolution, against the first-moment kernel
`k(s) = s * rho(s)`:

`(rho ⋆ (L · U)) (L) = L * (rho ⋆ U) (L) − (k ⋆ U) (L)`.

This is the commutator that lets a weak-domain equation be mollified and the limit taken, with no
derivative of the mollified object appearing.  It is proved here for a continuous compactly
supported mollifier against a continuous function, so every integral in sight converges.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Convolution of a compactly supported kernel against a continuous function. -/
noncomputable def mollify (ρ u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, ρ t * u (x - t)

/-- The first-moment kernel of a mollifier. -/
noncomputable def firstMomentKernel (ρ : ℝ → ℝ) (t : ℝ) : ℝ := t * ρ t

private theorem integrable_kernel_mul {ρ u : ℝ → ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (x : ℝ) : Integrable fun t => ρ t * u (x - t) := by
  have hcont : Continuous fun t : ℝ => ρ t * u (x - t) :=
    hρ.mul (hu.comp (continuous_const.sub continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  exact hcρ.mul_right

private theorem integrable_moment_mul {ρ u : ℝ → ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (x : ℝ) :
    Integrable fun t => firstMomentKernel ρ t * u (x - t) := by
  have hcont : Continuous fun t : ℝ => firstMomentKernel ρ t * u (x - t) := by
    unfold firstMomentKernel
    exact (continuous_id.mul hρ).mul (hu.comp (continuous_const.sub continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  have hk : HasCompactSupport (firstMomentKernel ρ) := by
    unfold firstMomentKernel
    exact hcρ.mul_left
  exact hk.mul_right

/-- **Mollifier position commutator.**  Mollifying the coordinate-multiplied function is the
coordinate times the mollification, minus the mollification against the first-moment kernel. -/
theorem mollify_position_eq (ρ u : ℝ → ℝ) (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (x : ℝ) :
    mollify ρ (fun y => y * u y) x = x * mollify ρ u x - mollify (firstMomentKernel ρ) u x := by
  have h1 := integrable_kernel_mul hρ hu hcρ x
  have h2 := integrable_moment_mul hρ hu hcρ x
  have hsplit : ∀ t : ℝ, ρ t * ((x - t) * u (x - t)) =
      x * (ρ t * u (x - t)) - firstMomentKernel ρ t * u (x - t) := by
    intro t
    unfold firstMomentKernel
    ring
  unfold mollify
  simp only [hsplit]
  rw [integral_sub (h1.const_mul x) h2, integral_const_mul]

/-- Mollification against the zero kernel vanishes. -/
theorem mollify_zero (u : ℝ → ℝ) (x : ℝ) : mollify (fun _ => 0) u x = 0 := by
  simp [mollify]

/-- Mollification is linear in the mollified function. -/
theorem mollify_add (ρ u v : ℝ → ℝ) (hρ : Continuous ρ) (hu : Continuous u) (hv : Continuous v)
    (hcρ : HasCompactSupport ρ) (x : ℝ) :
    mollify ρ (fun y => u y + v y) x = mollify ρ u x + mollify ρ v x := by
  have h1 := integrable_kernel_mul hρ hu hcρ x
  have h2 := integrable_kernel_mul hρ hv hcρ x
  unfold mollify
  simp only [mul_add]
  exact integral_add h1 h2

end GaloisForLFunctions.HTGeometry
