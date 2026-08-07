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

/-! ## The commutator defect is of order the mollifier width

Multiplication by the coordinate is the only operation that fails to commute with mollification,
and its defect is mollification against the first-moment kernel.  For a mollifier of unit mass
supported within `ε` of the origin that kernel has `L¹` mass at most `ε`, so the defect vanishes
linearly in the width.  This is the quantitative statement a squeeze argument consumes.
-/

/-- **The first-moment kernel is of order the width.**  A unit-mass mollifier supported in
`[−ε, ε]` has first-moment kernel of `L¹` mass at most `ε`. -/
theorem integral_abs_firstMomentKernel_le {ρ : ℝ → ℝ} {ε : ℝ}
    (hnn : ∀ t, 0 ≤ ρ t) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hint : Integrable ρ) (hmass : (∫ t, ρ t) = 1) :
    (∫ t, |firstMomentKernel ρ t|) ≤ ε := by
  have hpt : ∀ t : ℝ, |firstMomentKernel ρ t| ≤ ε * ρ t := by
    intro t
    unfold firstMomentKernel
    rw [abs_mul, abs_of_nonneg (hnn t)]
    rcases le_or_gt |t| ε with ht | ht
    · exact mul_le_mul_of_nonneg_right ht (hnn t)
    · rw [hsupp t ht]
      simp
  have hdom : Integrable fun t => ε * ρ t := hint.const_mul ε
  have hmeas : AEStronglyMeasurable (fun t => |firstMomentKernel ρ t|) volume := by
    unfold firstMomentKernel
    exact (aestronglyMeasurable_id.mul hint.aestronglyMeasurable).norm
  have hIint : Integrable fun t => |firstMomentKernel ρ t| := by
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt t
  have hmono : (∫ t, |firstMomentKernel ρ t|) ≤ ∫ t, ε * ρ t :=
    integral_mono hIint hdom hpt
  rwa [integral_const_mul, hmass, mul_one] at hmono

end GaloisForLFunctions.HTGeometry
