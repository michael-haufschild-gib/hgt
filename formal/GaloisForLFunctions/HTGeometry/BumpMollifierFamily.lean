import GaloisForLFunctions.HTGeometry.MollifierUniformApproximation

/-!
# A concrete mollifier family

The approximation results take a nonnegative continuous density of unit mass supported within `ε`
of the origin.  Normalised smooth bump functions supply such a family for every width, so the
uniform-approximation machinery can be instantiated without any further construction.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The smooth bump of outer radius `ε` centred at the origin. -/
noncomputable def widthBump {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : ℝ) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The normalised mollifier of width `ε`. -/
noncomputable def bumpMollifier {ε : ℝ} (hε : 0 < ε) : ℝ → ℝ :=
  (widthBump hε).normed volume

theorem continuous_bumpMollifier {ε : ℝ} (hε : 0 < ε) : Continuous (bumpMollifier hε) :=
  (widthBump hε).continuous_normed

theorem hasCompactSupport_bumpMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (bumpMollifier hε) :=
  (widthBump hε).hasCompactSupport_normed

theorem nonneg_bumpMollifier {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ bumpMollifier hε t :=
  (widthBump hε).nonneg_normed t

theorem integral_bumpMollifier {ε : ℝ} (hε : 0 < ε) : (∫ t, bumpMollifier hε t) = 1 :=
  (widthBump hε).integral_normed

theorem integrable_bumpMollifier {ε : ℝ} (hε : 0 < ε) : Integrable (bumpMollifier hε) :=
  (continuous_bumpMollifier hε).integrable_of_hasCompactSupport
    (hasCompactSupport_bumpMollifier hε)

/-- **The mollifier is supported within its width.** -/
theorem bumpMollifier_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε < |t|) :
    bumpMollifier hε t = 0 := by
  have hsupp : Function.support (bumpMollifier hε) = Metric.ball (0 : ℝ) ε :=
    (widthBump hε).support_normed_eq
  by_contra hne
  have hmem : t ∈ Function.support (bumpMollifier hε) := hne
  rw [hsupp, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  exact absurd hmem (not_lt.mpr ht.le)

/-- **The bump family instantiates the uniform approximation bound.**  For a profile with a uniform
modulus `M` at scale `ε`, mollifying by the width-`ε` bump moves it by at most `M`, uniformly. -/
theorem abs_sub_mollify_bump_le {u : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε) (hu : Continuous u)
    (hmod : ∀ y t : ℝ, |t| ≤ ε → |u y - u (y - t)| ≤ M) (x : ℝ) :
    |u x - mollify (bumpMollifier hε) u x| ≤ M :=
  abs_sub_mollify_le (continuous_bumpMollifier hε) hu (hasCompactSupport_bumpMollifier hε)
    (nonneg_bumpMollifier hε) (integrable_bumpMollifier hε) (integral_bumpMollifier hε)
    (fun _ ht => bumpMollifier_eq_zero hε ht) hmod x

/-- **The first-moment defect of the bump family is of order the width.** -/
theorem integral_abs_firstMomentKernel_bump_le {ε : ℝ} (hε : 0 < ε) :
    (∫ t, |firstMomentKernel (bumpMollifier hε) t|) ≤ ε :=
  integral_abs_firstMomentKernel_le (nonneg_bumpMollifier hε)
    (fun _ ht => bumpMollifier_eq_zero hε ht) (integrable_bumpMollifier hε)
    (integral_bumpMollifier hε)

end GaloisForLFunctions.HTGeometry
