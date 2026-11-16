import GaloisForLFunctions.HTGeometry.ConstitutivePositiveEvenLaplaceEscape
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Strict real convexity of a positive Laplace source with nonreal zeros

The positive two-shell source has a strictly log-convex real transform,
strictly increasing with the absolute real argument. An explicit positive
curvature identity proves these properties alongside its existing off-axis
zero. Even these strict real inequalities do not locate complex zeros.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

open HTGeometry

/-- Real restriction of the positive symmetric shells at distances one and two. -/
def twoShellRealLaplace (a t : ℝ) : ℝ :=
  Real.cosh (2 * a) * Real.cosh t + Real.cosh a * Real.cosh (2 * t)

def twoShellRealLaplace₁ (a t : ℝ) : ℝ :=
  Real.cosh (2 * a) * Real.sinh t + 2 * Real.cosh a * Real.sinh (2 * t)

def twoShellRealLaplace₂ (a t : ℝ) : ℝ :=
  Real.cosh (2 * a) * Real.cosh t + 4 * Real.cosh a * Real.cosh (2 * t)

theorem twoShellRealLaplace_pos (a t : ℝ) : 0 < twoShellRealLaplace a t := by
  unfold twoShellRealLaplace
  positivity

/-- Identification with the actual complex Laplace source. -/
theorem ofReal_twoShellRealLaplace (a t : ℝ) :
    (twoShellRealLaplace a t : ℂ) = positiveEvenTwoShellLaplace a (t : ℂ) := by
  unfold twoShellRealLaplace positiveEvenTwoShellLaplace
  push_cast
  rfl

theorem hasDerivAt_twoShellRealLaplace (a t : ℝ) :
    HasDerivAt (twoShellRealLaplace a) (twoShellRealLaplace₁ a t) t := by
  have h := ((Real.hasDerivAt_cosh t).const_mul (Real.cosh (2 * a))).add
    (((Real.hasDerivAt_cosh (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)).const_mul (Real.cosh a))
  exact h.congr_deriv (by unfold twoShellRealLaplace₁; ring)

theorem hasDerivAt_twoShellRealLaplace₁ (a t : ℝ) :
    HasDerivAt (twoShellRealLaplace₁ a) (twoShellRealLaplace₂ a t) t := by
  have h := ((Real.hasDerivAt_sinh t).const_mul (Real.cosh (2 * a))).add
    (((Real.hasDerivAt_sinh (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)).const_mul (2 * Real.cosh a))
  exact h.congr_deriv (by unfold twoShellRealLaplace₂; ring)

/-- Exact positive numerator of the logarithmic curvature. -/
theorem twoShellRealLaplace_curvature (a t : ℝ) :
    twoShellRealLaplace a t * twoShellRealLaplace₂ a t -
        twoShellRealLaplace₁ a t ^ 2 =
      Real.cosh (2 * a) ^ 2 + 4 * Real.cosh a ^ 2 +
        Real.cosh (2 * a) * Real.cosh a / 2 *
          (Real.cosh (3 * t) + 9 * Real.cosh t) := by
  have h₃ : Real.cosh (3 * t) =
      Real.cosh t * Real.cosh (2 * t) + Real.sinh t * Real.sinh (2 * t) := by
    rw [show 3 * t = t + 2 * t by ring, Real.cosh_add]
  have h₁ : Real.cosh t =
      Real.cosh t * Real.cosh (2 * t) - Real.sinh t * Real.sinh (2 * t) := by
    have h := Real.cosh_sub (2 * t) t
    rw [show 2 * t - t = t by ring] at h
    linear_combination h
  unfold twoShellRealLaplace twoShellRealLaplace₁ twoShellRealLaplace₂
  linear_combination
    Real.cosh (2 * a) ^ 2 * Real.cosh_sq_sub_sinh_sq t +
    4 * Real.cosh a ^ 2 * Real.cosh_sq_sub_sinh_sq (2 * t) -
    (Real.cosh (2 * a) * Real.cosh a / 2) * h₃ -
    (9 * Real.cosh (2 * a) * Real.cosh a / 2) * h₁

theorem twoShellRealLaplace_curvature_pos (a t : ℝ) :
    0 < twoShellRealLaplace a t * twoShellRealLaplace₂ a t -
      twoShellRealLaplace₁ a t ^ 2 := by
  rw [twoShellRealLaplace_curvature]
  positivity

/-- Positivity is strict everywhere, so the real logarithm is strictly convex. -/
theorem strictConvexOn_log_twoShellRealLaplace (a : ℝ) :
    StrictConvexOn ℝ Set.univ (fun t => Real.log (twoShellRealLaplace a t)) := by
  have hd (t : ℝ) := (hasDerivAt_twoShellRealLaplace a t).log
    (twoShellRealLaplace_pos a t).ne'
  have he : deriv (fun t => Real.log (twoShellRealLaplace a t)) =
      fun t => twoShellRealLaplace₁ a t / twoShellRealLaplace a t :=
    funext fun t => (hd t).deriv
  apply strictConvexOn_of_deriv2_pos' convex_univ
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
  intro t _
  change 0 < deriv (deriv (fun t => Real.log (twoShellRealLaplace a t))) t
  rw [he]
  change 0 < deriv (twoShellRealLaplace₁ a / twoShellRealLaplace a) t
  rw [((hasDerivAt_twoShellRealLaplace₁ a t).div
    (hasDerivAt_twoShellRealLaplace a t) (twoShellRealLaplace_pos a t).ne').deriv]
  apply div_pos
  · nlinarith only [twoShellRealLaplace_curvature_pos a t]
  · exact sq_pos_of_pos (twoShellRealLaplace_pos a t)

/-- Absolute distance from the origin completely orders real transform values. -/
theorem twoShellRealLaplace_lt_iff (a s t : ℝ) :
    twoShellRealLaplace a s < twoShellRealLaplace a t ↔ |s| < |t| := by
  have hmono {x y : ℝ} (hxy : |x| ≤ |y|) :
      twoShellRealLaplace a x ≤ twoShellRealLaplace a y := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.mpr hxy) (Real.cosh_pos _).le
    · apply mul_le_mul_of_nonneg_left _ (Real.cosh_pos _).le
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using
        mul_le_mul_of_nonneg_left hxy (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · intro h
    exact lt_of_not_ge (fun hst => (not_le_of_gt h) (hmono hst))
  · intro h
    apply add_lt_add_of_lt_of_le
    · exact mul_lt_mul_of_pos_left (Real.cosh_lt_cosh.mpr h) (Real.cosh_pos _)
    · apply mul_le_mul_of_nonneg_left _ (Real.cosh_pos _).le
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using
        mul_le_mul_of_nonneg_left h.le (show (0 : ℝ) ≤ 2 by norm_num)

/-- The origin is the unique real minimum. -/
theorem twoShellRealLaplace_eq_at_zero_iff (a t : ℝ) :
    twoShellRealLaplace a t = twoShellRealLaplace a 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have hlt := (twoShellRealLaplace_lt_iff a 0 t).mpr (by simpa using abs_pos.mpr ht)
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · rintro rfl
    rfl

/-- Strict log-convexity of the real restriction coexists with an off-axis complex zero. -/
theorem twoShell_strictLogConvex_with_offAxisZero :
    StrictConvexOn ℝ Set.univ (fun t => Real.log (twoShellRealLaplace 1 t)) ∧
      positiveEvenTwoShellLaplace 1 ((1 : ℂ) + (Real.pi : ℂ) * Complex.I) = 0 :=
  ⟨strictConvexOn_log_twoShellRealLaplace 1, positiveEvenTwoShellLaplace_explicit_offAxis⟩

#print axioms twoShellRealLaplace_curvature
#print axioms strictConvexOn_log_twoShellRealLaplace
#print axioms twoShellRealLaplace_lt_iff
#print axioms twoShell_strictLogConvex_with_offAxisZero

end GaloisForLFunctions.HilbertMetric
