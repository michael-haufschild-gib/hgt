import GaloisForLFunctions.HilbertMetric.Geometry.PlanarTendex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact release dynamics for the constant tidal tensor

The constant-tensor approximation in §4.2 of arXiv:2611.16083 has an explicit
flow: radial separation follows a hyperbolic cosine and tangential separation
a cosine. These functions solve the second-order equation with zero initial
velocity. The exact null-length identity retains all orders of time, unlike
the quadratic configuration jet.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric
open Real
open HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- Exact release from rest for tidal coefficient `exp(q)²`. -/
def constantTendexFlow (q : ℝ) (v : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (v.1 * cosh (sqrt 2 * exp q * t), v.2 * cos (exp q * t))

/-- Velocity of the exact constant-tensor release. -/
def constantTendexVelocity (q : ℝ) (v : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (v.1 * (sqrt 2 * exp q) * sinh (sqrt 2 * exp q * t),
   -v.2 * exp q * sin (exp q * t))

theorem constantTendexFlow_zero (q : ℝ) (v : ℝ × ℝ) :
    constantTendexFlow q v 0 = v := by
  simp [constantTendexFlow]

theorem constantTendexVelocity_zero (q : ℝ) (v : ℝ × ℝ) :
    constantTendexVelocity q v 0 = 0 := by
  simp [constantTendexVelocity]

/-- Differentiation gives the explicit velocity. -/
theorem constantTendexFlow_hasDerivAt (q : ℝ) (v : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (constantTendexFlow q v) (constantTendexVelocity q v t) t := by
  have hb : HasDerivAt (fun s : ℝ => sqrt 2 * exp q * s) (sqrt 2 * exp q) t := by
    simpa using (hasDerivAt_id t).const_mul (sqrt 2 * exp q)
  have ha : HasDerivAt (fun s : ℝ => exp q * s) (exp q) t := by
    simpa using (hasDerivAt_id t).const_mul (exp q)
  have h := (hb.cosh.const_mul v.1).prodMk (ha.cos.const_mul v.2)
  have hd : (v.1 * (sinh (sqrt 2 * exp q * t) * (sqrt 2 * exp q)),
      v.2 * (-sin (exp q * t) * exp q)) = constantTendexVelocity q v t := by
    apply Prod.ext <;> dsimp [constantTendexVelocity] <;> ring
  rw [hd] at h
  exact h

/-- The explicit flow satisfies the actual second-order tidal equation. -/
theorem constantTendexVelocity_hasDerivAt (q : ℝ) (v : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (constantTendexVelocity q v)
      (planarTendex (exp q ^ 2) (constantTendexFlow q v t)) t := by
  have hb : HasDerivAt (fun s : ℝ => sqrt 2 * exp q * s) (sqrt 2 * exp q) t := by
    simpa using (hasDerivAt_id t).const_mul (sqrt 2 * exp q)
  have ha : HasDerivAt (fun s : ℝ => exp q * s) (exp q) t := by
    simpa using (hasDerivAt_id t).const_mul (exp q)
  have h := (hb.sinh.const_mul (v.1 * (sqrt 2 * exp q))).prodMk
    (ha.sin.const_mul (-v.2 * exp q))
  have hs : sqrt 2 ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have hd : (v.1 * (sqrt 2 * exp q) *
      (cosh (sqrt 2 * exp q * t) * (sqrt 2 * exp q)),
      -v.2 * exp q * (cos (exp q * t) * exp q)) =
      planarTendex (exp q ^ 2) (constantTendexFlow q v t) := by
    apply Prod.ext <;> dsimp [planarTendex, constantTendexFlow]
    · linear_combination v.1 * exp q ^ 2 * cosh (sqrt 2 * exp q * t) * hs
    · ring
  rw [hd] at h
  exact h

/-- Exact all-time length of an initially null separation. -/
theorem constantTendexFlow_null_length (q a t : ℝ) :
    euclideanPairing (constantTendexFlow q (a, sqrt 2 * a) t)
      (constantTendexFlow q (a, sqrt 2 * a) t) =
        3 * a ^ 2 + a ^ 2 *
          (sinh (sqrt 2 * exp q * t) ^ 2 - 2 * sin (exp q * t) ^ 2) := by
  have hs : sqrt 2 ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have hh := cosh_sq_sub_sinh_sq (sqrt 2 * exp q * t)
  have hc := sin_sq_add_cos_sq (exp q * t)
  unfold euclideanPairing constantTendexFlow
  dsimp
  linear_combination a ^ 2 * hh + 2 * a ^ 2 * hc + a ^ 2 * cos (exp q * t) ^ 2 * hs

/-- Hyperbolic stretching strictly dominates the two transverse oscillatory contributions
except at zero time. -/
theorem tendex_null_length_gap (s : ℝ) :
    0 ≤ sinh (sqrt 2 * s) ^ 2 - 2 * sin s ^ 2 ∧
      (sinh (sqrt 2 * s) ^ 2 - 2 * sin s ^ 2 = 0 ↔ s = 0) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hx : sqrt 2 * s ≠ 0 := mul_ne_zero (by positivity) hs
  have hstrict : |sqrt 2 * s| < |sinh (sqrt 2 * s)| := by
    rw [abs_sinh]
    exact self_lt_sinh_iff.mpr (abs_pos.mpr hx)
  have hh := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hstrict
  simp only [sq_abs, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hh
  have hc := (sq_le_sq₀ (abs_nonneg (sin s)) (abs_nonneg s)).mpr abs_sin_le_abs
  simp only [sq_abs] at hc
  have hp : 0 < sinh (sqrt 2 * s) ^ 2 - 2 * sin s ^ 2 := by
    nlinarith only [hh, hc]
  exact ⟨hp.le, iff_of_false hp.ne' hs⟩

/-- Every initially null separation weakly lengthens under the exact constant-tensor flow. -/
theorem constantTendexFlow_null_length_ge (q a t : ℝ) :
    3 * a ^ 2 ≤ euclideanPairing (constantTendexFlow q (a, sqrt 2 * a) t)
      (constantTendexFlow q (a, sqrt 2 * a) t) := by
  rw [constantTendexFlow_null_length, mul_assoc (sqrt 2) (exp q) t]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) (tendex_null_length_gap _).1)

/-- Exact finite-time preservation of an initially null separation occurs only at
zero time or for the zero vector. -/
theorem constantTendexFlow_null_length_eq_iff (q a t : ℝ) :
    euclideanPairing (constantTendexFlow q (a, sqrt 2 * a) t)
      (constantTendexFlow q (a, sqrt 2 * a) t) = 3 * a ^ 2 ↔ a = 0 ∨ t = 0 := by
  rw [constantTendexFlow_null_length, mul_assoc (sqrt 2) (exp q) t,
    add_eq_left, mul_eq_zero, sq_eq_zero_iff, (tendex_null_length_gap _).2]
  simp only [mul_eq_zero, exp_ne_zero, false_or]

end GaloisForLFunctions.HilbertMetric
