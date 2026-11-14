import GaloisForLFunctions.HilbertMetric.Geometry.PlanarTendex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

end GaloisForLFunctions.HilbertMetric
