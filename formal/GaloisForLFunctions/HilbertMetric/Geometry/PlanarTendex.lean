import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Planar tidal null geometry

The planar point-mass tensor in arXiv:2611.16083 has radial and tangential
entries `2 k` and `-k`. In its orthonormal polar frame its null geometry is
the existing Cartan split form after rescaling the radial coordinate by `√2`.
The explicit logarithmic spiral has null tangent, nonzero acceleration,
and an injective radius parameter.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric

open Real
open HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- Point-mass tidal action in an orthonormal polar frame. -/
def planarTendex (k : ℝ) (v : ℝ × ℝ) : ℝ × ℝ := (2 * k * v.1, -k * v.2)

/-- Tidal bilinear form in the same frame. -/
def planarTendexForm (k : ℝ) (v w : ℝ × ℝ) : ℝ :=
  euclideanPairing v (planarTendex k w)

/-- The tidal form is a rescaled pullback of the Cartan Lorentz form. -/
theorem planarTendexForm_split (k : ℝ) (v w : ℝ × ℝ) :
    planarTendexForm k v w = k * splitForm
      (sqrt 2 * v.1, v.2) (sqrt 2 * w.1, w.2) := by
  have hs : sqrt 2 ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  unfold planarTendexForm planarTendex euclideanPairing splitForm
  dsimp
  linear_combination -k * v.1 * w.1 * hs

/-- Null directions are the two lines of slope `±√2`, including the zero vector. -/
theorem planarTendexForm_null_iff (q : ℝ) (v : ℝ × ℝ) :
    planarTendexForm (exp q) v v = 0 ↔
      v.2 = sqrt 2 * v.1 ∨ v.2 = -(sqrt 2 * v.1) := by
  have hs : sqrt 2 ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have he : planarTendexForm (exp q) v v =
      exp q * ((sqrt 2 * v.1) ^ 2 - v.2 ^ 2) := by
    unfold planarTendexForm planarTendex euclideanPairing
    dsimp
    linear_combination -exp q * v.1 ^ 2 * hs
  rw [he, mul_eq_zero]
  simp only [exp_ne_zero, false_or, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by linarith)

/-- Nullity does not annihilate the tidal acceleration. -/
theorem planarTendex_null_acceleration_energy (k a : ℝ) :
    euclideanPairing (planarTendex k (a, sqrt 2 * a))
      (planarTendex k (a, sqrt 2 * a)) = 6 * k ^ 2 * a ^ 2 := by
  have hs : sqrt 2 ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  unfold planarTendex euclideanPairing
  dsimp
  linear_combination k ^ 2 * a ^ 2 * hs

/-- Radial and tangential coordinates of a Cartesian vector. -/
def tendexPolarCoordinates (theta : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (cos theta * v.1 + sin theta * v.2, -sin theta * v.1 + cos theta * v.2)

/-- A logarithmic spiral with the paper's positive null slope. -/
def tendexNullSpiral (theta₀ u : ℝ) : ℝ × ℝ :=
  (exp u * cos (theta₀ + sqrt 2 * u), exp u * sin (theta₀ + sqrt 2 * u))

/-- Cartesian velocity of the logarithmic spiral. -/
def tendexNullSpiralVelocity (theta₀ u : ℝ) : ℝ × ℝ :=
  (exp u * (cos (theta₀ + sqrt 2 * u) - sqrt 2 * sin (theta₀ + sqrt 2 * u)),
   exp u * (sin (theta₀ + sqrt 2 * u) + sqrt 2 * cos (theta₀ + sqrt 2 * u)))

/-- The explicit spiral has the claimed derivative in the Cartesian plane. -/
theorem tendexNullSpiral_hasDerivAt (theta₀ u : ℝ) :
    HasDerivAt (tendexNullSpiral theta₀) (tendexNullSpiralVelocity theta₀ u) u := by
  have ht : HasDerivAt (fun s : ℝ => theta₀ + sqrt 2 * s) (sqrt 2) u := by
    simpa using ((hasDerivAt_id u).const_mul (sqrt 2)).const_add theta₀
  have h := ((hasDerivAt_exp u).mul ht.cos).prodMk ((hasDerivAt_exp u).mul ht.sin)
  have hd :
      (exp u * cos (theta₀ + sqrt 2 * u) +
          exp u * (-sin (theta₀ + sqrt 2 * u) * sqrt 2),
       exp u * sin (theta₀ + sqrt 2 * u) +
          exp u * (cos (theta₀ + sqrt 2 * u) * sqrt 2)) =
        tendexNullSpiralVelocity theta₀ u := by
    apply Prod.ext <;> dsimp [tendexNullSpiralVelocity] <;> ring
  rw [hd] at h
  exact h

/-- Polar components of the spiral tangent have the fixed null ratio `√2`. -/
theorem tendexNullSpiralVelocity_polar (theta₀ u : ℝ) :
    tendexPolarCoordinates (theta₀ + sqrt 2 * u) (tendexNullSpiralVelocity theta₀ u) =
      (exp u, sqrt 2 * exp u) := by
  have h := sin_sq_add_cos_sq (theta₀ + sqrt 2 * u)
  apply Prod.ext <;>
    simp only [tendexPolarCoordinates, tendexNullSpiralVelocity]
  · linear_combination exp u * h
  · linear_combination sqrt 2 * exp u * h

/-- Every tangent of the spiral is null for the point-mass tidal metric. -/
theorem tendexNullSpiral_null (q theta₀ u : ℝ) :
    planarTendexForm (exp q)
      (tendexPolarCoordinates (theta₀ + sqrt 2 * u) (tendexNullSpiralVelocity theta₀ u))
      (tendexPolarCoordinates (theta₀ + sqrt 2 * u) (tendexNullSpiralVelocity theta₀ u)) = 0 := by
  rw [tendexNullSpiralVelocity_polar, planarTendexForm_null_iff]
  exact Or.inl rfl

/-- Squared radius of the null spiral. -/
theorem tendexNullSpiral_radius_sq (theta₀ u : ℝ) :
    euclideanPairing (tendexNullSpiral theta₀ u) (tendexNullSpiral theta₀ u) =
      exp u ^ 2 := by
  have h := sin_sq_add_cos_sq (theta₀ + sqrt 2 * u)
  unfold tendexNullSpiral euclideanPairing
  dsimp
  linear_combination exp u ^ 2 * h

/-- No two parameter values on a null spiral meet; in particular it cannot close. -/
theorem tendexNullSpiral_injective (theta₀ : ℝ) : Function.Injective (tendexNullSpiral theta₀) := by
  intro u v huv
  have h := congrArg (fun z => euclideanPairing z z) huv
  rw [tendexNullSpiral_radius_sq, tendexNullSpiral_radius_sq] at h
  exact exp_injective ((sq_eq_sq₀ (exp_nonneg u) (exp_nonneg v)).mp h)

end GaloisForLFunctions.HilbertMetric

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HilbertMetric.planarTendexForm_split
#print axioms GaloisForLFunctions.HilbertMetric.planarTendexForm_null_iff
#print axioms GaloisForLFunctions.HilbertMetric.planarTendex_null_acceleration_energy
#print axioms GaloisForLFunctions.HilbertMetric.tendexNullSpiral_hasDerivAt
#print axioms GaloisForLFunctions.HilbertMetric.tendexNullSpiralVelocity_polar
#print axioms GaloisForLFunctions.HilbertMetric.tendexNullSpiral_null
#print axioms GaloisForLFunctions.HilbertMetric.tendexNullSpiral_radius_sq
#print axioms GaloisForLFunctions.HilbertMetric.tendexNullSpiral_injective
-- END PAPER AXIOM AUDIT
