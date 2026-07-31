/-
# Arithmetic fibers of the square-root quadratic cloud

The quadratic osculating model of Bourgain's square-root curve is an affine
copy of the discrete parabola.  Its first two coordinates recover the two
integer moments of a triple.  Consequently, coordinatewise near-pairs at the
natural scales are actual parabola-fiber pairs.
-/
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticModel
import GaloisForLFunctions.RHTower.BourgainTripleNearPerturbation
import GaloisForLFunctions.RHTower.BourgainParabolaFiberSubpower

open scoped BigOperators

namespace RHTower

noncomputable section

/-- First derivative of the square-root curve at the parameter `a²`. -/
def bourgainSquareRootLinearJet (a : ℝ) : BourgainPhaseSpace :=
  ![1, 2 * a ^ (2 : ℕ), 3 * a / 2, 1 / (2 * a)]

/-- Half of the second derivative at the parameter `a²`. -/
def bourgainSquareRootQuadraticJet (a : ℝ) : BourgainPhaseSpace :=
  ![0, 1, 3 / (8 * a), -(1 / (8 * a ^ (3 : ℕ)))]

/-- Vector-valued quadratic osculating model at the base parameter `a²`. -/
def bourgainSquareRootQuadraticCurveModel
    (a s : ℝ) : BourgainPhaseSpace :=
  bourgainSquareRootCurve (a ^ (2 : ℕ)) +
    s • bourgainSquareRootLinearJet a +
    s ^ (2 : ℕ) • bourgainSquareRootQuadraticJet a

/-- Quadratic model sampled at the local integer points `n/D`. -/
def bourgainSquareRootQuadraticSample
    {H : ℕ} (a D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  bourgainSquareRootQuadraticCurveModel a
    ((bourgainIndex n : ℝ) / D)

@[simp] theorem bourgainSquareRootQuadraticCurveModel_zero
    (a s : ℝ) :
    bourgainSquareRootQuadraticCurveModel a s 0 =
      a ^ (2 : ℕ) + s := by
  simp [bourgainSquareRootQuadraticCurveModel,
    bourgainSquareRootCurve, bourgainSquareRootLinearJet,
    bourgainSquareRootQuadraticJet]

@[simp] theorem bourgainSquareRootQuadraticCurveModel_one
    (a s : ℝ) :
    bourgainSquareRootQuadraticCurveModel a s 1 =
      (a ^ (2 : ℕ)) ^ (2 : ℕ) +
        2 * a ^ (2 : ℕ) * s + s ^ (2 : ℕ) := by
  simp [bourgainSquareRootQuadraticCurveModel,
    bourgainSquareRootCurve, bourgainSquareRootLinearJet,
    bourgainSquareRootQuadraticJet]
  ring

/-- The scalar quadratic phase is the dot product with the vector-valued
osculating model. -/
theorem bourgainDot_quadraticCurveModel
    (a s : ℝ) (x : BourgainPhaseSpace) :
    bourgainDot x (bourgainSquareRootQuadraticCurveModel a s) =
      bourgainSquareRootQuadraticLocalPhase a x s := by
  simp [bourgainDot, bourgainSquareRootQuadraticCurveModel,
    bourgainSquareRootQuadraticLocalPhase,
    bourgainSquareRootLinearPhaseCoordinate,
    bourgainSquareRootQuadraticPhaseCoordinate,
    bourgainSquareRootCurvePhase,
    bourgainSquareRootCurve, bourgainSquareRootLinearJet,
    bourgainSquareRootQuadraticJet, Fin.sum_univ_four]
  ring

/-- Coordinate zero of the sampled triple cloud records `Σn/D`. -/
theorem bourgainTripleCloud_quadraticSample_zero
    {H : ℕ} (a D : ℝ) (h : Fin 3 → Fin H) :
    bourgainTripleCloud
        (bourgainSquareRootQuadraticSample a D) h 0 =
      3 * a ^ (2 : ℕ) +
        ((bourgainParabolaTripleMoment h).1 : ℝ) / D := by
  simp [bourgainTripleCloud, bourgainSquareRootQuadraticSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  ring

/-- Coordinate one records the affine first moment and quadratic second
moment of the sampled triple. -/
theorem bourgainTripleCloud_quadraticSample_one
    {H : ℕ} (a D : ℝ) (h : Fin 3 → Fin H) :
    bourgainTripleCloud
        (bourgainSquareRootQuadraticSample a D) h 1 =
      3 * (a ^ (2 : ℕ)) ^ (2 : ℕ) +
        2 * a ^ (2 : ℕ) *
          (((bourgainParabolaTripleMoment h).1 : ℝ) / D) +
        ((bourgainParabolaTripleMoment h).2 : ℝ) /
          D ^ (2 : ℕ) := by
  simp [bourgainTripleCloud, bourgainSquareRootQuadraticSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  field_simp
  ring

/-- An integer is determined by a scaled `1/2`-near condition once the
physical scale is at least half the denominator. -/
theorem nat_eq_of_scaled_div_near
    {m n : ℕ} {D Y : ℝ}
    (hD : 0 < D) (hscale : D ≤ 2 * Y)
    (hnear :
      |Y * ((m : ℝ) / D - (n : ℝ) / D)| < 1 / 2) :
    m = n := by
  have hratio : 1 / 2 ≤ Y / D := by
    rw [le_div_iff₀ hD]
    linarith
  have hratio0 : 0 ≤ Y / D := by linarith
  have hscaled :
      (Y / D) * |(m : ℝ) - (n : ℝ)| < 1 / 2 := by
    rw [show
        Y * ((m : ℝ) / D - (n : ℝ) / D) =
          (Y / D) * ((m : ℝ) - (n : ℝ)) by
      field_simp] at hnear
    simpa [abs_mul, abs_of_nonneg hratio0] using hnear
  have habs : |(m : ℝ) - (n : ℝ)| < 1 := by
    nlinarith [abs_nonneg ((m : ℝ) - (n : ℝ))]
  rw [abs_lt] at habs
  have hmn : m < n + 1 := by
    exact_mod_cast (show (m : ℝ) < (n : ℝ) + 1 by linarith [habs.2])
  have hnm : n < m + 1 := by
    exact_mod_cast (show (n : ℝ) < (m : ℝ) + 1 by linarith [habs.1])
  omega

/-- At natural linear and quadratic scales, a near pair of quadratic triple
cloud points belongs to one exact `(Σn,Σn²)` fiber. -/
theorem bourgainParabolaTripleMoment_eq_of_quadraticSample_near
    {H : ℕ} {a D : ℝ} (hD : 0 < D)
    {Y : BourgainPhaseSpace}
    (hY0 : D ≤ 2 * Y 0)
    (hY1 : D ^ (2 : ℕ) ≤ 2 * Y 1)
    {h h' : Fin 3 → Fin H}
    (hnear :
      BourgainScaledNear Y
        (bourgainTripleCloud
          (bourgainSquareRootQuadraticSample a D) h)
        (bourgainTripleCloud
          (bourgainSquareRootQuadraticSample a D) h')) :
    bourgainParabolaTripleMoment h =
      bourgainParabolaTripleMoment h' := by
  apply Prod.ext
  · apply nat_eq_of_scaled_div_near hD hY0
    have hzero := hnear (0 : Fin 4)
    rw [bourgainTripleCloud_quadraticSample_zero,
      bourgainTripleCloud_quadraticSample_zero] at hzero
    convert hzero using 1 ; ring
  · have hfirst :
        (bourgainParabolaTripleMoment h).1 =
          (bourgainParabolaTripleMoment h').1 := by
      apply nat_eq_of_scaled_div_near hD hY0
      have hzero := hnear (0 : Fin 4)
      rw [bourgainTripleCloud_quadraticSample_zero,
        bourgainTripleCloud_quadraticSample_zero] at hzero
      convert hzero using 1 ; ring
    apply nat_eq_of_scaled_div_near (sq_pos_of_pos hD) hY1
    have hone := hnear (1 : Fin 4)
    rw [bourgainTripleCloud_quadraticSample_one,
      bourgainTripleCloud_quadraticSample_one, hfirst] at hone
    convert hone using 1 ; ring

end

end RHTower
