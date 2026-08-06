import GaloisForLFunctions.HTGeometry.TwoCylinderMeromorphicDifferential
import GaloisForLFunctions.HTGeometry.PeriodCotangentCylinderForm

/-!
# The double-sine increments inside the two-cylinder base field

The hypertranscendence criterion needs the translation increments of the source to be elements of
the base field `ℂ(u₁)(u₂)`, not merely of the meromorphic field.  Both increments of the
double-sine source are period cotangents, and each one lives in a single cylinder:

* the cotangent of the second period is a rational function of `u₂` with constant coefficients, so
  it is the coefficient extension of the one-variable cotangent model;
* the cotangent of the first period is a rational function of `u₁` alone, so it is the image of the
  coefficient field.

The missing link between the two presentations is that the two-cylinder embedding restricted to
constant-coefficient rational functions of the outer variable is the second cylinder's embedding.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance ibDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ibComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance ibComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

variable {l : Fin 2 → ℂ}

/-! ### Constant-coefficient elements go to the second cylinder -/

/-- **The two-cylinder embedding restricted to constant coefficients is the second cylinder.** -/
theorem twoCylinderEmbed_coeffExtend (hl : LinearIndependent ℚ l) (r : RatFunc ℂ) :
    twoCylinderEmbed hl (coeffExtend (K := RatFunc ℂ) r) = cylinderEmbed hl 1 r := by
  refine RatFunc.induction_on
    (P := fun r => twoCylinderEmbed hl (coeffExtend (K := RatFunc ℂ) r)
      = cylinderEmbed hl 1 r) r ?_
  intro p q hq
  have hcomp : ((cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
        meroField (Set.univ : Set ℂ)).toRingHom).comp (algebraMap ℂ (RatFunc ℂ))
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) := by
    ext c
    exact (cylinderEmbed hl 0).commutes c
  have hdiv : cylinderEmbed hl 1 (algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
      = cylinderEmbed hl 1 (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) /
        cylinderEmbed hl 1 (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) :=
    map_div₀ (cylinderEmbed hl 1) _ _
  rw [coeffExtend_div, twoCylinderEmbed_div, Polynomial.eval₂_map, Polynomial.eval₂_map, hcomp,
    hdiv, cylinderEmbed_polynomial, cylinderEmbed_polynomial, ← Polynomial.aeval_def,
    ← Polynomial.aeval_def]

/-! ### The two increments -/

/-- **The increment of the first direction, in the base field.**  The cotangent of the first period
is the image of the coefficient field of the two-cylinder model. -/
theorem periodCotMero_eq_twoCylinderEmbed_coeff (hl : LinearIndependent ℚ l) {w : ℂ}
    (hw : w ≠ 0) (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / w) :
    periodCotMero w
      = twoCylinderEmbed hl (algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
          (cotModel ((Real.pi : ℂ) / w * Complex.I))) := by
  rw [twoCylinderEmbed_coeff, periodCotMero_eq_cylinderEmbed hl 0 hw hl0]

/-- **The increment of the second direction, in the base field.**  The cotangent of the second
period is the coefficient extension of the one-variable cotangent model. -/
theorem periodCotMero_eq_twoCylinderEmbed_coeffExtend (hl : LinearIndependent ℚ l) {w : ℂ}
    (hw : w ≠ 0) (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / w) :
    periodCotMero w
      = twoCylinderEmbed hl (coeffExtend (K := RatFunc ℂ)
          (cotModel ((Real.pi : ℂ) / w * Complex.I))) := by
  rw [twoCylinderEmbed_coeffExtend, periodCotMero_eq_cylinderEmbed hl 1 hw hl1]

/-- The second increment, with the coefficient extension carried out on the model. -/
theorem periodCotMero_eq_twoCylinderEmbed_cotModel (hl : LinearIndependent ℚ l) {w : ℂ}
    (hw : w ≠ 0) (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / w) :
    periodCotMero w
      = twoCylinderEmbed hl
          (cotModel (algebraMap ℂ (RatFunc ℂ) ((Real.pi : ℂ) / w * Complex.I))) := by
  rw [← coeffExtend_cotModel, periodCotMero_eq_twoCylinderEmbed_coeffExtend hl hw hl1]

end

end GaloisForLFunctions.HTGeometry
