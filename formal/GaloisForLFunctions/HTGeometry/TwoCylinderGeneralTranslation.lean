import GaloisForLFunctions.HTGeometry.TwoCylinderTranslationAction

/-!
# A general translation acts on the two-cylinder field

The two structural translations of a double-sine frame are periods of one cylinder coordinate each,
so each of them moves only the other coordinate.  An arbitrary translation moves both: the
coefficient field dilates by the first coordinate's multiplier and the outer variable by the
second's.

That is what makes the external orbit of a defect live inside the two-cylinder field: every
translate of the source has its increments in the same base field, dilated by the translation.
-/

open Filter Set Topology Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance gtDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gtComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance gtComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

variable {l : Fin 2 → ℂ}

/-- The action of a general translation on the two-cylinder field: the coefficient field dilates by
the first coordinate's multiplier, the outer variable by the second's. -/
def twoCylTranslate {q0 q1 : ℂ} (hq0 : q0 ≠ 0) (hq1 : q1 ≠ 0) :
    RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  ((ratFuncScale (algebraMap ℂ (RatFunc ℂ) q1) (by simpa using hq1) :
      RatFunc (RatFunc ℂ) →ₐ[RatFunc ℂ] RatFunc (RatFunc ℂ)) :
        RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ)).comp (cylinderCoeffScale hq0)

theorem twoCylTranslate_apply {q0 q1 : ℂ} (hq0 : q0 ≠ 0) (hq1 : q1 ≠ 0)
    (y : RatFunc (RatFunc ℂ)) :
    twoCylTranslate hq0 hq1 y
      = ratFuncScale (algebraMap ℂ (RatFunc ℂ) q1) (by simpa using hq1)
        (cylinderCoeffScale hq0 y) := rfl

/-- **A general translation acts on the embedded two-cylinder field by dilating both
coordinates.** -/
theorem addTranslationMeroEquiv_twoCylinderEmbed_general (hl : LinearIndependent ℚ l) (tau : ℂ)
    (y : RatFunc (RatFunc ℂ)) :
    addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
      = twoCylinderEmbed hl
          (twoCylTranslate (q0 := Complex.exp (l 0 * tau)) (q1 := Complex.exp (l 1 * tau))
            (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) y) := by
  classical
  set q0 : ℂ := Complex.exp (l 0 * tau) with hq0def
  have hq0 : q0 ≠ 0 := Complex.exp_ne_zero _
  set q1 : ℂ := Complex.exp (l 1 * tau) with hq1def
  have hq1 : q1 ≠ 0 := Complex.exp_ne_zero _
  have hq1R : algebraMap ℂ (RatFunc ℂ) q1 ≠ 0 := by simpa using hq1
  set iota : RatFunc ℂ →+* meroField (Set.univ : Set ℂ) :=
    (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ)).toRingHom with hiota
  set u2 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 1) with hu2def
  have hcoeff : ∀ c : RatFunc ℂ,
      addTranslationMeroEquiv tau (iota c) = iota (ratFuncScale q0 hq0 c) := by
    intro c
    rw [hiota]
    show addTranslationMeroEquiv tau (cylinderEmbed hl 0 c)
      = cylinderEmbed hl 0 (ratFuncScale q0 hq0 c)
    exact addTranslationMeroEquiv_cylinderEmbed hl 0 tau c
  have hiotaS : iota (algebraMap ℂ (RatFunc ℂ) q1)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) q1 := by
    rw [hiota]
    exact (cylinderEmbed hl 0).commutes _
  have hpoly : ∀ p : Polynomial (RatFunc ℂ),
      addTranslationMeroEquiv tau (Polynomial.eval₂ iota u2 p)
        = Polynomial.eval₂ iota u2
          (polyScale (algebraMap ℂ (RatFunc ℂ) q1) (polyCoeffScale hq0 p)) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [Polynomial.eval₂_add, (addTranslationMeroEquiv tau).map_add, hp, hq, map_add,
          map_add, Polynomial.eval₂_add]
    | monomial n c =>
        rw [Polynomial.eval₂_monomial, map_mul, map_pow, hcoeff, hu2def,
          addTranslationMeroEquiv_physicalExponentialMero, polyCoeffScale_monomial,
          polyScale_eq_comp]
        simp only [Polynomial.monomial_comp]
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, hiotaS]
  refine RatFunc.induction_on
    (P := fun y => addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
      = twoCylinderEmbed hl (twoCylTranslate hq0 hq1 y)) y ?_
  intro p s _
  rw [twoCylTranslate_apply, cylinderCoeffScale_div, ratFuncScale_div, twoCylinderEmbed_div,
    twoCylinderEmbed_div, map_div₀, hpoly, hpoly]

end

end GaloisForLFunctions.HTGeometry
