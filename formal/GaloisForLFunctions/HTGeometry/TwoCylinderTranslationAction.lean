import GaloisForLFunctions.HTGeometry.CotangentMeromorphicIdentification

/-!
# The two translation directions on the two-cylinder function field

A translation of the complex plane acts on the embedded two-cylinder field `ℂ(u₁)(u₂)` by dilating
both coordinates.  When the translation is a period of the second coordinate only the first
coordinate moves, and the action is by scaling the coefficient field.  This is the companion of the
dilation of the outer variable, and together the two cover the two period directions of a
double-sine frame.
-/

open Filter Set Topology Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section


variable {K : Type*} [Field K]

theorem ratFuncScale_inv_scale (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncScale q hq (ratFuncScale q⁻¹ (inv_ne_zero hq) f) = f := by
  refine RatFunc.induction_on
    (P := fun f => ratFuncScale q hq (ratFuncScale q⁻¹ (inv_ne_zero hq) f) = f) f ?_
  intro p s _
  rw [ratFuncScale_div, ratFuncScale_div, polyScale_polyScale, polyScale_polyScale,
    mul_inv_cancel₀ hq, polyScale_one, polyScale_one]

/-- The dilation `X ↦ q X` of `K(X)` as a ring automorphism. -/
def ratFuncScaleEquiv (q : K) (hq : q ≠ 0) : RatFunc K ≃+* RatFunc K where
  toFun := ratFuncScale q hq
  invFun := ratFuncScale q⁻¹ (inv_ne_zero hq)
  left_inv := ratFuncScale_scale_inv q hq
  right_inv := ratFuncScale_inv_scale q hq
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] theorem ratFuncScaleEquiv_apply (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncScaleEquiv q hq f = ratFuncScale q hq f := rfl


local instance tcDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance tcComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance tcComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

variable {l : Fin 2 → ℂ}

/-- Scaling the coefficient field of the two-cylinder function field: the dilation of the first
cylinder coordinate, acting on `ℂ(u₁)[u₂]` through the coefficients. -/
def polyCoeffScale {q : ℂ} (hq : q ≠ 0) :
    Polynomial (RatFunc ℂ) →+* Polynomial (RatFunc ℂ) :=
  Polynomial.mapRingHom ((ratFuncScale q hq : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ) : RatFunc ℂ →+* RatFunc ℂ)

theorem polyCoeffScale_injective {q : ℂ} (hq : q ≠ 0) :
    Function.Injective (polyCoeffScale hq) :=
  Polynomial.map_injective _ (RingHom.injective _)

@[simp] theorem polyCoeffScale_monomial {q : ℂ} (hq : q ≠ 0) (n : ℕ) (c : RatFunc ℂ) :
    polyCoeffScale hq (Polynomial.monomial n c)
      = Polynomial.monomial n (ratFuncScale q hq c) := by
  simp [polyCoeffScale]

/-- The dilation of the first cylinder coordinate as a map of the two-cylinder field. -/
def cylinderCoeffScale {q : ℂ} (hq : q ≠ 0) :
    RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  RatFunc.mapRingHom (polyCoeffScale hq)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyCoeffScale_injective hq))

theorem cylinderCoeffScale_div {q : ℂ} (hq : q ≠ 0) (p s : Polynomial (RatFunc ℂ)) :
    cylinderCoeffScale hq (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p /
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) s)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (polyCoeffScale hq p) /
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (polyCoeffScale hq s) := by
  show RatFunc.mapRingHom (polyCoeffScale hq) _ _ = _
  rw [show ((RatFunc.mapRingHom (polyCoeffScale hq)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyCoeffScale_injective hq)) :
        RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ)) : RatFunc (RatFunc ℂ) → RatFunc (RatFunc ℂ))
      = RatFunc.map (polyCoeffScale hq) _ from RatFunc.coe_mapRingHom_eq_coe_map _ _]
  exact RatFunc.map_apply_div _ _ p s

/-- **Translation acts on the embedded two-cylinder field by dilating the first coordinate**,
whenever the second coordinate is a period of the translation.  This is the companion of
`addTranslationMeroEquiv_twoCylinderEmbed`, covering the other of the two period directions. -/
theorem addTranslationMeroEquiv_twoCylinderEmbed_coeff (hl : LinearIndependent ℚ l) (tau : ℂ)
    (h1 : Complex.exp (l 1 * tau) = 1) (y : RatFunc (RatFunc ℂ)) :
    addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
      = twoCylinderEmbed hl
          (cylinderCoeffScale (q := Complex.exp (l 0 * tau)) (Complex.exp_ne_zero _) y) := by
  classical
  set q0 : ℂ := Complex.exp (l 0 * tau) with hq0def
  have hq0 : q0 ≠ 0 := Complex.exp_ne_zero _
  set iota : RatFunc ℂ →+* meroField (Set.univ : Set ℂ) :=
    (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ)).toRingHom with hiota
  set u2 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 1) with hu2def
  have hcoeff : ∀ c : RatFunc ℂ,
      addTranslationMeroEquiv tau (iota c) = iota (ratFuncScale q0 hq0 c) := by
    intro c
    rw [hiota]
    show addTranslationMeroEquiv tau (cylinderEmbed hl 0 c)
      = cylinderEmbed hl 0 (ratFuncScale q0 hq0 c)
    rw [addTranslationMeroEquiv_cylinderEmbed hl 0 tau c]
  have hu2 : addTranslationMeroEquiv tau u2 = u2 := by
    rw [hu2def, addTranslationMeroEquiv_physicalExponentialMero, h1, map_one, one_mul]
  have hpoly : ∀ p : Polynomial (RatFunc ℂ),
      addTranslationMeroEquiv tau (Polynomial.eval₂ iota u2 p)
        = Polynomial.eval₂ iota u2 (polyCoeffScale hq0 p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p s hp hs =>
        rw [Polynomial.eval₂_add, (addTranslationMeroEquiv tau).map_add, hp, hs, map_add,
          Polynomial.eval₂_add]
    | monomial n c =>
        rw [Polynomial.eval₂_monomial, map_mul, map_pow, hcoeff, hu2,
          polyCoeffScale_monomial, Polynomial.eval₂_monomial]
  refine RatFunc.induction_on (P := fun y => addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
    = twoCylinderEmbed hl (cylinderCoeffScale hq0 y)) y ?_
  intro p s _
  rw [cylinderCoeffScale_div, twoCylinderEmbed_div, twoCylinderEmbed_div, map_div₀, hpoly, hpoly]

theorem polyCoeffScale_inv_scale {q : ℂ} (hq : q ≠ 0) (p : Polynomial (RatFunc ℂ)) :
    polyCoeffScale hq (polyCoeffScale (inv_ne_zero hq) p) = p := by
  refine Polynomial.ext fun n => ?_
  simp only [polyCoeffScale, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact ratFuncScale_inv_scale q hq _

theorem polyCoeffScale_scale_inv {q : ℂ} (hq : q ≠ 0) (p : Polynomial (RatFunc ℂ)) :
    polyCoeffScale (inv_ne_zero hq) (polyCoeffScale hq p) = p := by
  refine Polynomial.ext fun n => ?_
  simp only [polyCoeffScale, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact ratFuncScale_scale_inv q hq _

theorem cylinderCoeffScale_inv_scale {q : ℂ} (hq : q ≠ 0) (y : RatFunc (RatFunc ℂ)) :
    cylinderCoeffScale hq (cylinderCoeffScale (inv_ne_zero hq) y) = y := by
  refine RatFunc.induction_on
    (P := fun y => cylinderCoeffScale hq (cylinderCoeffScale (inv_ne_zero hq) y) = y) y ?_
  intro p s _
  rw [cylinderCoeffScale_div, cylinderCoeffScale_div, polyCoeffScale_inv_scale,
    polyCoeffScale_inv_scale]

theorem cylinderCoeffScale_scale_inv {q : ℂ} (hq : q ≠ 0) (y : RatFunc (RatFunc ℂ)) :
    cylinderCoeffScale (inv_ne_zero hq) (cylinderCoeffScale hq y) = y := by
  refine RatFunc.induction_on
    (P := fun y => cylinderCoeffScale (inv_ne_zero hq) (cylinderCoeffScale hq y) = y) y ?_
  intro p s _
  rw [cylinderCoeffScale_div, cylinderCoeffScale_div, polyCoeffScale_scale_inv,
    polyCoeffScale_scale_inv]

/-- The dilation of the first cylinder coordinate as a ring automorphism of the two-cylinder
field. -/
def cylinderCoeffScaleEquiv {q : ℂ} (hq : q ≠ 0) :
    RatFunc (RatFunc ℂ) ≃+* RatFunc (RatFunc ℂ) where
  toFun := cylinderCoeffScale hq
  invFun := cylinderCoeffScale (inv_ne_zero hq)
  left_inv := cylinderCoeffScale_scale_inv hq
  right_inv := cylinderCoeffScale_inv_scale hq
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] theorem cylinderCoeffScaleEquiv_apply {q : ℂ} (hq : q ≠ 0) (y : RatFunc (RatFunc ℂ)) :
    cylinderCoeffScaleEquiv hq y = cylinderCoeffScale hq y := rfl

end

end GaloisForLFunctions.HTGeometry
