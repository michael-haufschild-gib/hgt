import GaloisForLFunctions.HTGeometry.RatFuncTotalDerivation
import GaloisForLFunctions.HTGeometry.RatFuncFieldShift
import GaloisForLFunctions.HTGeometry.TwoPacketRationalPrimitiveRigidity

/-!
# Coefficient extension of rational coordinate fields

An embedding of coefficient fields extends injectively to their one-variable rational function
fields while fixing the coordinate.  If the coefficient embedding is differential, this extension
commutes with the total coordinate derivations.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E]

theorem ratFuncCoeffRegular (f : F →+* E) :
    nonZeroDivisors (Polynomial F) ≤
      Submonoid.comap (Polynomial.mapRingHom f) (nonZeroDivisors (Polynomial E)) := by
  intro p hp
  apply mem_nonZeroDivisors_of_ne_zero
  intro hzero
  have hpzero : (p : Polynomial F) = 0 :=
    (Polynomial.map_injective f f.injective) (by simpa using hzero)
  exact nonZeroDivisors.coe_ne_zero ⟨p, hp⟩ hpzero

/-- Coefficientwise embedding of rational function fields. -/
def ratFuncCoeffMap (f : F →+* E) : RatFunc F →+* RatFunc E :=
  RatFunc.mapRingHom (Polynomial.mapRingHom f) (ratFuncCoeffRegular f)

theorem ratFuncCoeffMap_injective (f : F →+* E) :
    Function.Injective (ratFuncCoeffMap f) := by
  exact RatFunc.map_injective (Polynomial.mapRingHom f) (ratFuncCoeffRegular f)
    (Polynomial.map_injective f f.injective)

theorem ratFuncCoeffMap_algebraMap_poly (f : F →+* E) (p : Polynomial F) :
    ratFuncCoeffMap f (algebraMap (Polynomial F) (RatFunc F) p) =
      algebraMap (Polynomial E) (RatFunc E) (Polynomial.map f p) := by
  change (RatFunc.map (Polynomial.mapRingHom f) (ratFuncCoeffRegular f))
    (algebraMap (Polynomial F) (RatFunc F) p) = _
  simpa using RatFunc.map_apply_div (Polynomial.mapRingHom f)
    (ratFuncCoeffRegular f) p 1

theorem ratFuncCoeffMap_X (f : F →+* E) :
    ratFuncCoeffMap f (RatFunc.X : RatFunc F) = RatFunc.X := by
  rw [show (RatFunc.X : RatFunc F) =
      algebraMap (Polynomial F) (RatFunc F) Polynomial.X by
        rw [RatFunc.algebraMap_X],
    ratFuncCoeffMap_algebraMap_poly, Polynomial.map_X, RatFunc.algebraMap_X]

theorem ratFuncCoeffMap_base (f : F →+* E) (c : F) :
    ratFuncCoeffMap f (algebraMap F (RatFunc F) c) =
      algebraMap E (RatFunc E) (f c) := by
  rw [show algebraMap F (RatFunc F) c =
      algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c) by
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply],
    ratFuncCoeffMap_algebraMap_poly, Polynomial.map_C]
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- Coefficient extension commutes with unit translation of the rational coordinate. -/
theorem ratFuncCoeffMap_ratShift (f : F →+* E) (r : RatFunc F) :
    ratFuncCoeffMap f (FieldShift.ratShift r) =
      FieldShift.ratShift (ratFuncCoeffMap f r) := by
  let lhs : RatFunc F →+* RatFunc E :=
    (ratFuncCoeffMap f).comp FieldShift.ratShift
  let rhs : RatFunc F →+* RatFunc E :=
    FieldShift.ratShift.comp (ratFuncCoeffMap f)
  have hhom : lhs = rhs := by
    apply IsFractionRing.ringHom_ext (A := Polynomial F)
    intro p
    change ratFuncCoeffMap f
        (FieldShift.ratShift (algebraMap (Polynomial F) (RatFunc F) p)) =
      FieldShift.ratShift
        (ratFuncCoeffMap f (algebraMap (Polynomial F) (RatFunc F) p))
    rw [FieldShift.ratShift_algebraMap, ratFuncCoeffMap_algebraMap_poly,
      ratFuncCoeffMap_algebraMap_poly, FieldShift.ratShift_algebraMap]
    congr 1
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [Polynomial.add_comp, Polynomial.map_add, Polynomial.map_add,
          Polynomial.add_comp, hp, hq]
    | monomial n a => simp [Polynomial.monomial_comp]
  exact RingHom.congr_fun hhom r

variable [CharZero F] [CharZero E] [Differential F] [Differential E]

/-- Coefficient extension commutes with total differentiation on the polynomial coordinate ring. -/
theorem polyTotalDeriv_map (f : F →+* E)
    (hf : ∀ c : F, f (Differential.deriv c) = Differential.deriv (f c))
    (p : Polynomial F) :
    polyTotalDeriv (Polynomial.map f p) = Polynomial.map f (polyTotalDeriv p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial n c =>
      simp only [Polynomial.map_monomial, polyTotalDeriv_apply,
        Polynomial.derivative_monomial, coeffDeriv_monomial, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        hf, map_mul, map_natCast]

/-- Coefficient extension as a rational algebra homomorphism. -/
def ratFuncCoeffAlgHom (f : F →+* E) : RatFunc F →ₐ[ℚ] RatFunc E :=
  { ratFuncCoeffMap f with
    commutes' := fun q => by simp }

/-- Coefficient extension commutes with total coordinate differentiation. -/
theorem ratFuncCoeffMap_deriv (f : F →+* E)
    (hf : ∀ c : F, f (Differential.deriv c) = Differential.deriv (f c))
    (r : RatFunc F) :
    coordinateTotalDerivation (ratFuncCoeffMap f r) =
      ratFuncCoeffMap f (coordinateTotalDerivation r) := by
  refine fractionRingAlgHom_derivation_commutes
    (φ := ratFuncCoeffAlgHom f)
    (DK := coordinateTotalDerivation) (DE := coordinateTotalDerivation)
    (A := Polynomial F) (K := RatFunc F) ?_ r
  intro p
  rw [coordinateTotalDerivation_algebraMap,
    show ratFuncCoeffAlgHom f (algebraMap (Polynomial F) (RatFunc F) p) =
      algebraMap (Polynomial E) (RatFunc E) (Polynomial.map f p) by
        exact ratFuncCoeffMap_algebraMap_poly f p,
    coordinateTotalDerivation_algebraMap,
    show ratFuncCoeffAlgHom f
        (algebraMap (Polynomial F) (RatFunc F) (polyTotalDeriv p)) =
      algebraMap (Polynomial E) (RatFunc E) (Polynomial.map f (polyTotalDeriv p)) by
        exact ratFuncCoeffMap_algebraMap_poly f (polyTotalDeriv p),
    polyTotalDeriv_map f hf]

end

end GaloisForLFunctions.HTGeometry
