import GaloisForLFunctions.HTGeometry.PaperStabilizedAdditiveAction
import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization
import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# Scalar translations survive on the rational field; polynomial coactions do not

Every scalar specialization of the stabilized clock extends to a native rational
field automorphism, preserving the additive group law faithfully. Yet this family
cannot arise from a polynomial additive coaction on the whole rational field:
local nilpotence forces every unit, hence every field element, to be fixed.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

/-- The distinguished stabilized polynomial in the literal rational function field. -/
def paperRationalStabilizedCoordinate : FreeCoordinateRationalField ℂ (Fin 5) :=
  algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5)) (stabilize f)

/-- Every complex time extends to an actual rational-field automorphism. -/
def paperRationalClockTranslation (t : ℂ) :
    FreeCoordinateRationalField ℂ (Fin 5) ≃ₐ[ℂ] FreeCoordinateRationalField ℂ (Fin 5) :=
  IsFractionRing.algEquivOfAlgEquiv (paperStabilizedTranslation t)

@[simp] theorem paperRationalClockTranslation_algebraMap (t : ℂ) (p : R 5) :
    paperRationalClockTranslation t
      (algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5)) p) =
      algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5))
        (paperStabilizedTranslation t p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

/-- The extended family retains the exact additive group law on every rational function. -/
theorem paperRationalClockTranslation_add (s t : ℂ)
    (q : FreeCoordinateRationalField ℂ (Fin 5)) :
    paperRationalClockTranslation s (paperRationalClockTranslation t q) =
      paperRationalClockTranslation (s + t) q := by
  have h : (paperRationalClockTranslation s).toRingHom.comp
      (paperRationalClockTranslation t).toRingHom =
      (paperRationalClockTranslation (s + t)).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := R 5)
    intro p
    change paperRationalClockTranslation s (paperRationalClockTranslation t
      (algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5)) p)) =
        paperRationalClockTranslation (s + t)
          (algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5)) p)
    simp only [paperRationalClockTranslation_algebraMap, paperStabilizedTranslation_add]
  exact RingHom.congr_fun h q

@[simp] theorem paperRationalClockTranslation_zero
    (q : FreeCoordinateRationalField ℂ (Fin 5)) : paperRationalClockTranslation 0 q = q := by
  have h : (paperRationalClockTranslation 0).toRingHom = RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := R 5)
    intro p
    exact paperRationalClockTranslation_algebraMap 0 p |>.trans
      (congrArg (algebraMap (R 5) (FreeCoordinateRationalField ℂ (Fin 5)))
        (paperStabilizedTranslation_zero p))
  exact RingHom.congr_fun h q

@[simp] theorem paperRationalClockTranslation_coordinate (t : ℂ) :
    paperRationalClockTranslation t paperRationalStabilizedCoordinate =
      paperRationalStabilizedCoordinate +
        algebraMap ℂ (FreeCoordinateRationalField ℂ (Fin 5)) t := by
  rw [paperRationalStabilizedCoordinate, paperRationalClockTranslation_algebraMap,
    paperStabilizedTranslation_f, map_add]
  rfl

/-- Reciprocals exhibit the rational dependence on the action parameter. -/
theorem paperRationalClockTranslation_reciprocal (t : ℂ) :
    paperRationalClockTranslation t paperRationalStabilizedCoordinate⁻¹ =
      (paperRationalStabilizedCoordinate +
        algebraMap ℂ (FreeCoordinateRationalField ℂ (Fin 5)) t)⁻¹ := by
  rw [map_inv₀, paperRationalClockTranslation_coordinate]

theorem paperRationalClockTranslation_injective : Function.Injective paperRationalClockTranslation := by
  intro s t h
  have he := DFunLike.congr_fun h paperRationalStabilizedCoordinate
  rw [paperRationalClockTranslation_coordinate, paperRationalClockTranslation_coordinate] at he
  exact (algebraMap ℂ (FreeCoordinateRationalField ℂ (Fin 5))).injective (add_left_cancel he)

/-- Every polynomial additive action on the whole native rational field has zero derivative. -/
theorem paperRationalPolynomialAction_derivation_eq_zero
    (ρ : PolynomialAdditiveAction ℂ (FreeCoordinateRationalField ℂ (Fin 5))) :
    ρ.derivation = 0 := by
  ext q
  by_cases hq : q = 0
  · simp [hq]
  · exact paperLocallyNilpotent_kills_unit ρ.derivation ρ.locallyNilpotent (Units.mk0 q hq)

/-- Every polynomial additive coaction on this field is itself trivial. -/
theorem paperRationalPolynomialAction_fixed
    (ρ : PolynomialAdditiveAction ℂ (FreeCoordinateRationalField ℂ (Fin 5)))
    (q : FreeCoordinateRationalField ℂ (Fin 5)) : ρ.toAlgHom q = Polynomial.C q :=
  ρ.action_eq_C_of_derivation_eq_zero (paperRationalPolynomialAction_derivation_eq_zero ρ) q

theorem paperRationalPolynomialAction_specialize
    (ρ : PolynomialAdditiveAction ℂ (FreeCoordinateRationalField ℂ (Fin 5)))
    (t : ℂ) (q : FreeCoordinateRationalField ℂ (Fin 5)) : ρ.specializeEquiv t q = q := by
  simp [PolynomialAdditiveAction.specialize_apply, paperRationalPolynomialAction_fixed]

/-- The actual faithful scalar family cannot be promoted to a polynomial coaction of the field. -/
theorem paperRationalClockTranslation_not_polynomial :
    ¬ ∃ ρ : PolynomialAdditiveAction ℂ (FreeCoordinateRationalField ℂ (Fin 5)),
      ∀ t : ℂ, ρ.specializeEquiv t = paperRationalClockTranslation t := by
  rintro ⟨ρ, hρ⟩
  have h : paperRationalClockTranslation 1 = paperRationalClockTranslation 0 := by
    rw [← hρ 1, ← hρ 0]
    apply AlgEquiv.ext
    intro q
    rw [paperRationalPolynomialAction_specialize, paperRationalPolynomialAction_specialize]
  exact one_ne_zero (paperRationalClockTranslation_injective h)

end

end GaloisForLFunctions.HTGeometry
