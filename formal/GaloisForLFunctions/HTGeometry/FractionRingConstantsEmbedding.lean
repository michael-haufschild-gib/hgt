import GaloisForLFunctions.HTGeometry.FractionRingAdjoinX
import GaloisForLFunctions.HTGeometry.RationalFunctionRelativeClosure

/-!
# Rational functions over a subfield of the constants

Extending the constants embeds one field of rational functions in the other, the variable going to
the variable.

An element of the image algebraic over the small constants is algebraic there, hence constant, so
the image carries no algebraic element beyond the small constants — which is the hypothesis of the
base change step.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem injective_polyMap :
    Function.Injective (Polynomial.mapRingHom (algebraMap F E)) :=
  Polynomial.map_injective _ (algebraMap F E).injective

/-- Extending the constants, on rational functions. -/
noncomputable def fracEmbedRingHom (F E : Type*) [Field F] [Field E] [Algebra F E] :
    FractionRing (Polynomial F) →+* FractionRing (Polynomial E) :=
  IsFractionRing.lift
    (g := (algebraMap (Polynomial E) (FractionRing (Polynomial E))).comp
      (Polynomial.mapRingHom (algebraMap F E)))
    ((IsFractionRing.injective (Polynomial E) (FractionRing (Polynomial E))).comp
      injective_polyMap)

theorem fracEmbedRingHom_algebraMap (f : Polynomial F) :
    fracEmbedRingHom F E (algebraMap (Polynomial F) (FractionRing (Polynomial F)) f) =
      algebraMap (Polynomial E) (FractionRing (Polynomial E))
        (f.map (algebraMap F E)) :=
  IsFractionRing.lift_algebraMap _ _

theorem fracEmbedRingHom_injective :
    Function.Injective (fracEmbedRingHom F E) :=
  (fracEmbedRingHom F E).injective

/-- Extending the constants, as a map of algebras over the small constants. -/
noncomputable def fracEmbed (F E : Type*) [Field F] [Field E] [Algebra F E] :
    FractionRing (Polynomial F) →ₐ[F] FractionRing (Polynomial E) where
  __ := fracEmbedRingHom F E
  commutes' := fun a => by
    have h1 : algebraMap F (FractionRing (Polynomial F)) a =
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
          (algebraMap F (Polynomial F) a) :=
      IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)) a
    have h2 : algebraMap F (FractionRing (Polynomial E)) a =
        algebraMap (Polynomial E) (FractionRing (Polynomial E))
          (algebraMap F (Polynomial E) a) :=
      IsScalarTower.algebraMap_apply F (Polynomial E) (FractionRing (Polynomial E)) a
    have h3 : (algebraMap F (Polynomial F) a).map (algebraMap F E) =
        algebraMap F (Polynomial E) a := by
      rw [Polynomial.algebraMap_eq, Polynomial.map_C]
      rw [show (algebraMap F (Polynomial E)) a = Polynomial.C (algebraMap F E a) from rfl]
    show fracEmbedRingHom F E (algebraMap F (FractionRing (Polynomial F)) a) = _
    rw [h1, fracEmbedRingHom_algebraMap, h3, ← h2]

theorem fracEmbed_apply (u : FractionRing (Polynomial F)) :
    fracEmbed F E u = fracEmbedRingHom F E u := rfl

/-- **The image of the small rational functions carries no new algebraic element.** -/
theorem mem_bot_of_mem_fieldRange_of_isAlgebraic
    {x : FractionRing (Polynomial E)} (hx : x ∈ (fracEmbed F E).fieldRange)
    (halg : IsAlgebraic F x) :
    x ∈ (⊥ : IntermediateField F (FractionRing (Polynomial E))) := by
  obtain ⟨u, rfl⟩ := hx
  have hinj : Function.Injective (fracEmbed F E) := fracEmbedRingHom_injective
  have hu : IsAlgebraic F u := by
    have h := (isAlgebraic_algHom_iff (fracEmbed F E) hinj).1 halg
    exact h
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_isAlgebraic hu
  refine IntermediateField.mem_bot.2 ⟨a, ?_⟩
  rw [← ha]
  exact ((fracEmbed F E).commutes a).symm

end GaloisForLFunctions.HTGeometry
