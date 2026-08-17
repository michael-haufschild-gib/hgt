import GaloisForLFunctions.HTGeometry.FreeParameterBaseChange
import GaloisForLFunctions.HTGeometry.TranscendentalBaseChangeLattice

/-!
# The free parameter of the rational-function model

In `FractionRing (Polynomial E)` the variable is transcendental over `E`, and together with `E` it
generates everything.  These are the two hypotheses the base-change lattice theorem needs, in the
model where the free parameter is a formal variable rather than a coordinate of an ambient field.

With them the transfer of primitivity along a free parameter is available for any finite Galois
extension: no field lies strictly between `F(T)` and `J(T)` as soon as none lies strictly between
`F` and `J`.
-/

open IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The evaluation of a polynomial at the free parameter is its image in the fraction field. -/
theorem aeval_fracX (p : Polynomial E) :
    Polynomial.aeval (fracX E) p
      = algebraMap (Polynomial E) (FractionRing (Polynomial E)) p := by
  have hX : Polynomial.aeval (fracX E) (Polynomial.X : Polynomial E) = fracX E := by
    simp
  have h := Polynomial.algHom_ext (f := (Polynomial.aeval (fracX E) :
      Polynomial E →ₐ[E] FractionRing (Polynomial E)))
    (g := IsScalarTower.toAlgHom E (Polynomial E) (FractionRing (Polynomial E))) ?_
  · exact congrFun (congrArg (fun f : Polynomial E →ₐ[E] FractionRing (Polynomial E) =>
      (f : Polynomial E → FractionRing (Polynomial E))) h) p
  · rw [hX]
    rfl

/-- **The free parameter is transcendental over the coefficient field.** -/
theorem transcendental_fracX : Transcendental E (fracX E) := by
  rw [transcendental_iff]
  intro p hp
  rw [aeval_fracX] at hp
  exact IsFractionRing.injective (Polynomial E) (FractionRing (Polynomial E))
    (by rw [hp, _root_.map_zero])

/-- The coefficient field, inside the rational functions, as an intermediate field over the base. -/
def fracCoeffField (F E : Type*) [Field F] [Field E] [Algebra F E] :
    IntermediateField F (FractionRing (Polynomial E)) :=
  (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E))).fieldRange

theorem mem_fracCoeffField (a : E) :
    algebraMap E (FractionRing (Polynomial E)) a ∈ fracCoeffField F E :=
  ⟨a, rfl⟩

/-- **The coefficient field and the free parameter generate the rational functions.** -/
theorem fracCoeffField_sup_adjoin_fracX_eq_top :
    fracCoeffField F E ⊔ F⟮fracX E⟯ = ⊤ := by
  refine eq_top_of_mem_of_mem (S := fracCoeffField F E ⊔ F⟮fracX E⟯) ?_ ?_
  · intro a
    exact le_sup_left (α := IntermediateField F (FractionRing (Polynomial E)))
      (mem_fracCoeffField a)
  · exact le_sup_right (α := IntermediateField F (FractionRing (Polynomial E)))
      (IntermediateField.mem_adjoin_simple_self F (fracX E))

/-- The coefficient field is isomorphic to its copy inside the rational functions. -/
noncomputable def fracCoeffFieldEquiv : E ≃ₐ[F] ↥(fracCoeffField F E) :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E)))

instance fracCoeffField_finiteDimensional [FiniteDimensional F E] :
    FiniteDimensional F ↥(fracCoeffField F E) :=
  Module.Finite.equiv (fracCoeffFieldEquiv (F := F) (E := E)).toLinearEquiv

instance fracCoeffField_isGalois [FiniteDimensional F E] [IsGalois F E] :
    IsGalois F ↥(fracCoeffField F E) :=
  IsGalois.of_algEquiv (fracCoeffFieldEquiv (F := F) (E := E))

/-- The free parameter is transcendental over the copy of the coefficient field. -/
theorem transcendental_fracX_over_fracCoeffField :
    Transcendental (↥(fracCoeffField F E)) (fracX E) := by
  rw [transcendental_iff]
  intro p hp
  set e : E ≃ₐ[F] ↥(fracCoeffField F E) := fracCoeffFieldEquiv with he
  set φ : ↥(fracCoeffField F E) →+* E := (e.symm : ↥(fracCoeffField F E) →ₐ[F] E).toRingHom with hφ
  have hcomp : ((algebraMap E (FractionRing (Polynomial E))).comp φ)
      = algebraMap (↥(fracCoeffField F E)) (FractionRing (Polynomial E)) := by
    ext y
    show algebraMap E (FractionRing (Polynomial E)) (e.symm y)
      = (y : FractionRing (Polynomial E))
    exact congrArg (fun z : ↥(fracCoeffField F E) => (z : FractionRing (Polynomial E)))
      (e.apply_symm_apply y)
  have haeval : Polynomial.aeval (fracX E) (p.map φ) = Polynomial.aeval (fracX E) p := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
  have hq : p.map φ = 0 :=
    transcendental_iff.1 (transcendental_fracX (E := E)) (p.map φ) (by rw [haeval, hp])
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact (e.symm : ↥(fracCoeffField F E) →ₐ[F] E).toRingHom.injective
  exact (Polynomial.map_eq_zero_iff hinj).1 hq

theorem transcendental_fracX_over_base : Transcendental F (fracX E) := by
  intro halg
  exact transcendental_fracX_over_fracCoeffField (F := F) (E := E)
    (halg.tower_top (↥(fracCoeffField F E)))

/-- **Free-parameter base change preserves primitivity.**  If no field lies strictly between `F` and
`J` inside the rational functions, then none lies strictly between `F(T)` and `J(T)`. -/
theorem eq_bot_or_eq_adjoin_fracX_of_primitive
    [FiniteDimensional F E] [IsGalois F E]
    (J : IntermediateField F (FractionRing (Polynomial E))) (hJ : J ≤ fracCoeffField F E)
    (hprim : ∀ P : IntermediateField F (FractionRing (Polynomial E)), P ≤ J → P = ⊥ ∨ P = J)
    (M : IntermediateField (↥F⟮fracX E⟯) (FractionRing (Polynomial E)))
    (hM : M ≤ IntermediateField.adjoin (↥F⟮fracX E⟯)
      (J : Set (FractionRing (Polynomial E)))) :
    M = ⊥ ∨ M = IntermediateField.adjoin (↥F⟮fracX E⟯)
      (J : Set (FractionRing (Polynomial E))) :=
  eq_bot_or_eq_adjoin_of_primitive_base_change (fracCoeffField F E) (fracX E)
    transcendental_fracX_over_base transcendental_fracX_over_fracCoeffField
    fracCoeffField_sup_adjoin_fracX_eq_top J hJ hprim M hM

end GaloisForLFunctions.HTGeometry

end
