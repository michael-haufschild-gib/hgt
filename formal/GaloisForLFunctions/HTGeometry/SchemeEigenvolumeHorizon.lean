import GaloisForLFunctions.HTGeometry.SchemeMorphismOrderPullback
import GaloisForLFunctions.HTGeometry.EigenvolumeRamificationSystem

/-!
# The eigenvolume horizon theorem on a scheme

The abstract ramification system is instantiated here on the codimension-one points of an
integral Noetherian scheme carrying a self-morphism.  The order function is mathlib's order of
vanishing, its support is finite, and the shifted order law is assembled from the pullback law,
the order of the Jacobian factor, and the eigenvolume condition.

The conclusion is the eigenvolume horizon theorem in its scheme form: the horizon is a reduced
divisor, it is totally invariant, and the morphism is unramified off it.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

/-- A codimension-one point of a scheme. -/
abbrev CodimOnePoint (X : Scheme.{u}) := {z : X // coheight z = 1}

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of a rational function at a codimension-one point. -/
noncomputable def ordAt (g : X.functionField) (z : CodimOnePoint X) : ℤ := Scheme.ord g z.1

/-- The codimension-one point below a codimension-one point along a self-morphism. -/
def pointBelow (f : X ⟶ X) (hwd : ∀ z : CodimOnePoint X, coheight (f.base z.1) = 1)
    (z : CodimOnePoint X) : CodimOnePoint X :=
  ⟨f.base z.1, hwd z⟩

/-- **The divisorial support of a rational function is finite.** -/
theorem finite_ordAt_support [CompactSpace X] (g : X.functionField) :
    {z : CodimOnePoint X | ordAt g z ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_
    (Function.Injective.injOn Subtype.val_injective)
  refine Set.Finite.subset (finite_ord_support g) ?_
  rintro z ⟨y, hy, rfl⟩
  exact hy

section Law

variable (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
variable {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
variable (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
variable (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
variable (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)

include hPg hJ0 hpull hjac heig in
/-- **The shifted order law on a scheme.**  The pullback law, the order of the Jacobian factor
and the eigenvolume condition together give the local law of the abstract ramification system. -/
theorem schemeEigenvolume_shiftLaw (z : CodimOnePoint X) :
    ordAt g z + 1 = (e z : ℤ) * (ordAt g (F z) + 1) := by
  have hmul := Scheme.ord_mul (x := z.1) hPg hJ0
  rw [heig z, hpull z, hjac z] at hmul
  show Scheme.ord g z.1 + 1 = (e z : ℤ) * (Scheme.ord g (F z).1 + 1)
  rw [hmul]
  ring

include hPg hJ0 hpull hjac heig in
/-- **A self-morphism preserving an eigenvolume is unramified off its horizon.** -/
theorem schemeEigenvolume_ramificationIndex_eq_one_off_horizon {z : CodimOnePoint X}
    (hz : ordAt g z = 0) : e z = 1 :=
  ramificationIndex_eq_one_of_order_eq_zero
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig) hz

variable [CompactSpace X]
variable (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
variable (hram : ∀ y : CodimOnePoint X, ordAt g y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y →
  ∃ k < n, 1 < e (F^[k] y))

include hPg hJ0 hpull hjac heig hF hone hram in
/-- **The horizon of a scheme eigenvolume is a reduced divisor.** -/
theorem schemeEigenvolume_ordAt_eq_neg_one {z : CodimOnePoint X} (hz : ordAt g z ≠ 0) :
    ordAt g z = -1 :=
  eigenvolumeOrder_eq_neg_one_of_someRamified hF hone
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig)
    (finite_ordAt_support g) hram hz

include hPg hJ0 hpull hjac heig hF hone hram in
/-- **The horizon of a scheme eigenvolume is totally invariant.** -/
theorem schemeEigenvolume_ordAt_ne_zero_iff (z : CodimOnePoint X) :
    ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0 := by
  refine ⟨fun hz => ?_, fun hz =>
    order_ne_zero_of_image_ne_zero (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig) hz⟩
  have hval : ordAt g z = -1 :=
    schemeEigenvolume_ordAt_eq_neg_one F e hPg hJ0 hpull hjac heig hF hone hram hz
  have hlaw := schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig z
  rw [hval] at hlaw
  have hzero : (e z : ℤ) * (ordAt g (F z) + 1) = 0 := by linarith
  have hepos : (e z : ℤ) ≠ 0 := by
    have := hone z
    omega
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hepos
  · omega

end Law

/-- **The pullback law at every codimension-one point of a self-morphism.**  This is the
hypothesis `hpull` of the horizon theorem, discharged from the induced maps of local rings. -/
theorem ord_functionFieldMap_pointwise
    (f : X ⟶ X) (hf : f.base (genericPoint X) = genericPoint X)
    (hwd : ∀ z : CodimOnePoint X, coheight (f.base z.1) = 1)
    (hdvr : ∀ z : CodimOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk z.1))
    (e : CodimOnePoint X → ℕ)
    (π : ∀ z : CodimOnePoint X, X.presheaf.stalk (f.base z.1))
    (hπ : ∀ z : CodimOnePoint X, Irreducible (π z))
    (he : ∀ z : CodimOnePoint X, IsDiscreteValuationRing.addVal (X.presheaf.stalk z.1)
      ((f.stalkMap z.1).hom (π z)) = (e z : ℕ∞))
    {g : X.functionField} (hg : g ≠ 0) (z : CodimOnePoint X) :
    Scheme.ord (functionFieldMap f hf g) z.1 =
      (e z : ℤ) * Scheme.ord g (pointBelow f hwd z).1 := by
  haveI := hdvr z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (f.base z.1)) := hdvr ⟨f.base z.1, hwd z⟩
  exact ord_functionFieldMap_eq_mul_ramification f hf z.2 (hwd z) (hπ z) (e z) (he z) hg

end GaloisForLFunctions.HTGeometry
