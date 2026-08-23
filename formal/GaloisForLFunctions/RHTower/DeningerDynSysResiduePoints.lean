import GaloisForLFunctions.RHTower.DeningerDynSysProp35Integral
import GaloisForLFunctions.RHTower.DeningerDynSysNormalizationAction
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.CharP.Algebra

/-!
# Points with values in an algebraically closed field, in residue-field form

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3: a point of `X₀(C)`
is a scheme-theoretic point `x₀` of `X₀` together with an embedding of `κ(x₀)` into `C`, and such
embeddings exist only when `char κ(x₀) = char C`.

Proposition 3.5 in this language: along an integral morphism with injective section maps, every
pair `(x₀ , κ(x₀) ↪ C)` is the image of a pair `(x , κ(x) ↪ C)` with `x` lying over `x₀`.  This is
the surjectivity statement of `DeningerDynSysProp35Integral` transported through the bijection
between `Spec C ⟶ X` and such pairs.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀) {C : Type u} [Field C]

/-- **Deninger, §3, after Proposition 3.5.**  A point of `X₀` contributes to `X₀(C)` only if its
residue field has the characteristic of `C`. -/
theorem deningerResiduePoint_ringChar_eq (x₀ : X₀)
    (α₀ : X₀.residueField x₀ ⟶ CommRingCat.of C) :
    ringChar (X₀.residueField x₀) = ringChar C := by
  haveI : CharP (X₀.residueField x₀) (ringChar (X₀.residueField x₀)) := ringChar.charP _
  haveI : CharP C (ringChar (X₀.residueField x₀)) :=
    charP_of_injective_ringHom (f := α₀.hom) α₀.hom.injective _
  exact (ringChar.eq C (ringChar (X₀.residueField x₀))).symm

variable [IsAlgClosed C]

/-- **Deninger, Proposition 3.5, surjectivity in residue-field form.**  Along an integral morphism
with injective section maps, every point of the base with an embedding of its residue field into
an algebraically closed field is induced by such a datum upstairs. -/
theorem deningerResiduePoint_exists [IsIntegralHom π]
    (hinj : ∀ U₀ : X₀.Opens, IsAffineOpen U₀ → Function.Injective (π.app U₀).hom)
    (x₀ : X₀) (α₀ : X₀.residueField x₀ ⟶ CommRingCat.of C) :
    ∃ (x : X) (hx : π.base x = x₀) (α : X.residueField x ⟶ CommRingCat.of C),
      π.residueFieldMap x ≫ α = (X₀.residueFieldCongr hx).hom ≫ α₀ := by
  obtain ⟨h, hh⟩ := deningerSchemePoint_surjective_of_isIntegralHom (C := C) π hinj
    ((Scheme.SpecToEquivOfField C X₀).symm ⟨x₀, α₀⟩)
  have hh' : h ≫ π = (Scheme.SpecToEquivOfField C X₀).symm ⟨x₀, α₀⟩ := hh
  have key : Scheme.SpecToEquivOfField C X₀ (h ≫ π) = ⟨x₀, α₀⟩ := by
    rw [hh', Equiv.apply_symm_apply]
  rw [Scheme.SpecToEquivOfField_eq_iff] at key
  simp only [Scheme.SpecToEquivOfField_apply_fst, Scheme.SpecToEquivOfField_apply_snd,
    Scheme.Hom.comp_base] at key
  obtain ⟨e, he⟩ := key
  refine ⟨h.base (IsLocalRing.closedPoint C), e,
    X.descResidueField (Scheme.stalkClosedPointTo h), ?_⟩
  rw [← Scheme.descResidueField_stalkClosedPointTo_comp π h]
  exact he

variable {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **Deninger, Proposition 3.5 for the relative normalization, in residue-field form.**  Every
point of the base together with an embedding of its residue field into an algebraically closed
field lifts to the normalization of the base in a scheme-theoretically dominant morphism. -/
theorem deningerNormalizationResiduePoint_exists [IsSchemeTheoreticallyDominant f]
    (y : Y) (α : Y.residueField y ⟶ CommRingCat.of C) :
    ∃ (z : f.normalization) (hz : f.fromNormalization.base z = y)
      (β : (f.normalization).residueField z ⟶ CommRingCat.of C),
      f.fromNormalization.residueFieldMap z ≫ β = (Y.residueFieldCongr hz).hom ≫ α :=
  deningerResiduePoint_exists f.fromNormalization
    (fun U _ => deningerNormalization_app_injective f U) y α

end

end RHTower
