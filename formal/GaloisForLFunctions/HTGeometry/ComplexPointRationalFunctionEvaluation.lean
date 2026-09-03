import GaloisForLFunctions.HTGeometry.SpecStalkLocalization
import GaloisForLFunctions.HTGeometry.FunctionFieldPullback
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Analysis.Complex.Basic

/-!
# Rational-function evaluation at complex-valued scheme points

A rational function which is regular at a complex-valued point is represented by a germ in the
local ring at that point.  The point's stalk map, followed by the canonical identification of the
unique stalk of `Spec ℂ` with `ℂ`, evaluates that germ.  This gives a scheme-theoretic coordinate
evaluation interface without postulating an analytification functor.
-/

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace

universe u

noncomputable section

/-- A complex-valued point of a scheme. -/
abbrev Scheme.ComplexPoint (X : Scheme) := Spec (.of ℂ) ⟶ X

/-- A complex-valued point over a fixed base field embedding. -/
structure Scheme.ComplexPointOver (k : Type) [Field k] [Algebra k ℂ]
    (X : Scheme) (s : X ⟶ Spec (.of k)) where
  hom : X.ComplexPoint
  commutes : hom ≫ s =
    Spec.map (CommRingCat.ofHom (algebraMap k ℂ))

/-- Underlying scheme point of a complex-valued point. -/
def Scheme.ComplexPoint.center {X : Scheme} (p : X.ComplexPoint) : X :=
  p (genericPoint (Spec (.of ℂ)))

/-- Evaluation of a local germ at a complex-valued point. -/
noncomputable def Scheme.ComplexPoint.stalkEval {X : Scheme} (p : X.ComplexPoint) :
    X.presheaf.stalk p.center →+* ℂ :=
  (HTGeometry.specFieldStalkEquiv ℂ
      (genericPoint (Spec (.of ℂ)))).symm.toRingHom.comp
    (p.stalkMap (genericPoint (Spec (.of ℂ)))).hom

/-- A rational function regular at a complex-valued point, represented by a germ in its local
ring whose image at the generic point is the given rational function. -/
structure Scheme.RationalFunctionRegularAtComplexPoint
    (X : Scheme) [IrreducibleSpace X] (p : X.ComplexPoint)
    (f : X.functionField) where
  germ : X.presheaf.stalk p.center
  represents :
    X.presheaf.stalkSpecializes (genericPoint_specializes p.center) germ = f

/-- Value of a regular rational-function germ at its complex-valued point. -/
noncomputable def Scheme.RationalFunctionRegularAtComplexPoint.value
    {X : Scheme} [IrreducibleSpace X] {p : X.ComplexPoint} {f : X.functionField}
    (h : X.RationalFunctionRegularAtComplexPoint p f) : ℂ :=
  p.stalkEval h.germ

/-- On an affine spectrum, the adjunction unit is the spectrum map of the canonical global-section
equivalence. -/
theorem Scheme.toSpecΓ_eq_specMap_ΓSpecIso_hom (R : CommRingCat) :
    (Spec R).toSpecΓ = Spec.map (Scheme.ΓSpecIso R).hom := by
  apply (cancel_mono (Spec.map (Scheme.ΓSpecIso R).inv)).1
  rw [← Spec.map_comp]
  rw [Iso.inv_hom_id, Spec.map_id]
  exact ΓSpec.adjunction.right_triangle_components (Opposite.op R)

/-- A rational-function germ transported from the generic-point stalk to any point proved equal
to the generic point.  Keeping the equality explicit avoids an untracked choice of local
representative. -/
noncomputable def Scheme.genericPointGerm
    {X : Scheme} [IrreducibleSpace X]
    (q : X) (hq : q = genericPoint X) (f : X.functionField) :
    X.presheaf.stalk q :=
  hq.symm ▸ f

/-- The transported generic-point germ represents the original rational function. -/
theorem Scheme.genericPointGerm_represents
    {X : Scheme} [IrreducibleSpace X]
    (q : X) (hq : q = genericPoint X) (f : X.functionField) :
    X.presheaf.stalkSpecializes (genericPoint_specializes q)
      (X.genericPointGerm q hq f) = f := by
  subst q
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Transport from the generic-point stalk agrees with specialization in the reverse equality
direction. -/
theorem Scheme.genericPointGerm_eq_stalkSpecializes
    {X : Scheme} [IrreducibleSpace X]
    (q : X) (hq : q = genericPoint X) (f : X.functionField) :
    X.genericPointGerm q hq f =
      X.presheaf.stalkSpecializes (show q ⤳ genericPoint X by rw [hq]) f := by
  subst q
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Every rational function is regular at a complex-valued point whose center is the generic
point. -/
noncomputable def Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint
    {X : Scheme} [IrreducibleSpace X]
    (p : X.ComplexPoint) (hp : p.center = genericPoint X) (f : X.functionField) :
    X.RationalFunctionRegularAtComplexPoint p f :=
  ⟨X.genericPointGerm p.center hp f,
    X.genericPointGerm_represents p.center hp f⟩

/-- The field-valued stalk equivalence sends the canonical function-field image of an element
back to that same element. -/
theorem Scheme.specFieldStalkEquiv_symm_specFunctionFieldAlgEquiv
    (K : Type u) [Field K] (a : K) :
    (HTGeometry.specFieldStalkEquiv K
      (genericPoint (Spec (.of K)))).symm
        (Scheme.specFunctionFieldAlgEquiv K a) = a := by
  letI := Scheme.specFunctionFieldAlgebra K
  rw [show Scheme.specFunctionFieldAlgEquiv K a =
      (StructureSheaf.toStalk K (genericPoint (Spec (.of K)))).hom a by
    exact (Scheme.specFunctionFieldAlgEquiv K).commutes a]
  apply (HTGeometry.specFieldStalkEquiv K
    (genericPoint (Spec (.of K)))).injective
  rw [RingEquiv.apply_symm_apply]
  unfold HTGeometry.specFieldStalkEquiv HTGeometry.specStalkRingEquiv
  simp only [RingEquiv.trans_apply]
  let p := genericPoint (Spec (.of K))
  let e : K ≃ₐ[K] Localization.AtPrime p.asIdeal :=
    IsLocalization.atUnits (R := K) (S := Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl (by
        intro b hb
        have hbot : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime p.asIdeal
        have hne : b ≠ 0 := by
          intro h
          apply hb
          rw [h, hbot]
          exact Ideal.zero_mem _
        exact ⟨Units.mk0 b hne, rfl⟩)
  change (StructureSheaf.toStalk K p).hom a =
    (StructureSheaf.stalkIso K p) (e a)
  have he : e a = algebraMap K (Localization.AtPrime p.asIdeal) a := by
    simpa using e.commutes a
  rw [he]
  exact ((StructureSheaf.stalkIso K p).commutes a).symm

/-- Evaluation of the canonical generic-center germ is the dominant function-field pullback,
followed by the canonical identification of the function field of `Spec ℂ` with `ℂ`. -/
theorem Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint_value
    {X : Scheme} [IrreducibleSpace X]
    (p : X.ComplexPoint) [IsDominant p] (f : X.functionField) :
    (X.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint p
      p.map_genericPoint_of_isDominant f).value =
      (HTGeometry.specFieldStalkEquiv ℂ
        (genericPoint (Spec (.of ℂ)))).symm
        (p.functionFieldPullback f) := by
  simp only [Scheme.RationalFunctionRegularAtComplexPoint.value,
    Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint]
  rw [show X.genericPointGerm p.center p.map_genericPoint_of_isDominant f =
      X.presheaf.stalkSpecializes p.dominantGenericSpecializes f by
    rw [X.genericPointGerm_eq_stalkSpecializes]
    congr]
  simp [Scheme.ComplexPoint.stalkEval,
    Scheme.Hom.functionFieldPullback]
  congr

end


end AlgebraicGeometry
