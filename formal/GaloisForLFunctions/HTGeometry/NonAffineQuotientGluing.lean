import GaloisForLFunctions.HTGeometry.SchemeQuotientDescent
import Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# General non-affine quotient gluing

A quotient sheaf need not be affine.  This file gives the exact bridge from a sheaf coequalizer
with a jointly-surjective Zariski-open scheme atlas to a scheme quotient.  Mathlib's local
representability theorem glues the atlas; full faithfulness of Yoneda then transports the sheaf
coequalizer universal property back to `Scheme`.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A quotient relation whose sheaf coequalizer admits a jointly-surjective Zariski-open scheme
atlas.  No affineness hypothesis is imposed on the glued quotient. -/
structure NonAffineQuotientDatum (R X : Scheme.{u}) (s t : R ⟶ X) where
  quotientSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u)
  quotientMap : yoneda.obj X ⟶ quotientSheaf.1
  condition : yoneda.map s ≫ quotientMap = yoneda.map t ≫ quotientMap
  isColimit : IsColimit (Cofork.ofπ quotientMap condition)
  chartIndex : Type u
  chart : chartIndex → Scheme.{u}
  chartMap : (i : chartIndex) → yoneda.obj (chart i) ⟶ quotientSheaf.1
  chartOpen : ∀ i, IsOpenImmersion.presheaf (chartMap i)
  chartLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc chartMap)

namespace NonAffineQuotientDatum

variable {R X : Scheme.{u}} {s t : R ⟶ X}
variable (D : NonAffineQuotientDatum R X s t)

/-- General non-affine quotient obtained by gluing its Zariski-open scheme atlas. -/
noncomputable def quotientScheme : Scheme.{u} := by
  letI := D.chartLocallySurjective
  exact (Scheme.LocalRepresentability.glueData D.chartOpen).glued

/-- The glued scheme represents the quotient sheaf. -/
noncomputable def representableBy : D.quotientSheaf.1.RepresentableBy D.quotientScheme := by
  letI := D.chartLocallySurjective
  exact Scheme.LocalRepresentability.representableBy D.chartOpen

/-- Scheme quotient projection induced from the quotient sheaf map. -/
noncomputable def projection : X ⟶ D.quotientScheme :=
  Yoneda.fullyFaithful.preimage (D.quotientMap ≫ D.representableBy.toIso.inv)

@[simp]
theorem yoneda_map_projection :
    yoneda.map D.projection = D.quotientMap ≫ D.representableBy.toIso.inv :=
  Yoneda.fullyFaithful.map_preimage _

theorem projection_condition : s ≫ D.projection = t ≫ D.projection := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, Functor.map_comp, D.yoneda_map_projection]
  rw [← Category.assoc, D.condition, Category.assoc]

private def yonedaCofork (c : Cofork s t) : Cofork (yoneda.map s) (yoneda.map t) :=
  Cofork.ofπ (yoneda.map c.π) (by
    simpa only [Functor.map_comp] using congrArg yoneda.map c.condition)

@[simp]
private theorem yonedaCofork_π (c : Cofork s t) :
    (yonedaCofork c).π = yoneda.map c.π := rfl

private noncomputable def desc (c : Cofork s t) : D.quotientScheme ⟶ c.pt :=
  Yoneda.fullyFaithful.preimage
    (D.representableBy.toIso.hom ≫ D.isColimit.desc (yonedaCofork c))

private theorem yoneda_map_desc (c : Cofork s t) :
    yoneda.map (D.desc c) = D.representableBy.toIso.hom ≫
      D.isColimit.desc (yonedaCofork c) := by
  exact Yoneda.fullyFaithful.map_preimage _

private theorem projection_desc (c : Cofork s t) : D.projection ≫ D.desc c = c.π := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, D.yoneda_map_projection]
  rw [yoneda_map_desc D c]
  calc
    (D.quotientMap ≫ D.representableBy.toIso.inv) ≫
        (D.representableBy.toIso.hom ≫ D.isColimit.desc (yonedaCofork c)) =
      D.quotientMap ≫ (D.representableBy.toIso.inv ≫
        D.representableBy.toIso.hom ≫ D.isColimit.desc (yonedaCofork c)) := by
          simp only [Category.assoc]
    _ = D.quotientMap ≫ D.isColimit.desc (yonedaCofork c) :=
      congrArg (fun k ↦ D.quotientMap ≫ k)
        (D.representableBy.toIso.inv_hom_id_assoc (D.isColimit.desc (yonedaCofork c)))
    _ = yoneda.map c.π := by
      exact (Cofork.IsColimit.π_desc (t := yonedaCofork c) D.isColimit).trans
        (yonedaCofork_π c)

private theorem desc_unique (c : Cofork s t) (m : D.quotientScheme ⟶ c.pt)
    (hm : D.projection ≫ m = c.π) : m = D.desc c := by
  apply Yoneda.fullyFaithful.map_injective
  rw [yoneda_map_desc D c]
  have hfac : D.quotientMap ≫
      (D.representableBy.toIso.inv ≫ yoneda.map m) = yoneda.map c.π := by
    rw [← Category.assoc, ← D.yoneda_map_projection, ← Functor.map_comp, hm]
  have hu : D.representableBy.toIso.inv ≫ yoneda.map m =
      D.isColimit.desc (yonedaCofork c) := by
    apply Cofork.IsColimit.hom_ext D.isColimit
    calc
      D.quotientMap ≫ (D.representableBy.toIso.inv ≫ yoneda.map m) =
          yoneda.map c.π := hfac
      _ = D.quotientMap ≫ D.isColimit.desc (yonedaCofork c) := by
        exact (yonedaCofork_π c).symm.trans
          (Cofork.IsColimit.π_desc (t := yonedaCofork c) D.isColimit).symm
  calc
    yoneda.map m = 𝟙 _ ≫ yoneda.map m := (Category.id_comp _).symm
    _ = (D.representableBy.toIso.hom ≫ D.representableBy.toIso.inv) ≫
        yoneda.map m := by rw [D.representableBy.toIso.hom_inv_id]
    _ = D.representableBy.toIso.hom ≫
        (D.representableBy.toIso.inv ≫ yoneda.map m) := Category.assoc _ _ _
    _ = D.representableBy.toIso.hom ≫ D.isColimit.desc (yonedaCofork c) :=
      congrArg (fun k ↦ D.representableBy.toIso.hom ≫ k) hu

/-- A locally representable sheaf coequalizer is an actual coequalizer in `Scheme`. -/
noncomputable def schemeQuotientPresentation : SchemeQuotientPresentation R X s t where
  quotient := D.quotientScheme
  projection := D.projection
  condition := D.projection_condition
  isColimit := Cofork.IsColimit.mk _ D.desc D.projection_desc D.desc_unique

end NonAffineQuotientDatum

end AlgebraicGeometry
