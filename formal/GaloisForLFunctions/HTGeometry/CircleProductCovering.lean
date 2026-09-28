import GaloisForLFunctions.HTGeometry.FundamentalGroupProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Products of simply connected spaces and the circle covering

Path classes in a product split into coordinate path classes. The real
exponential circle cover remains a covering after adjoining any unchanged
topological factor; its local sheets are constructed explicitly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A product of simply connected spaces is simply connected. -/
instance simplyConnectedSpace_product {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] : SimplyConnectedSpace (X × Y) := by
  apply simply_connected_iff_paths_homotopic.mpr
  refine ⟨inferInstance, fun a b => ⟨fun p q => ?_⟩⟩
  rw [← Path.Homotopic.prod_projLeft_projRight p,
    ← Path.Homotopic.prod_projLeft_projRight q]
  congr 1
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- Adjoining an unchanged factor preserves the exponential circle covering. -/
theorem circleProduct_isCoveringMap (X : Type*) [TopologicalSpace X] :
    IsCoveringMap (fun p : X × ℝ => (p.1, Circle.exp p.2)) := by
  intro x
  obtain ⟨hdisc, U, hxU, hU, heU, H, hH⟩ := Circle.isCoveringMap_exp x.2
  letI := hdisc
  let W : Set (X × Circle) := Prod.snd ⁻¹' U
  let e : ((fun p : X × ℝ => (p.1, Circle.exp p.2)) ⁻¹' W) ≃ₜ
      W × (Circle.exp ⁻¹' {x.2}) :=
    { toFun := fun p =>
        (⟨(p.1.1, (H ⟨p.1.2, p.2⟩).1.1), (H ⟨p.1.2, p.2⟩).1.2⟩,
          (H ⟨p.1.2, p.2⟩).2)
      invFun := fun p =>
        ⟨(p.1.1.1, H.symm (⟨p.1.1.2, p.1.2⟩, p.2)),
          (H.symm (⟨p.1.1.2, p.1.2⟩, p.2)).2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact congrArg Subtype.val (H.symm_apply_apply ⟨p.1.2, p.2⟩)
      right_inv := by
        intro p
        have h := H.apply_symm_apply (⟨p.1.1.2, p.1.2⟩, p.2)
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext rfl (congrArg (fun q => q.1.1) h)
        · exact congrArg (fun q : U × (Circle.exp ⁻¹' {x.2}) => q.2) h
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := Circle.exp ⁻¹' {x.2})
  refine ⟨hdisc, W, hxU, hU.preimage continuous_snd,
    heU.preimage continuous_snd, e, ?_⟩
  intro p
  exact Prod.ext rfl (hH ⟨p.1.2, p.2⟩)

end

end GaloisForLFunctions.HTGeometry
