import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting

open Set
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {X : Type*} [TopologicalSpace X] {x y : X} {γ : Path x x} {δ : Path y y}

/-- The actual moving basepoint of a free homotopy of loops. -/
def freeLoopBasePath (H : γ.toContinuousMap.Homotopy δ.toContinuousMap) : Path x y where
  toFun s := H (s, 0)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := (H.apply_zero 0).trans γ.source
  target' := (H.apply_one 0).trans δ.source

/-- The two boundary routes of a free loop homotopy agree, with their actual basepoint connector. -/
theorem freeLoopHomotopy_boundary (H : γ.toContinuousMap.Homotopy δ.toContinuousMap)
    (hclosed : ∀ s : I, H (s, 0) = H (s, 1)) :
    (γ.trans (freeLoopBasePath H)).Homotopic ((freeLoopBasePath H).trans δ) := by
  obtain ⟨F⟩ := Path.Homotopic.map_trans_evalAt H Path.id
  refine ⟨(F.pathCast γ.source.symm δ.target.symm).cast ?_ ?_⟩
  · apply Path.ext
    funext t
    change ((Path.id.map γ.continuous).trans (H.evalAt 1)) t =
      (γ.trans (freeLoopBasePath H)) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · rfl
    · exact (hclosed _).symm
  · apply Path.ext
    funext t
    change ((H.evalAt 0).trans (Path.id.map δ.continuous)) t =
      ((freeLoopBasePath H).trans δ) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl

/-- Free loop homotopies give an explicit fiber equivalence intertwining native monodromies. -/
theorem exists_monodromy_equiv_of_freeLoopHomotopy {E : Type*} [TopologicalSpace E] {p : E → X}
    (cov : IsCoveringMap p) (H : γ.toContinuousMap.Homotopy δ.toContinuousMap)
    (hclosed : ∀ s : I, H (s, 0) = H (s, 1)) :
    ∃ e : p ⁻¹' {x} ≃ p ⁻¹' {y},
      (∀ z, e z = cov.monodromy (.mk (freeLoopBasePath H)) z) ∧
      ∀ z, e (cov.monodromyPerm x (FundamentalGroup.fromPath (.mk γ)) z) =
        cov.monodromyPerm y (FundamentalGroup.fromPath (.mk δ)) (e z) := by
  let e := Equiv.ofBijective (cov.monodromy (.mk (freeLoopBasePath H)))
    (cov.monodromy_bijective (.mk (freeLoopBasePath H)))
  refine ⟨e, fun _ => rfl, ?_⟩
  intro z
  change cov.monodromy (.mk (freeLoopBasePath H)) (cov.monodromy (.mk γ) z) =
    cov.monodromy (.mk δ) (cov.monodromy (.mk (freeLoopBasePath H)) z)
  have he := Path.Homotopic.Quotient.eq.mpr (freeLoopHomotopy_boundary H hclosed)
  have hm := congrArg (fun q => cov.monodromy q z) he
  simpa only [Path.Homotopic.Quotient.mk_trans, cov.monodromy_trans_apply] using hm

end
end GaloisForLFunctions.HTGeometry
