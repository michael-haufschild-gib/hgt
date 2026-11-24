import GaloisForLFunctions.HTGeometry.RestrictScalarsRegular

/-! Weak regularity is preserved under flat scalar extension, with
the sequence acting through the algebra map. -/

noncomputable section

open RingTheory.Sequence GaloisForLFunctions.HTGeometry
open scoped Pointwise

namespace GlobalTheory.PD

universe u

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The base elements and their images cut out the same successive
quotients of a module over the extension ring. -/
theorem weaklyRegular_map {r : List A} (h : IsWeaklyRegular N r) :
    IsWeaklyRegular N (r.map (algebraMap A B)) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < r.length := by simpa only [List.length_map] using hi
  have hr := h.regular_mod_prev i hi'
  rw [← List.map_take, List.getElem_map]
  let I := Ideal.ofList (r.take i)
  let Q := (Ideal.ofList ((r.take i).map (algebraMap A B))) • (⊤ : Submodule B N)
  have hQ : Q.restrictScalars A = I • (⊤ : Submodule A N) := by
    change (((Ideal.ofList ((r.take i).map (algebraMap A B))) •
      (⊤ : Submodule B N))).restrictScalars A = I • (⊤ : Submodule A N)
    rw [← Ideal.map_ofList]
    exact restrictScalars_map_smul_top (D := B) (N := N) I
  let e := (Submodule.quotEquivOfEq _ _ hQ).symm.trans
    (Submodule.Quotient.restrictScalarsEquiv (S := A) Q)
  have hR := (isSMulRegular_congr e r[i]).mp hr
  intro x y hxy
  apply hR
  simpa only [IsScalarTower.algebraMap_smul] using hxy

/-- Transport a weakly regular sequence from the base ring to a flat algebra. -/
theorem weaklyRegular_map_of_flat [Module.Flat A B] {r : List A}
    (h : IsWeaklyRegular A r) : IsWeaklyRegular B (r.map (algebraMap A B)) := by
  have h' : IsWeaklyRegular B r :=
    ((TensorProduct.rid A B).isWeaklyRegular_congr r).mp h.isWeaklyRegular_lTensor
  exact weaklyRegular_map h'

end GlobalTheory.PD
