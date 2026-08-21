import GaloisForLFunctions.HTGeometry.BorelWeil.PairChart

/-!
# The cell sections as a subalgebra

The weight-zero sections over an intersection of cells form a `k`-subalgebra of the flag
localization — the ring of functions on that intersection — and the Weyl group acts on the flag
localization by `k`-algebra maps.

## Main definitions

* `cellSubalg` — the ring of functions on an intersection of cells.
* `weylAlg` — the Weyl action as an algebra map.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The ring of functions on an intersection of Bruhat cells. -/
noncomputable def cellSubalg (N : ℕ) (k : Type*) [Field k] [Infinite k]
    (I : Finset (Equiv.Perm (Fin N))) : Subalgebra k (FlagLoc N k) :=
  Submodule.toSubalgebra (cellSections N k I (fun _ => 0))
    ⟨one_mem_flagSemiInv_zero, one_mem_denomBounded _⟩
    (fun x y hx hy => ⟨mul_mem_flagSemiInv_zero hx.1 hy.1, denomBounded_mul hx.2 hy.2⟩)

@[simp] theorem mem_cellSubalg {I : Finset (Equiv.Perm (Fin N))} {x : FlagLoc N k} :
    x ∈ cellSubalg N k I ↔ x ∈ cellSections N k I (fun _ => 0) := Iff.rfl

/-- The Weyl action as a `k`-algebra map. -/
noncomputable def weylAlg (w : Equiv.Perm (Fin N)) : FlagLoc N k →ₐ[k] FlagLoc N k where
  toFun := weylSubst w
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]
    show weylSubst w (algebraMap _ _ (algebraMap k (MvPolynomial (Fin N × Fin N) k) r)) = _
    rw [weylSubst_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]

@[simp] theorem weylAlg_apply (w : Equiv.Perm (Fin N)) (x : FlagLoc N k) :
    weylAlg w x = weylSubst w x := rfl

theorem weylAlg_map_adjoin (w : Equiv.Perm (Fin N)) (S : Set (FlagLoc N k)) :
    (Algebra.adjoin k S).map (weylAlg (k := k) w) = Algebra.adjoin k (weylAlg (k := k) w '' S) :=
  (Algebra.adjoin_image k (weylAlg (k := k) w) S).symm

end GaloisForLFunctions.HTGeometry.BorelWeil
