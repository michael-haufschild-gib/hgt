import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# A non-vacuity certificate for the affine group scheme layer

The group algebra `R[G]` of a finite abelian group `G` is a commutative Hopf algebra which is
finite and free as an `R`-module, so it is an instance of every hypothesis used in
`AffineGroupSchemeCoLie`, `DualCoalgebraFiniteFree` and `CartierDualLieAlgebra`.  Geometrically
`Spec R[G]` is the diagonalisable group scheme `D(G)` — for `G = ℤ/n` this is `μ_n` — whose Cartier
dual is the constant group scheme `G`.

This file records that certificate and shows the augmentation ideal is nontrivial as soon as `G`
is, so the co-Lie module and the Lie algebra of the layer are not studied on an empty class.
-/

namespace GaloisForLFunctions.HTGeometry.GroupAlgebraExample

open MonoidAlgebra Coalgebra AffineGroupScheme

variable (R G : Type*) [CommRing R] [CommGroup G] [Fintype G] [DecidableEq G]

noncomputable instance : Module.Finite R (MonoidAlgebra R G) :=
  Module.Finite.of_basis (MonoidAlgebra.basis G R)

/-- The hypotheses of the affine-group-scheme layer are satisfiable. -/
noncomputable example : Bialgebra R (MonoidAlgebra R G) := inferInstance
example : Module.Free R (MonoidAlgebra R G) := inferInstance
example : Module.Finite R (MonoidAlgebra R G) := inferInstance
noncomputable example : CommRing (MonoidAlgebra R G) := inferInstance

variable {R G}

/-- Group-like elements have counit `1`, so `g - 1` lies in the augmentation ideal. -/
theorem single_sub_one_mem_augIdeal (g : G) :
    (MonoidAlgebra.single g (1 : R) - 1 : MonoidAlgebra R G) ∈ augIdeal R (MonoidAlgebra R G) := by
  rw [mem_augIdeal, map_sub, Bialgebra.counit_one]
  rw [show (Coalgebra.counit (R := R) (MonoidAlgebra.single g (1 : R)))
      = Coalgebra.counit (R := R) (1 : R) from MonoidAlgebra.counit_single g 1]
  simp

/-- For a nontrivial group and a nontrivial base, the augmentation ideal is nonzero: the group
scheme `Spec R[G]` is not the trivial one. -/
theorem augIdeal_ne_bot [Nontrivial R] {g : G} (hg : g ≠ 1) :
    augIdeal R (MonoidAlgebra R G) ≠ ⊥ := by
  intro h
  have hmem := single_sub_one_mem_augIdeal (R := R) g
  rw [h, Submodule.mem_bot] at hmem
  have hne : (MonoidAlgebra.single g (1 : R) : MonoidAlgebra R G) ≠ 1 := by
    intro hcontra
    have hbas : (MonoidAlgebra.basis G R) g = (MonoidAlgebra.basis G R) 1 := by
      rw [MonoidAlgebra.basis_apply, MonoidAlgebra.basis_apply, hcontra, MonoidAlgebra.one_def]
    exact hg ((MonoidAlgebra.basis G R).injective hbas)
  exact hne (by rwa [sub_eq_zero] at hmem)

end GaloisForLFunctions.HTGeometry.GroupAlgebraExample
