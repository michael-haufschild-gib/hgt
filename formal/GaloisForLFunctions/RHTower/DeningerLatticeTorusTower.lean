import GaloisForLFunctions.HTGeometry.LatticeCoverSystem
import GaloisForLFunctions.HTGeometry.TorusFormalityColimit
import GaloisForLFunctions.RHTower.DeningerCharacterShapeFormality

/-!
# The tower of tori of a unit space

The lattices of a torsion-free abelian group — its finitely generated subgroups — are free of
finite rank, directed under inclusion, and exhaust the group.  Choosing a basis in each turns the
filtration into a family of integer matrices and hence into a tower of tori: the torus of a lattice
is the quotient of its real coordinate space by the integer points, and an inclusion of lattices
induces the covering map.  This is the tower whose colimit carries the shape of the unit space.

The formality comparison of the tower is a quasi-isomorphism of commutative differential graded
algebras: stagewise it is the comparison of the exterior algebra on the dual with the algebra of
periodic forms, and quasi-isomorphisms are preserved by the filtered colimit.

* `RHTower.deningerLatticeBasis` : a basis of each lattice.
* `RHTower.deningerTorusTower` : the tower of tori of the lattice filtration.
* `RHTower.deningerTorusFormality_isQuasiIso` : the formality comparison of that tower.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry Module

section LatticeTower

variable {M : Type*} [AddCommGroup M] [Module.IsTorsionFree ℤ M]

instance : IsDirectedOrder (DeningerLattice M) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := deningerFGSubmodule_directed (M := M) a b
    exact ⟨c, hac, hbc⟩⟩

noncomputable instance : DecidableEq (DeningerLattice M) := Classical.decEq _

/-- Each lattice is finitely generated, hence a finite module. -/
instance deningerLatticeFinite (N : DeningerLattice M) :
    Module.Finite ℤ (N : Submodule ℤ M) :=
  Module.Finite.iff_fg.mpr N.2

/-- Each lattice is free. -/
instance deningerLatticeFreeInstance (N : DeningerLattice M) :
    Module.Free ℤ (N : Submodule ℤ M) :=
  deningerLatticeFree N.2

/-- **A basis of a lattice**, indexed by its rank. -/
noncomputable def deningerLatticeBasis (N : DeningerLattice M) :
    Basis (Fin (Module.finrank ℤ (N : Submodule ℤ M))) ℤ (N : Submodule ℤ M) :=
  Module.finBasis ℤ (N : Submodule ℤ M)

/-- **The tower of tori of the lattice filtration of a torsion-free abelian group.**  The dimension
attached to a lattice is its rank, and the covering map of an inclusion is the transpose of the
inclusion matrix in the chosen bases. -/
noncomputable def deningerTorusTower (𝕜 : Type*) [RCLike 𝕜] :
    TorusCoverSystem 𝕜 (1 : 𝕜) (DeningerLattice M) :=
  torusCoverSystemOfBases 𝕜 (fun N : DeningerLattice M => (N : Submodule ℤ M))
    (fun _ _ h => h) (fun N => Module.finrank ℤ (N : Submodule ℤ M)) deningerLatticeBasis

@[simp] theorem deningerTorusTower_dim (𝕜 : Type*) [RCLike 𝕜] (N : DeningerLattice M) :
    (deningerTorusTower (M := M) 𝕜).dim N = Module.finrank ℤ (N : Submodule ℤ M) := rfl

/-- **The formality comparison of the tower of tori of a unit space is a quasi-isomorphism.**  The
exterior algebra on the colimit of the duals of the lattices computes the cohomology of the tower. -/
theorem deningerTorusFormality_isQuasiIso :
    (colimHom (exteriorSystemHom (deningerTorusTower (M := M) ℝ))
      (torusSystemHom (deningerTorusTower (M := M) ℝ))
      (fun i => torusFormalityHom (1 : ℝ) ((deningerTorusTower (M := M) ℝ).dim i))
      (torusFormality_compat (deningerTorusTower (M := M) ℝ))).IsQuasiIso :=
  torusFormalityColimit_isQuasiIso (deningerTorusTower (M := M) ℝ) one_ne_zero

end LatticeTower

end RHTower
