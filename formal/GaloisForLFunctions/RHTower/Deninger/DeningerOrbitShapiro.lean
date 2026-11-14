import GaloisForLFunctions.RHTower.Deninger.DeningerPermutationShapiro
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Stabilizer homology for arbitrary orbit modules

The free module on a group orbit is the representation induced from the
trivial representation of a point stabilizer. The orbit--coset bijection
is checked equivariantly, so Shapiro's lemma applies in every degree.
No finiteness or choice of orbit representatives is needed in the statement.

This extends the coset calculation to geometric orbits, the orbit-family
mechanism in Ash--Gunnells, arXiv:2611.03303, Lemma 4.4 and §6.
-/

namespace RHTower

open CategoryTheory Representation MonoidAlgebra MulAction

universe u

variable {k G X : Type u} [CommRing k] [Group G] [MulAction G X]

/-- The orbit--stabilizer equivalence respects the left group actions. -/
theorem deningerCosetOrbit_equivariant (x : X) (g : G)
    (q : G ⧸ stabilizer G x) :
    (orbitEquivQuotientStabilizer G x).symm (g • q) =
      g • (orbitEquivQuotientStabilizer G x).symm q := by
  apply Subtype.ext
  exact ofQuotientStabilizer_smul G x g q

/-- Reindexing the permutation basis from cosets to orbit points. -/
noncomputable def deningerCosetOrbitLinearEquiv (x : X) :
    k[G ⧸ stabilizer G x] ≃ₗ[k] k[orbit G x] :=
  mapDomainLinearEquiv k k (orbitEquivQuotientStabilizer G x).symm

/-- The basis reindexing is an intertwiner, not merely a vector-space equivalence. -/
theorem deningerCosetOrbitLinearEquiv_comm (x : X) (g : G) :
    (deningerCosetOrbitLinearEquiv (k := k) x).toLinearMap ∘ₗ
        ofMulAction k G (G ⧸ stabilizer G x) g =
      ofMulAction k G (orbit G x) g ∘ₗ
        (deningerCosetOrbitLinearEquiv (k := k) x).toLinearMap := by
  refine MonoidAlgebra.lhom_ext' (fun q => LinearMap.ext_ring ?_)
  change deningerCosetOrbitLinearEquiv x
      (ofMulAction k G (G ⧸ stabilizer G x) g (single q 1)) =
    ofMulAction k G (orbit G x) g (deningerCosetOrbitLinearEquiv x (single q 1))
  simp only [deningerCosetOrbitLinearEquiv, ofMulAction_single,
    mapDomainLinearEquiv_single, deningerCosetOrbit_equivariant]

/-- The free module on any orbit is induced from its point stabilizer. -/
noncomputable def deningerIndOrbitIso (x : X) :
    Rep.ind (stabilizer G x).subtype (Rep.trivial k (stabilizer G x) k) ≅
      Rep.ofMulAction k G (orbit G x) :=
  deningerIndTrivialIso (stabilizer G x) ≪≫
    Rep.mkIso (Representation.Equiv.mk (deningerCosetOrbitLinearEquiv x)
      (deningerCosetOrbitLinearEquiv_comm x))

/-- All group-homology degrees of an orbit module reduce to its stabilizer. -/
noncomputable def deningerOrbitShapiro (x : X) (n : ℕ) :
    groupHomology (Rep.ofMulAction k G (orbit G x)) n ≅
      groupHomology (Rep.trivial k (stabilizer G x) k) n := by
  classical
  exact (groupHomology.mapIso (MulEquiv.refl G) (deningerCosetOrbitLinearEquiv x)
      (deningerCosetOrbitLinearEquiv_comm x) n).symm ≪≫
    deningerPermutationShapiro (stabilizer G x) n

end RHTower
