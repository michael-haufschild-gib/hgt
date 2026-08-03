import GaloisForLFunctions.RHTower.DeningerH1Cyclic

/-!
# The zeroth homology of the regular representation

The coinvariants of the regular representation are the ground ring, by the augmentation: every basis
vector is a translate of the one at the identity, and the augmentation is constant on translates.

* `deningerRegularCoinvariantsEquiv` : the coinvariants of the regular representation.
* `deningerRegularH0Iso` : its zeroth homology.
-/

namespace RHTower

open CategoryTheory Rep Representation

universe u

variable {G : Type u} [Group G] (k : Type u) [CommRing k]

/-- **The coinvariants of the regular representation are the ground ring.** -/
noncomputable def deningerRegularCoinvariantsEquiv :
    Coinvariants (Representation.ofMulAction k G G) ≃ₗ[k] k := by
  refine LinearEquiv.ofLinear
    (Representation.Coinvariants.lift _ (deningerZAug (Z := G) k).hom.toLinearMap
      (fun g => ?_))
    ((Representation.Coinvariants.mk _).comp
      ((MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lsingle (1 : G))) ?_ ?_
  · refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    show (deningerZAug (Z := G) k).hom
        (Representation.ofMulAction k G G g (MonoidAlgebra.single x (1 : k))) =
      (deningerZAug (Z := G) k).hom (MonoidAlgebra.single x (1 : k))
    rw [Representation.ofMulAction_single, deningerZAug_single, deningerZAug_single]
  · refine LinearMap.ext fun c => ?_
    show (deningerZAug (Z := G) k).hom (MonoidAlgebra.single (1 : G) c) = c
    rw [deningerZAug_single]
  · have key : ∀ w : MonoidAlgebra k G,
        Representation.Coinvariants.mk (Representation.ofMulAction k G G)
            (MonoidAlgebra.single (1 : G)
              ((deningerZAug (Z := G) k).hom w)) =
          Representation.Coinvariants.mk (Representation.ofMulAction k G G) w := by
      have hcomp : (Representation.Coinvariants.mk (Representation.ofMulAction k G G) ∘ₗ
            ((MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lsingle (1 : G))) ∘ₗ
              (deningerZAug (Z := G) k).hom.toLinearMap =
          Representation.Coinvariants.mk (Representation.ofMulAction k G G) := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        show Representation.Coinvariants.mk _ (MonoidAlgebra.single (1 : G)
            ((deningerZAug (Z := G) k).hom (MonoidAlgebra.single x (1 : k)))) =
          Representation.Coinvariants.mk _ (MonoidAlgebra.single x (1 : k))
        rw [deningerZAug_single,
          show MonoidAlgebra.single x (1 : k) =
            Representation.ofMulAction k G G x (MonoidAlgebra.single (1 : G) (1 : k)) by
            rw [Representation.ofMulAction_single, smul_eq_mul, mul_one],
          Representation.Coinvariants.mk_self_apply]
      exact fun w => DFunLike.congr_fun hcomp w
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    exact key w

/-- **The zeroth homology of the regular representation is the ground ring.** -/
noncomputable def deningerRegularH0Iso :
    groupHomology (Rep.ofMulAction k G G) 0 ≅ ModuleCat.of k k :=
  groupHomology.H0Iso _ ≪≫ (deningerRegularCoinvariantsEquiv k).toModuleIso

end RHTower
