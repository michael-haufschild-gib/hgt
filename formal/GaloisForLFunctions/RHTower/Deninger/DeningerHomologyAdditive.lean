import GaloisForLFunctions.RHTower.Deninger.DeningerPermutationSum

/-!
# Group homology is additive

The functor sending a representation to its complex of inhomogeneous chains is additive, hence so
is group homology in each degree, and it therefore takes biproducts of representations to
biproducts.

* `deningerChainsFunctor_additive`, `deningerHomologyFunctor_additive` : additivity.
* `deningerHomologyBiprodIso` : `Hₙ(G, A ⊞ B) ≅ Hₙ(G, A) ⊞ Hₙ(G, B)`.
* `deningerHomologyBiprod_obj` : the objects of the homology functor are the homology groups.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Finsupp

universe u

variable (k G : Type u) [CommRing k] [Group G]

instance deningerChainsFunctor_additive : (groupHomology.chainsFunctor k G).Additive where
  map_add {A B} f g := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun x => LinearMap.ext fun a => ?_)
    show (groupHomology.chainsMap (MonoidHom.id G) (f + g)).f n (Finsupp.single x a) =
      ((groupHomology.chainsMap (MonoidHom.id G) f).f n +
        (groupHomology.chainsMap (MonoidHom.id G) g).f n) (Finsupp.single x a)
    rw [groupHomology.chainsMap_f_single]
    show _ = (groupHomology.chainsMap (MonoidHom.id G) f).f n (Finsupp.single x a) +
      (groupHomology.chainsMap (MonoidHom.id G) g).f n (Finsupp.single x a)
    rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single, ← Finsupp.single_add]
    rfl

instance deningerHomologyFunctor_additive (n : ℕ) : (groupHomology.functor k G n).Additive where
  map_add {A B} f g := by
    show groupHomology.map (MonoidHom.id G) (f + g) n =
      groupHomology.map (MonoidHom.id G) f n + groupHomology.map (MonoidHom.id G) g n
    rw [groupHomology.map, groupHomology.map, groupHomology.map,
      show groupHomology.chainsMap (MonoidHom.id G) (f + g) =
        groupHomology.chainsMap (MonoidHom.id G) f +
          groupHomology.chainsMap (MonoidHom.id G) g from
        (groupHomology.chainsFunctor k G).map_add,
      HomologicalComplex.homologyMap_add]
    rfl

variable {k G}

/-- **Group homology takes biproducts to biproducts.**  The inverse is assembled from the images of
the four structure maps, and the two composite identities come from the total identity of the
biproduct together with additivity. -/
noncomputable def deningerHomologyBiprodIso (A B : Rep k G) (n : ℕ) :
    (groupHomology.functor k G n).obj (A ⊞ B) ≅
      (groupHomology.functor k G n).obj A ⊞ (groupHomology.functor k G n).obj B where
  hom := biprod.lift ((groupHomology.functor k G n).map biprod.fst)
    ((groupHomology.functor k G n).map biprod.snd)
  inv := biprod.desc ((groupHomology.functor k G n).map biprod.inl)
    ((groupHomology.functor k G n).map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← (groupHomology.functor k G n).map_comp,
      ← (groupHomology.functor k G n).map_comp, ← Functor.map_add, biprod.total,
      (groupHomology.functor k G n).map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [-groupHomology.functor_map, ← Functor.map_comp]

theorem deningerHomologyBiprod_obj (A : Rep k G) (n : ℕ) :
    (groupHomology.functor k G n).obj A = groupHomology A n := rfl

end RHTower
