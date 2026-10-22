import GaloisForLFunctions.RHTower.Deninger.DeningerCoinvariantsTranslation
import GaloisForLFunctions.RHTower.Deninger.DeningerCyclicHomology

/-!
# The first homology of an infinite cyclic group

The two term resolution of the trivial representation by the regular representation has boundary
translation by the generator minus the identity, which dies on coinvariants.  The connecting map of
its long exact sequence is therefore injective and surjective, so the first homology of an infinite
cyclic group is the zeroth homology of its regular representation.

* `deningerZ_coinvariants_boundary` : the boundary dies on coinvariants.
* `deningerZ_H1Iso` : the first homology of an infinite cyclic group.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Rep Representation

universe u

variable {Z : Type u} [Group Z] (e : Z ≃* Multiplicative ℤ) (k : Type u) [CommRing k]

include e in
theorem deningerZ_hcomm (a b : Z) : a * b = b * a :=
  e.injective (by rw [map_mul, map_mul, mul_comm])

/-- **The boundary dies on coinvariants.** -/
theorem deningerZ_coinvariants_boundary :
    (Rep.coinvariantsFunctor k Z).map (deningerZBoundary e k) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using Representation.Coinvariants.induction_on with
  | h y =>
    show Representation.Coinvariants.map _ _ (deningerZBoundary e k).hom
      (Representation.Coinvariants.mk _ y) = 0
    rw [Representation.Coinvariants.map_mk]
    obtain ⟨y', rfl⟩ := (MonoidAlgebra.coeffLinearEquiv k).symm.surjective y
    induction y' using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
    | single a c =>
      have hsmul : ∀ x : Z, (c • MonoidAlgebra.single x (1 : k) : MonoidAlgebra k Z) =
          MonoidAlgebra.single x c := by
        intro x
        simp
      show Representation.Coinvariants.mk _
        ((deningerZBoundary e k).hom (MonoidAlgebra.single a c)) = 0
      rw [deningerZBoundary_single, smul_sub, hsmul, hsmul, map_sub, sub_eq_zero,
        show MonoidAlgebra.single (a * deningerZGen e) c =
          Representation.ofMulAction k Z Z (deningerZGen e) (MonoidAlgebra.single a c) by
          rw [Representation.ofMulAction_single, smul_eq_mul, deningerZ_hcomm e],
        Representation.Coinvariants.mk_self_apply]

variable [DecidableEq Z]

/-- **The first homology of an infinite cyclic group** is the zeroth homology of its regular
representation. -/
noncomputable def deningerZ_H1Iso :
    groupHomology (Rep.trivial k Z k) 1 ≅ groupHomology (Rep.ofMulAction k Z Z) 0 := by
  have hX := deningerZShortComplex_shortExact e k
  have hg : (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).g = 0 := by
    have hnat := groupHomology.map_id_comp_H0Iso_hom (deningerZBoundary e k)
    rw [deningerZ_coinvariants_boundary, comp_zero] at hnat
    refine (cancel_mono (groupHomology.H0Iso (deningerZShortComplex e k).X₂).hom).1 ?_
    exact hnat.trans zero_comp.symm
  have hmono : Mono (groupHomology.mapShortComplex₃ hX (i := 1) (j := 0) rfl).g :=
    (groupHomology.mapShortComplex₃_exact hX rfl).mono_g
      ((deningerIsZero_leftRegular Z k 0).eq_zero_of_src _)
  have hepi : Epi (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).f :=
    (groupHomology.mapShortComplex₁_exact hX rfl).epi_f hg
  have hepi' : Epi (groupHomology.mapShortComplex₃ hX (i := 1) (j := 0) rfl).g := hepi
  have hiso := @isIso_of_mono_of_epi (ModuleCat k) _ _ _ _
    (groupHomology.mapShortComplex₃ hX (i := 1) (j := 0) rfl).g hmono hepi'
  exact @asIso _ _ _ _ _ hiso

end RHTower
