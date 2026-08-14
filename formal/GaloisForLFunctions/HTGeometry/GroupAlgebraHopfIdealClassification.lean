import GaloisForLFunctions.HTGeometry.HopfIdealKernel
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Classification of Hopf ideals in group algebras

Every Hopf ideal of `k[M]` is the kernel induced by quotienting `M` by the subgroup of character
relations `m` for which `[m] - 1` belongs to the ideal.  The proof embeds the quotient group
algebra in the original Hopf quotient, using linear independence of distinct group-like elements.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupAlgebraHopfIdealClassification

noncomputable section

variable {k M : Type*} [Field k] [AddCommGroup M]

def monomialUnit (m : M) : (AddMonoidAlgebra k M)ˣ where
  val := AddMonoidAlgebra.single m 1
  inv := AddMonoidAlgebra.single (-m) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

@[simp] theorem monomialUnit_val (m : M) :
    (monomialUnit (k := k) m : AddMonoidAlgebra k M) =
      AddMonoidAlgebra.single m 1 := rfl

def monomialUnitHom : Multiplicative M →* (AddMonoidAlgebra k M)ˣ where
  toFun m := monomialUnit m.toAdd
  map_one' := by
    apply Units.ext
    simp [monomialUnit, AddMonoidAlgebra.one_def]
  map_mul' m n := by
    apply Units.ext
    simp [monomialUnit, AddMonoidAlgebra.single_mul_single]

variable (I : Ideal (AddMonoidAlgebra k M)) [I.IsHopfIdeal k]

def quotientMonomialUnitHom :
    Multiplicative M →* (AddMonoidAlgebra k M ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp monomialUnitHom

def quotientMonomialAddHom :
    M →+ Additive ((AddMonoidAlgebra k M ⧸ I)ˣ) :=
  MonoidHom.toAdditive (quotientMonomialUnitHom I)

def relationSubgroup : AddSubgroup M :=
  AddMonoidHom.ker (quotientMonomialAddHom I)

omit [I.IsHopfIdeal k] in
theorem mem_relationSubgroup_iff (m : M) :
    m ∈ relationSubgroup I ↔
      AddMonoidAlgebra.single m 1 - 1 ∈ I := by
  change quotientMonomialUnitHom I (Multiplicative.ofAdd m) = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk I (AddMonoidAlgebra.single m 1) = 1 ↔ _
  rw [← sub_eq_zero]
  change Ideal.Quotient.mk I (AddMonoidAlgebra.single m 1 - 1) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

def quotientGroupUnitHom :
    Multiplicative (M ⧸ relationSubgroup I) →*
      (AddMonoidAlgebra k M ⧸ I)ˣ :=
  AddMonoidHom.toMultiplicative
    (QuotientAddGroup.kerLift (quotientMonomialAddHom I))

def quotientGroupMonomialHom :
    Multiplicative (M ⧸ relationSubgroup I) →*
      (AddMonoidAlgebra k M ⧸ I) :=
  (Units.coeHom (AddMonoidAlgebra k M ⧸ I)).comp (quotientGroupUnitHom I)

omit [I.IsHopfIdeal k] in
@[simp] theorem quotientGroupMonomialHom_mk (m : M) :
    quotientGroupMonomialHom I
        (Multiplicative.ofAdd (QuotientAddGroup.mk' (relationSubgroup I) m)) =
      Ideal.Quotient.mk I (AddMonoidAlgebra.single m 1) := by
  rfl

omit [I.IsHopfIdeal k] in
theorem quotientGroupMonomialHom_injective :
    Function.Injective (quotientGroupMonomialHom I) := by
  intro a b hab
  have hu : quotientGroupUnitHom I a = quotientGroupUnitHom I b := Units.ext hab
  change a.toAdd = b.toAdd
  apply QuotientAddGroup.kerLift_injective (quotientMonomialAddHom I)
  exact congrArg Multiplicative.toAdd hu

theorem quotientGroupMonomialHom_isGroupLike
    (q : M ⧸ relationSubgroup I) :
    IsGroupLikeElem k
      (quotientGroupMonomialHom I (Multiplicative.ofAdd q)) := by
  obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective (relationSubgroup I) q
  rw [quotientGroupMonomialHom_mk]
  apply IsGroupLikeElem.map (Bialgebra.Quotient.mkBialgHom (R := k) I)
  constructor
  · simp
  · simp [AddMonoidAlgebra.comul_single]

theorem groupLike_family_linearIndependent
    (g : (M ⧸ relationSubgroup I) → (AddMonoidAlgebra k M ⧸ I))
    (hg : ∀ q, IsGroupLikeElem k (g q)) (hinj : Function.Injective g) :
    LinearIndependent k g := by
  have himage : LinearIndepOn k id (g '' (Set.univ : Set (M ⧸ relationSubgroup I))) :=
    linearIndepOn_isGroupLikeElem.mono (by
      rintro x ⟨q, -, rfl⟩
      exact hg q)
  have hcomp := himage.comp_of_image (s := Set.univ) (f := g) hinj.injOn
  have hfull := hcomp.comp
    (fun q : M ⧸ relationSubgroup I =>
      (⟨q, Set.mem_univ q⟩ : (Set.univ : Set (M ⧸ relationSubgroup I))))
    (fun _ _ h => congrArg Subtype.val h)
  have heq : ((fun x : (Set.univ : Set (M ⧸ relationSubgroup I)) =>
      (id ∘ g) x.1) ∘
      (fun q : M ⧸ relationSubgroup I =>
        (⟨q, Set.mem_univ q⟩ : (Set.univ : Set (M ⧸ relationSubgroup I))))) = g := by
    funext q
    rfl
  rw [heq] at hfull
  exact hfull

def quotientGroupAlgHom :
    AddMonoidAlgebra k (M ⧸ relationSubgroup I) →ₐ[k]
      (AddMonoidAlgebra k M ⧸ I) :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k M ⧸ I)
    (M ⧸ relationSubgroup I) (quotientGroupMonomialHom I)

omit [I.IsHopfIdeal k] in
@[simp] theorem quotientGroupAlgHom_single (q : M ⧸ relationSubgroup I) (c : k) :
    quotientGroupAlgHom I (AddMonoidAlgebra.single q c) =
      c • quotientGroupMonomialHom I (Multiplicative.ofAdd q) := by
  simp [quotientGroupAlgHom]

theorem quotientGroupAlgHom_injective : Function.Injective (quotientGroupAlgHom I) := by
  let g : (M ⧸ relationSubgroup I) → (AddMonoidAlgebra k M ⧸ I) :=
    fun q => quotientGroupMonomialHom I (Multiplicative.ofAdd q)
  have hgLI : LinearIndependent k g := groupLike_family_linearIndependent I g
    (fun q => quotientGroupMonomialHom_isGroupLike I q)
    (fun _ _ h => congrArg Multiplicative.toAdd
      (quotientGroupMonomialHom_injective I h))
  have htotal : (Finsupp.linearCombination k g).comp
      (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap =
      (quotientGroupAlgHom I).toLinearMap := by
    apply LinearMap.ext
    intro p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single q c => simp [g]
  intro p q hpq
  apply (AddMonoidAlgebra.coeffLinearEquiv k).injective
  apply (linearIndependent_iff_injective_finsuppLinearCombination.mp hgLI)
  have hp := DFunLike.congr_fun htotal p
  have hq := DFunLike.congr_fun htotal q
  change Finsupp.linearCombination k g ((AddMonoidAlgebra.coeffLinearEquiv k) p) =
    quotientGroupAlgHom I p at hp
  change Finsupp.linearCombination k g ((AddMonoidAlgebra.coeffLinearEquiv k) q) =
    quotientGroupAlgHom I q at hq
  rw [hp, hq]
  exact hpq

def quotientGroupMap :
    AddMonoidAlgebra k M →ₐc[k]
      AddMonoidAlgebra k (M ⧸ relationSubgroup I) :=
  AddMonoidAlgebra.mapDomainBialgHom k (QuotientAddGroup.mk' (relationSubgroup I))

omit [I.IsHopfIdeal k] in
theorem quotientGroupAlgHom_comp_quotientGroupMap :
    (quotientGroupAlgHom I).comp (quotientGroupMap I).toAlgHom =
      Ideal.Quotient.mkₐ k I := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    have hmap : quotientGroupMap I (AddMonoidAlgebra.single m 1) =
        AddMonoidAlgebra.single (QuotientAddGroup.mk' (relationSubgroup I) m) 1 := by
      change AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' (relationSubgroup I))
        (AddMonoidAlgebra.single m 1) = _
      rw [AddMonoidAlgebra.mapDomain_single]
    change quotientGroupAlgHom I
        (quotientGroupMap I (AddMonoidAlgebra.single m 1)) =
      Ideal.Quotient.mk I (AddMonoidAlgebra.single m 1)
    rw [hmap, quotientGroupAlgHom_single]
    simp only [one_smul]
    simpa only [QuotientAddGroup.mk'_apply] using quotientGroupMonomialHom_mk I m
  · ext

/-- Hopf ideals in a group algebra are exactly kernels induced by quotienting the grading group
by the subgroup of character relations. -/
theorem eq_ker_quotientGroupMap :
    I = RingHom.ker (quotientGroupMap I).toAlgHom.toRingHom := by
  apply le_antisymm
  · intro p hpI
    have hcomp := DFunLike.congr_fun (quotientGroupAlgHom_comp_quotientGroupMap I) p
    apply quotientGroupAlgHom_injective I
    calc
      quotientGroupAlgHom I (quotientGroupMap I p) = Ideal.Quotient.mk I p := hcomp
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpI
      _ = quotientGroupAlgHom I 0 := (map_zero _).symm
  · intro p hp
    have hcomp := DFunLike.congr_fun (quotientGroupAlgHom_comp_quotientGroupMap I) p
    change quotientGroupMap I p = 0 at hp
    change quotientGroupAlgHom I (quotientGroupMap I p) = Ideal.Quotient.mk I p at hcomp
    rw [hp, map_zero] at hcomp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hcomp.symm

end
end GroupAlgebraHopfIdealClassification
end GaloisForLFunctions.HTGeometry
