import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualQuadraticSourceNorm
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicLocalArtin
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualQuadraticSource
import GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.NormRestriction
import AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Actual quadratic-source dyadic Artin law

Let `S = ℚ(√41) ⊂ K₂` and let `u` be the selected Q8 unit. The upper dyadic
Artin symbols kill `u`, while `N_{K₂/S}(u) = -1`. Taking the product over all
places above a dyadic source place and applying local norm--restriction proves
the genuine source law `Artin_v(-1) = 1`. No uniqueness of an upper place is
assumed.
-/

namespace RHTower

noncomputable section

open scoped NumberField TensorProduct BigOperators IsMulCommutative
open GlobalClassFieldTheory.Reciprocity
open GaloisForLFunctions
open IsDedekindDomain
open AlgebraicNumberTheory.Valuations

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "S" => q8BiquadQuadraticSourceField

local instance deningerQ8ActualQuadraticSourceArtinLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance deningerQ8ActualQuadraticSourceArtinLocalInst2 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst3 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst4 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst5 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst6 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst7 : FiniteDimensional S K2 := by infer_instance
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst8 : FiniteDimensional S K3 :=
  FiniteDimensional.trans S K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst9 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst10 : NumberField S := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst11 : NumberField K2 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst12 : NumberField K3 := NumberField.mk
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst13 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst14 : IsGalois S K3 :=
  IsGalois.tower_top_of_isGalois ℚ S K3

theorem q8BiquadQuadraticSource_top_finrank :
    Module.finrank S K3 = 4 := by
  have htower := Module.finrank_mul_finrank S K2 K3
  rw [q8BiquadQuadraticSourceField_top_finrank,
    deningerQ8RootNumberNegOneTopField_finrank_over_second] at htower
  omega

noncomputable def q8QuadraticSourceRestrictHom :
    Gal(K3/S) →* deningerQ8ActualCyclicSubgroup where
  toFun σ := ⟨σ.restrictScalars ℚ, by
    rw [deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY,
      MulAction.mem_stabilizer_iff]
    let yS : S :=
      ⟨deningerQ8RootNumberNegOneSecondQuadraticRoot,
        IntermediateField.subset_adjoin ℚ
          {deningerQ8RootNumberNegOneSecondQuadraticRoot}
          (Set.mem_singleton _)⟩
    change σ (algebraMap S K3 yS) = algebraMap S K3 yS
    exact σ.commutes yS⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    rfl

theorem q8QuadraticSourceRestrictHom_injective :
    Function.Injective q8QuadraticSourceRestrictHom := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  have hx := DFunLike.congr_fun
    (congrArg Subtype.val h) x
  exact hx

theorem q8QuadraticSourceRestrictHom_surjective :
    Function.Surjective q8QuadraticSourceRestrictHom := by
  exact ((Nat.bijective_iff_injective_and_card
    q8QuadraticSourceRestrictHom).2 ⟨
      q8QuadraticSourceRestrictHom_injective, by
        rw [IsGalois.card_aut_eq_finrank,
          q8BiquadQuadraticSource_top_finrank,
          deningerQ8ActualCyclicSubgroup_natCard]⟩).2

noncomputable def q8QuadraticSourceGalEquivCyclicSubgroup :
    Gal(K3/S) ≃* deningerQ8ActualCyclicSubgroup :=
  MulEquiv.ofBijective q8QuadraticSourceRestrictHom
    ⟨q8QuadraticSourceRestrictHom_injective,
      q8QuadraticSourceRestrictHom_surjective⟩

noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst15 : IsCyclic deningerQ8ActualCyclicSubgroup := by
  have hq8 : IsCyclic q8CyclicSubgroup :=
    (MulEquiv.isCyclic q8CyclicSourceEquiv).mp inferInstance
  exact (MulEquiv.isCyclic deningerQ8ActualCyclicSubgroupEquiv).mpr hq8

noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst16 : IsCyclic Gal(K3/S) :=
  (MulEquiv.isCyclic q8QuadraticSourceGalEquivCyclicSubgroup).mpr
    (inferInstance : IsCyclic deningerQ8ActualCyclicSubgroup)

noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst17 : IsAbelianGalois S K3 :=
  IsAbelianGalois.of_isCyclic S K3

noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst18 : IsGalois K2 K3 :=
  IsGalois.tower_top_of_isGalois ℚ K2 K3
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst19 : IsCyclic Gal(K3/K2) := by
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank,
    deningerQ8RootNumberNegOneTopField_finrank_over_second]
noncomputable local instance deningerQ8ActualQuadraticSourceArtinLocalInst20 : IsAbelianGalois K2 K3 :=
  IsAbelianGalois.of_isCyclic K2 K3

noncomputable def q8BiquadTwoAdicUUnit : K2ˣ where
  val := q8BiquadTwoAdicU
  inv := (q8BiquadTwoAdicU : K2) - 1
  val_inv := by
    have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
    change (q8BiquadTwoAdicU : K2) ^ 2 = (q8BiquadTwoAdicU : K2) + 1 at hu
    rw [mul_sub, mul_one, ← pow_two, hu]
    simp
  inv_val := by
    have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
    change (q8BiquadTwoAdicU : K2) ^ 2 = (q8BiquadTwoAdicU : K2) + 1 at hu
    rw [sub_mul, one_mul, ← pow_two, hu]
    simp

theorem q8BiquadTwoAdicUUnit_quadraticSource_norm :
    Units.map (Algebra.norm S) q8BiquadTwoAdicUUnit = (-1 : Sˣ) := by
  apply Units.ext
  exact q8BiquadTwoAdicU_quadraticSource_norm

theorem two_mem_upper_of_finitePlaceBelow
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (W : HeightOneSpectrum (𝓞 K2))
    (hW : finitePlaceBelow (K := S) W = v) :
    (2 : 𝓞 K2) ∈ W.asIdeal := by
  have hv' : (2 : 𝓞 S) ∈
      (finitePlaceBelow (K := S) W).asIdeal := by
    rw [hW]
    exact hv
  exact hv'

theorem q8BiquadTwoAdicUUnit_finiteComponent
    (place : NumberField.FinitePlace K2) :
    IdeleGroup.finiteComponent place.maximalIdeal
        (IdeleGroup.principalIdele K2 q8BiquadTwoAdicUUnit) =
      q8BiquadTwoAdicUCompletionUnit place := by
  apply Units.ext
  rfl

set_option maxHeartbeats 800000 in
theorem q8QuadraticSourceArtin_localNorm_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal)
    (place : NumberField.FinitePlace K2)
    (hW : finitePlaceBelow (K := S) place.maximalIdeal = v) :
    letI : Algebra (v.adicCompletion S) (place.maximalIdeal.adicCompletion K2) :=
      (finitePlaceAdicCompletionMap S K2 v ⟨place.maximalIdeal, hW⟩).toAlgebra
    chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (LocalFieldTheory.normUnits (v.adicCompletion S)
          (place.maximalIdeal.adicCompletion K2)
          (q8BiquadTwoAdicUCompletionUnit place)) = 1 := by
  letI : Algebra (v.adicCompletion S)
      (place.maximalIdeal.adicCompletion K2) :=
    (finitePlaceAdicCompletionMap S K2 v
      ⟨place.maximalIdeal, hW⟩).toAlgebra
  have hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal := by
    exact two_mem_upper_of_finitePlaceBelow v hv place.maximalIdeal hW
  have hupper := q8BiquadTwoAdicU_chosenFinitePlaceArtin_eq_one place hplace
  let res : Gal(K3/K2) →* Gal(K3/S) :=
    (AlgEquiv.restrictNormalHom K3).comp (AlgEquiv.restrictScalarsHom S)
  have hnat := DFunLike.congr_fun
    (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
      (K := S) (L := K3) (K' := K2) (L' := K3)
      v place.maximalIdeal hW)
      (q8BiquadTwoAdicUCompletionUnit place)
  change
    res
        (chosenFinitePlaceArtinMonoidHom (K := K2) (L := K3)
          place.maximalIdeal (q8BiquadTwoAdicUCompletionUnit place)) =
      chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (LocalFieldTheory.normUnits (v.adicCompletion S)
          (place.maximalIdeal.adicCompletion K2)
          (q8BiquadTwoAdicUCompletionUnit place))
    at hnat
  calc
    chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (LocalFieldTheory.normUnits (v.adicCompletion S)
          (place.maximalIdeal.adicCompletion K2)
          (q8BiquadTwoAdicUCompletionUnit place)) =
        res
          (chosenFinitePlaceArtinMonoidHom (K := K2) (L := K3)
            place.maximalIdeal (q8BiquadTwoAdicUCompletionUnit place)) := hnat.symm
    _ = res 1 := congrArg res hupper
    _ = 1 := res.map_one

noncomputable def q8FinitePlacesAboveEquiv
    (v : HeightOneSpectrum (𝓞 S)) :
    {place : NumberField.FinitePlace K2 //
        finitePlaceBelow (K := S) place.maximalIdeal = v} ≃
      {W : HeightOneSpectrum (𝓞 K2) //
        finitePlaceBelow (K := S) W = v} where
  toFun place := ⟨place.1.maximalIdeal, place.2⟩
  invFun W := ⟨NumberField.FinitePlace.mk W.1, by
    simpa only [NumberField.FinitePlace.maximalIdeal_mk] using W.2⟩
  left_inv place := by
    apply Subtype.ext
    exact NumberField.FinitePlace.mk_maximalIdeal place.1
  right_inv W := by
    apply Subtype.ext
    exact NumberField.FinitePlace.maximalIdeal_mk W.1

noncomputable def q8QuadraticSourceNegOneCompletionUnit
    (v : HeightOneSpectrum (𝓞 S)) : (v.adicCompletion S)ˣ :=
  IdeleGroup.finiteComponent v
    (IdeleGroup.principalIdele S (-1 : Sˣ))

set_option maxHeartbeats 1600000 in
theorem q8QuadraticSourceNegOne_chosenFinitePlaceArtin_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
      (q8QuadraticSourceNegOneCompletionUnit v) = 1 := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv S v
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  letI := completionTensorDecomposition_extensionFintype
    (K := S) (L := K2) vK hvK
  let eAbove := finitePlaceExtensionEquivAbove (K := S) (L := K2) v
  let Above := {W : HeightOneSpectrum (𝓞 K2) //
    finitePlaceBelow (K := S) W = v}
  letI : Fintype Above := Fintype.ofEquiv
    (AbsoluteValueExtension vK K2) eAbove
  let PlaceAbove := {place : NumberField.FinitePlace K2 //
    finitePlaceBelow (K := S) place.maximalIdeal = v}
  let ePlace : PlaceAbove ≃ Above := q8FinitePlacesAboveEquiv v
  letI : Fintype PlaceAbove := Fintype.ofEquiv Above ePlace.symm
  letI : ∀ W : Above,
      Algebra (v.adicCompletion S) (W.1.adicCompletion K2) :=
    fun W => (finitePlaceAdicCompletionMap S K2 v W).toAlgebra
  let a := IdeleGroup.principalIdele K2 q8BiquadTwoAdicUUnit
  let fW (W : Above) : (v.adicCompletion S)ˣ :=
    LocalFieldTheory.normUnits (v.adicCompletion S) (W.1.adicCompletion K2)
      (IdeleGroup.finiteComponent W.1 a)
  have hnorm : IdeleGroup.norm S K2 a =
      IdeleGroup.principalIdele S (-1 : Sˣ) := by
    rw [show a = IdeleGroup.principalIdele K2 q8BiquadTwoAdicUUnit by rfl,
      IdeleGroup.norm_principalIdele,
      q8BiquadTwoAdicUUnit_quadraticSource_norm]
  have hprod := IdeleGroup.finiteComponent_norm_eq_prod S K2 v a
  rw [hnorm] at hprod
  have hreindex :
      (∏ place : PlaceAbove, fW (ePlace place)) = ∏ W : Above, fW W := by
    exact Fintype.prod_equiv ePlace
      (fun place : PlaceAbove => fW (ePlace place)) fW (fun _ => rfl)
  have hprodPlace : q8QuadraticSourceNegOneCompletionUnit v =
      ∏ place : PlaceAbove, fW (ePlace place) := by
    exact hprod.trans hreindex.symm
  have hfactor (place : PlaceAbove) :
      chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (fW (ePlace place)) = 1 := by
    have hlocal := q8QuadraticSourceArtin_localNorm_eq_one
      v hv place.1 place.2
    rw [← q8BiquadTwoAdicUUnit_finiteComponent place.1] at hlocal
    exact hlocal
  calc
    chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (q8QuadraticSourceNegOneCompletionUnit v) =
      chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
        (∏ place : PlaceAbove, fW (ePlace place)) := congrArg _ hprodPlace
    _ = ∏ place : PlaceAbove,
        chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v
          (fW (ePlace place)) := by rw [map_prod]
    _ = 1 := Finset.prod_eq_one fun place _ => hfactor place

/-- The coefficient-faithful quartic character on the actual quadratic source
Galois group.  It is transported from the same `C₄` character inducing the
literal two-dimensional Q8 Artin representation. -/
def q8QuadraticSourceCharacter :
    GaloisForLFunctions.LinearCharacter Gal(K3/S) :=
  deningerQ8ActualCyclicSubgroupCharacter.comp
    q8QuadraticSourceGalEquivCyclicSubgroup.toMonoidHom

/-- Genuine local source character: local Artin reciprocity followed by the
coefficient-faithful quartic source channel. -/
noncomputable def q8QuadraticSourceFinitePlaceCharacter
    (v : HeightOneSpectrum (𝓞 S)) :
    (v.adicCompletion S)ˣ →* ℂˣ :=
  q8QuadraticSourceCharacter.comp
    (chosenFinitePlaceArtinMonoidHom (K := S) (L := K3) v)

/-- The actual dyadic source character is even.  This is the arithmetic bit
which distinguishes the two conductor-eight quadratic angular candidates. -/
theorem q8QuadraticSourceFinitePlaceCharacter_neg_one_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    q8QuadraticSourceFinitePlaceCharacter v
      (q8QuadraticSourceNegOneCompletionUnit v) = 1 := by
  rw [q8QuadraticSourceFinitePlaceCharacter, MonoidHom.comp_apply,
    q8QuadraticSourceNegOne_chosenFinitePlaceArtin_eq_one v hv, map_one]

end
end RHTower
