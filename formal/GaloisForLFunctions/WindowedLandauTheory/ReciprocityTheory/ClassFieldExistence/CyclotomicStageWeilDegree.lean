import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueFrobeniusOrder
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteAbelianRestrictions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilGroupAtFinitePlace
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfACyclotomicCharacterIsAHeckeLSeries
import GaloisForLFunctions.RHTower.Artin.IdealsWithArtinSymbolInASubgroupOfACyclotomicExtension

/-! Every positive integer occurs as the order of the restricted
arithmetic Frobenius in an unramified finite cyclotomic stage. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem exists_unramified_cyclotomicStage_withRoots (h : IsPlaceOver A v)
    (n : ℕ) (hn : 0 < n) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      letI : Fintype Gal(L/K) := Fintype.ofFinite _
      letI : CommGroup Gal(L/K) :=
        { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
      IsUnramifiedPrime K L Gal(L/K) v ∧
        orderOf (AlgEquiv.restrictNormalHom L (frob h : Gal(Ω/K))) = n ∧
        HasEnoughRootsOfUnity L (normV v ^ n - 1) := by
  let q := Ideal.absNorm v.asIdeal
  let m := q ^ n - 1
  have hq : 1 < q := one_lt_normV v
  have hqn : 1 < q ^ n := one_lt_pow₀ hq hn.ne'
  have hm : 0 < m := Nat.sub_pos_of_lt hqn
  letI : NeZero m := ⟨hm.ne'⟩
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  letI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  let L := K⟮ζ⟯
  let e := AdjoinSimple.gen K ζ
  letI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsCyclotomicExtension {m} K L := hζ.intermediateField_adjoin_isCyclotomicExtension K
  letI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  let eO : 𝓞 L := ⟨e, (IsPrimitiveRoot.of_map_of_injective (f := L.val) hζ L.val.injective).isIntegral hm⟩
  have heO : IsPrimitiveRoot eO m :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L)
      (IsPrimitiveRoot.of_map_of_injective (f := L.val) hζ L.val.injective)
      (IsFractionRing.injective (𝓞 L) L)
  have ht : K⟮(eO : L)⟯ = ⊤ := by
    apply lift_injective
    rw [lift_adjoin_simple, lift_top]
    rfl
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hi := cyclotomicCharacter_injective (G := Gal(L/K)) heO ht
  letI : IsAbelianGalois K L := {
    is_comm.comm s t := hi (by rw [map_mul, map_mul, mul_comm]) }
  letI : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  have hmv : (m : 𝓞 K) ∉ v.asIdeal := by
    intro hm0
    letI := v.isMaximal
    let Q := Ideal.Quotient.mk v.asIdeal
    have hq0 : Q (q : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.absNorm_mem v.asIdeal)
    have h0 : Q (m : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm0
    have heq : (q : 𝓞 K) ^ n = (m : 𝓞 K) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hqn.le).symm
    have hQ := congrArg Q heq
    rw [map_pow, hq0, zero_pow hn.ne', map_add, h0, map_one, zero_add] at hQ
    exact zero_ne_one hQ
  have hu := isUnramifiedPrime_of_cyclotomicCharacter_injective K L heO hi hmv
  have hR : HasEnoughRootsOfUnity L (normV v ^ n - 1) := by
    change HasEnoughRootsOfUnity L m
    exact ⟨⟨e, IsPrimitiveRoot.of_map_of_injective (f := L.val) hζ L.val.injective⟩, inferInstance⟩
  refine ⟨⟨L, inferInstance, inferInstance⟩, hu, ?_, hR⟩
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI := w.isMaximal
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver A h
  let σ := AlgEquiv.restrictNormalHom L (frob h : Gal(Ω/K))
  have hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal := restrictNormalHom_isArithFrobAt A h (isFrob_frob (h := h))
  have hh := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal)
  rw [hu w.asIdeal inferInstance inferInstance, Subgroup.mem_bot,
    arithFrobAt_eq_frobeniusElement hu w.asIdeal] at hh
  have heq : σ = frobeniusElement K L Gal(L/K) v := mul_inv_eq_one.mp hh
  change orderOf σ = n
  rw [heq, ← orderOf_injective _ hi]
  exact orderOf_unit_of_val_eq_natCast_pow_sub_one hq hn _
    (coe_cyclotomicCharacter_frobeniusElement K L heO v hmv)

theorem exists_unramified_cyclotomicStage_frobenius_order (h : IsPlaceOver A v)
    (n : ℕ) (hn : 0 < n) :
    ∃ V : finiteAbelianExtensions K Ω,
      let L := (V : IntermediateField K Ω)
      letI := V.2.1
      letI := V.2.2
      letI : NumberField L := NumberField.of_module_finite K L
      letI : Fintype Gal(L/K) := Fintype.ofFinite _
      letI : CommGroup Gal(L/K) :=
        { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }
      IsUnramifiedPrime K L Gal(L/K) v ∧
        orderOf (AlgEquiv.restrictNormalHom L (frob h : Gal(Ω/K))) = n := by
  obtain ⟨V, hU, hV, -⟩ := exists_unramified_cyclotomicStage_withRoots K Ω h n hn
  exact ⟨V, hU, hV⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_unramified_cyclotomicStage_frobenius_order

#print axioms GlobalTheory.Reciprocity.exists_unramified_cyclotomicStage_withRoots
