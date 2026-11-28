import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.WeilCharacterWithRootsOfUnity
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SmoothWeilCharacterCyclicDescent
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeOrderAbelianQuotient
import Mathlib.NumberTheory.Cyclotomic.Gal

/-! A finite-exponent smooth Weil character descends through global
abelianization. A cyclotomic extension supplies roots of unity, then
successive prime-degree base changes descend the character. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

private theorem finite_exponent_weilCharacter_of_abelian_root_extension
    {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] (d : ℕ) :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      (B : IntermediateField K Ω) [FiniteDimensional K B] [IsAbelianGalois K B]
      [HasEnoughRootsOfUnity B n], Module.finrank K B = d →
      ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (ξ : Weil h →* H),
        (∀ s, ξ s ^ n = 1) → IsOpen {s : Ine (F := K) A | ξ (ineIncl h s) = 1} →
        ∀ s : Weil h, toMaxAb K Ω (s : Gal(Ω/K)) = 1 → ξ s = 1 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro K Ω _ _ _ _ _ B _ _ _ hd A v h ξ hpow hopen s hs
    classical
    by_cases hb : B = ⊥
    · let e : B ≃ₐ[K] K := (IntermediateField.equivOfEq hb).trans (IntermediateField.botEquiv K Ω)
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot B n
      letI : HasEnoughRootsOfUnity K n :=
        ⟨⟨e ζ, hζ.map_of_injective e.injective⟩, rootsOfUnity.isCyclic K n⟩
      exact finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one_of_rootsOfUnity K Ω h ξ hpow hopen hs
    · let G := Gal(B/K)
      letI : CommGroup G :=
        { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }
      letI : Finite (Subgroup G) :=
        Finite.of_injective (fun N : Subgroup G => (N : Set G)) SetLike.coe_injective
      have hbot : (⊥ : Subgroup G) ≠ ⊤ := by
        intro hb'
        apply hb
        have he : Module.finrank K B = 1 := by
          rw [← IsGalois.card_aut_eq_finrank]
          haveI : Subsingleton G := ⟨fun a b => by
            have h₀ (x : G) : x = 1 := Subgroup.mem_bot.mp (hb'.symm ▸ Subgroup.mem_top x)
            exact (h₀ a).trans (h₀ b).symm⟩
          exact Nat.card_unique
        apply le_antisymm _ bot_le
        exact (IntermediateField.eq_of_le_of_finrank_eq (F := ⊥) (E := B) bot_le
          (IntermediateField.finrank_bot.trans he.symm)).ge
      obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup G)).resolve_left hbot
      let E₀ := fixedField N
      let E := IntermediateField.lift E₀
      let eE := IntermediateField.liftAlgEquiv E₀
      letI : FiniteDimensional K E := FiniteDimensional.of_injective eE.symm.toLinearMap eE.symm.injective
      letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom
        (IntermediateField.inclusion (show E ≤ B from lift_le E₀))
      letI : NumberField E := NumberField.of_module_finite K E
      letI : IsAlgClosure E Ω :=
        ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
      let Q := IntermediateField.extendScalars (show E ≤ B from lift_le E₀)
      letI : Algebra K Q := (inferInstance : Algebra K B)
      letI : IsScalarTower K E Q := IsScalarTower.of_algebraMap_eq fun _ => rfl
      letI : FiniteDimensional K Q := inferInstanceAs (FiniteDimensional K B)
      letI : IsAbelianGalois K Q := inferInstanceAs (IsAbelianGalois K B)
      letI : FiniteDimensional E Q := FiniteDimensional.right K E Q
      letI : IsAbelianGalois E Q := IsAbelianGalois.tower_top K E Q
      letI : HasEnoughRootsOfUnity Q n := inferInstanceAs (HasEnoughRootsOfUnity B n)
      have hp := prime_card_quotient_of_isCoatom N hN
      have he : Nat.card Gal(E/K) = Nat.card (G ⧸ N) :=
        Nat.card_congr (eE.autCongr.symm.trans (IsGalois.normalAutEquivQuotient N).symm).toEquiv
      letI : Fact (Nat.card (G ⧸ N)).Prime := ⟨hp⟩
      letI : IsCyclic Gal(E/K) := isCyclic_of_prime_card he
      have he' : 1 < Module.finrank K E := by
        rw [← IsGalois.card_aut_eq_finrank, he]
        exact hp.one_lt
      have hlt : Module.finrank E Q < d := by
        letI : Module.Free E Q := Module.Free.of_divisionRing E Q
        have hd' : Module.finrank K E * Module.finrank E Q = d :=
          (Module.finrank_mul_finrank K E Q).trans hd
        rw [← hd']
        simpa only [one_mul] using
          Nat.mul_lt_mul_of_pos_right he' (Module.finrank_pos : 0 < Module.finrank E Q)
      apply weilCharacter_eq_one_of_toMaxAb_eq_one_of_cyclic_descent K Ω E h ξ _ hs
      let w := finitePlaceAtAbsoluteValuation (L := E) A h
      letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := E) A h
      let hw : IsPlaceOver A w := finitePlaceAtAbsoluteValuation_isPlaceOver (L := E) A h
      let f := ξ.comp (weilRestrictScalars h hw)
      have hf : IsOpen {z : Ine (F := E) A | f (ineIncl hw z) = 1} :=
        hopen.preimage (continuous_inertiaRestrictScalars (K := K) (L := E) (A := A))
      exact ih (Module.finrank E Q) hlt E Ω Q rfl hw f (fun z => hpow _) hf

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one
    {H : Type*} [CommGroup H] {n : ℕ} [NeZero n]
    (h : IsPlaceOver A v) (ξ : Weil h →* H) (hpow : ∀ s, ξ s ^ n = 1)
    (hop : IsOpen {s : Ine (F := K) A | ξ (ineIncl h s) = 1})
    {s : Weil h} (hs : toMaxAb K Ω (s : Gal(Ω/K)) = 1) : ξ s = 1 := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  letI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  let B := K⟮ζ⟯
  letI : FiniteDimensional K B :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  letI : IsCyclotomicExtension {n} K B := hζ.intermediateField_adjoin_isCyclotomicExtension K
  letI : IsGalois K B := IsCyclotomicExtension.isGalois {n} K B
  have he : IsPrimitiveRoot (AdjoinSimple.gen K ζ) n :=
    IsPrimitiveRoot.of_map_of_injective (f := B.val) hζ B.val.injective
  let c := he.autToPow K
  have hc : Function.Injective c := he.autToPow_injective K
  letI : IsAbelianGalois K B := {
    is_comm.comm s t := hc (by rw [map_mul, map_mul, mul_comm]) }
  letI : HasEnoughRootsOfUnity B n :=
    ⟨⟨_, he⟩, rootsOfUnity.isCyclic B n⟩
  exact finite_exponent_weilCharacter_of_abelian_root_extension (Module.finrank K B)
    K Ω B rfl h ξ hpow hop s hs

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one
