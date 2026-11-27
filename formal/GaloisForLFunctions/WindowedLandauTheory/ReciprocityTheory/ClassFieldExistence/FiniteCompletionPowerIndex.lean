import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalFieldPowerIndex
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-! In a finite number-field completion the power index is the product
of n² and the norm of the prime-power part of (n). -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN
open scoped WithZero ValuativeRel

namespace GlobalTheory.Reciprocity

universe u

private theorem irreducible_intValuation_eq_exp_neg_one {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (v : Valuation F ℤᵐ⁰) [v.Compatible] (hv : Function.Surjective v)
    {π : 𝒪[F]} (hπ : Irreducible π) : v (π : F) = WithZero.exp (-1 : ℤ) := by
  have he (z : 𝒪[F]) : v (z : F) ≤ 1 := by
    rw [← map_one v, ← v.vle_iff_le, (ValuativeRel.valuation F).vle_iff_le, map_one]
    exact z.2
  have hunit (z : 𝒪[F]) : IsUnit z ↔ v (z : F) = 1 :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one (v := v)
      { hom_inj := Subtype.val_injective
        map_le_one := he
        exists_of_le_one := fun x hx => by
          refine ⟨⟨x, ?_⟩, rfl⟩
          rwa [← map_one v, ← v.vle_iff_le, (ValuativeRel.valuation F).vle_iff_le, map_one] at hx })
  have hπlt : v (π : F) < 1 := lt_of_le_of_ne (he π) (mt (hunit π).mpr hπ.not_isUnit)
  have hπ0 : v (π : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hlog : WithZero.log (v (π : F)) < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hπ0, WithZero.exp_zero]
    exact hπlt
  refine le_antisymm ?_ ?_
  · rw [← WithZero.exp_log hπ0, WithZero.exp_le_exp]
    omega
  · obtain ⟨x, hx⟩ := hv (WithZero.exp (-1 : ℤ))
    have hxle : v x ≤ 1 := by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; decide
    let z : 𝒪[F] := ⟨x, by
      rwa [← map_one v, ← v.vle_iff_le, (ValuativeRel.valuation F).vle_iff_le, map_one] at hxle⟩
    have hzu : ¬IsUnit z := by
      rw [hunit, show v (z : F) = _ from hx, ← WithZero.exp_zero, WithZero.exp_inj]
      decide
    have hdiv : π ^ 1 ∣ z := (mem_maximalIdeal_pow_iff hπ (n := 1)).mp (by
      simpa only [pow_one] using (IsLocalRing.mem_maximalIdeal z).mpr hzu)
    obtain ⟨b, hb⟩ : π ∣ z := by simpa only [pow_one] using hdiv
    have heq : x = (π : F) * (b : F) := congrArg Subtype.val hb
    rw [← hx, heq, map_mul]
    exact mul_le_of_le_one_right' (he b)

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_power_adicCompletion (p : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom n : (p.adicCompletion K)ˣ →* (p.adicCompletion K)ˣ).range.index =
      n ^ 2 * p.asIdeal.absNorm ^ multiplicity p.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := K)).surjective p
  let p := w.maximalIdeal
  let F := p.adicCompletion K
  let v : Valuation F ℤᵐ⁰ := Valued.v
  letI : ValuativeRel F := numberFieldAdicCompletionValuativeRel K w
  letI : v.Compatible := numberFieldAdicCompletionValuationCompatible K w
  letI : IsNonarchimedeanLocalField F := numberFieldAdicCompletionIsNonarchimedeanLocalField K w
  letI : T2Space F := inferInstanceAs (T2Space (p.adicCompletion K))
  have hv : Function.Surjective v := valuedAdicCompletion_surjective K p
  have hO : v.valuationSubring.toSubring = 𝒪[F] := valuationSubring_eq_integer v
  let e : p.adicCompletionIntegers K ≃+* 𝒪[F] := RingEquiv.subringCongr hO
  have hq : Nat.card 𝓀[F] = p.asIdeal.absNorm := (Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv e.symm).toEquiv).trans (WindowedLandauTheory.UG.P.tjcosets_card_residue p)
  have hn0 : (n : F) ≠ 0 := by
    rw [← map_natCast (algebraMap K F), map_ne_zero_iff _ (algebraMap K F).injective]
    exact Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnO : (n : 𝒪[F]) ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    exact hn0 h'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨d, ε, hnd⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hnO hπ
  have hπv := irreducible_intValuation_eq_exp_neg_one v hv hπ
  have hε : v ((ε : 𝒪[F]) : F) = 1 := by
    have hi : v.Integers 𝒪[F] := by
      refine ⟨Subtype.val_injective, ?_, ?_⟩
      · intro x
        exact v.vle_one_iff.mp ((ValuativeRel.valuation F).vle_one_iff.mpr x.2)
      · intro x hx
        exact ⟨⟨x, (ValuativeRel.valuation F).vle_one_iff.mp (v.vle_one_iff.mpr hx)⟩, rfl⟩
    exact hi.isUnit_iff_valuation_eq_one.mp ε.isUnit
  have hnv : v (n : F) = WithZero.exp (-(d : ℤ)) := by
    have h := congrArg (fun a : 𝒪[F] => (a : F)) hnd
    change (n : F) = ((ε : 𝒪[F]) : F) * (π : F) ^ d at h
    rw [h, map_mul, map_pow, hε, hπv, one_mul, ← WithZero.exp_nsmul]
    simp
  have hd : d = multiplicity p.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    have hc : (n : F) = algebraMap (𝓞 K) F (n : 𝓞 K) := (map_natCast _ _).symm
    rw [hc] at hnv
    change Valued.v ((n : 𝓞 K) : p.adicCompletion K) = _ at hnv
    have hval := (valuedAdicCompletion_eq_valuation (K := K) (v := p) (n : 𝓞 K)).trans
      (valuation_of_algebraMap (K := K) (v := p) (n : 𝓞 K))
    have he := WithZero.exp_inj.mp
      ((intValuation_eq_exp_neg_multiplicity p (Nat.cast_ne_zero.mpr (NeZero.ne n))).symm.trans
        (hval.symm.trans hnv))
    omega
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hroots := (hζ.map_of_injective (algebraMap K F).injective).card_rootsOfUnity
  have hidx := index_power_localField v hv (NeZero.ne n) hπ hnd
  rw [hroots, hq, hd] at hidx
  change (powMonoidHom n : Fˣ →* Fˣ).range.index =
    n ^ 2 * p.asIdeal.absNorm ^ multiplicity p.asIdeal (Ideal.span {(n : 𝓞 K)})
  simpa only [pow_two] using hidx

end GlobalTheory.Reciprocity
