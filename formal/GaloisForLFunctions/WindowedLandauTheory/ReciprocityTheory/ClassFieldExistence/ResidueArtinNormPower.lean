import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinNorm

/-! Over a base residue field of prime order the residue norm is
the product over the prime-power Frobenius orbit. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
  {p n : ℕ} [Fact p.Prime]

local notation "w" => finitePlaceAtAbsoluteValuation (L := L) A h
local notation "hw" => finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
local notation "κ" => 𝓞 K ⧸ HeightOneSpectrum.asIdeal v
local notation "κ'" => 𝓞 L ⧸ HeightOneSpectrum.asIdeal w

theorem residueArtinOnBaseInertia_norm_pow [Algebra (ZMod p) κ']
    (e : κ ≃+* ZMod p) (hd : Module.finrank (ZMod p) κ' = n)
    {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α)
    {β : Weil hw →* ((w).adicCompletion L)ˣ} (hβ : IsLocalArtin L Ω β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1) (t : Ine (F := K) A) :
    algebraMap (ZMod p) κ' (e (finiteCompletionUnitReduction v (localArtinOnInertia hα t))) =
      ∏ j ∈ Finset.range n, ((residueArtinOnBaseInertia K Ω L h hβ he t ^ p ^ j : κ'ˣ) : κ') := by
  letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI := v.isMaximal
  letI := (w).isMaximal
  letI : Field κ := Ideal.Quotient.field v.asIdeal
  letI : Field κ' := Ideal.Quotient.field (w).asIdeal
  letI : Fintype κ := Fintype.ofEquiv (ZMod p) e.symm.toEquiv
  letI : Finite κ' := (w).asIdeal.finiteQuotientOfFreeOfNeBot (w).ne_bot
  letI : Fintype κ' := Fintype.ofFinite _
  letI : Algebra κ κ' := inferInstanceAs (Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ (w).asIdeal))
  have hq : Nat.card κ = p := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  have hdeg : Module.finrank κ κ' = n := by
    have hq' : Fintype.card κ = p := by rw [← Nat.card_eq_fintype_card, hq]
    have hc := (Module.card_eq_pow_finrank (K := κ) (V := κ')).symm.trans
      (Module.card_eq_pow_finrank (K := ZMod p) (V := κ'))
    rw [hq', ZMod.card, hd] at hc
    exact (pow_right_strictMono₀ (Fact.out : p.Prime).one_lt).injective hc
  have hmap : (algebraMap (ZMod p) κ').comp e.toRingHom = algebraMap κ κ' := by
    have hbase : (algebraMap κ κ').comp e.symm.toRingHom = algebraMap (ZMod p) κ' :=
      RingHom.ext_zmod _ _
    apply RingHom.ext
    intro x
    change algebraMap (ZMod p) κ' (e x) = _
    rw [← hbase, RingHom.comp_apply]
    change algebraMap κ κ' (e.symm (e x)) = _
    rw [e.symm_apply_apply]
  let r := residueArtinOnBaseInertia K Ω L h hβ he
  have h := congrArg Units.val (residueArtinOnBaseInertia_norm K Ω L h hα hβ he t)
  change (finiteCompletionUnitReduction v (localArtinOnInertia hα t) : κ) = Algebra.norm κ (r t : κ') at h
  change ((algebraMap (ZMod p) κ').comp e.toRingHom)
      (finiteCompletionUnitReduction v (localArtinOnInertia hα t) : κ) = _
  rw [hmap, h, FiniteField.algebraMap_norm_eq_prod_pow κ κ', hdeg, hq]
  exact Finset.prod_congr rfl fun j _ => (Units.val_pow_eq_pow_val _ _).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.residueArtinOnBaseInertia_norm_pow
