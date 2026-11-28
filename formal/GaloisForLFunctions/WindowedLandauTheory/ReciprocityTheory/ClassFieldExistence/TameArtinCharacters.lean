import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinData
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionUnitsReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDeepRoots
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusPowerOnTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaPrimePower

/-! A local character kills principal units exactly when its Weil
character kills wild inertia. On inertia, inverse Artin takes values in
the integral units and reaches all of them. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory.TameKummer GaloisForLFunctions.HTGeometry
open scoped WithZero

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

local notation "Fv" => v.adicCompletion K
local notation "ν" => tameValHom (Valued.v : Valuation Fv ℤᵐ⁰)

private theorem valuation_one_on_inertia
    (a : Weil h →* Fvˣ) (ord : ∀ s : Weil h, Multiplicative.toAdd (ν (a s)) = -deg s)
    (t : Ine (F := K) A) : Valued.v (a (ineIncl h t) : Fv) = 1 := by
  have ht : ν (a (ineIncl h t)) = 1 := by
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (ν (a (ineIncl h t))) = 0
    rw [ord, deg_ineIncl, neg_zero]
  exact (tameValHom_mem_ker_iff (Valued.v : Valuation Fv ℤᵐ⁰) _).mp
    (MonoidHom.mem_ker.mpr ht)

private def inertiaUnitsOfValuation
    (a : Weil h →* Fvˣ) (ord : ∀ s : Weil h, Multiplicative.toAdd (ν (a s)) = -deg s) :
    Ine (F := K) A →* unitsLevel (K := K) v 0 := by
  refine (a.comp (ineIncl h)).codRestrict (unitsLevel (K := K) v 0) ?_
  intro t
  change a (ineIncl h t) ∈ unitsLevel (K := K) v 0
  have hv := valuation_one_on_inertia a ord t
  refine mem_unitsLevel.mpr ⟨hv, ?_⟩
  rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
  exact Valued.v.map_sub_le hv.le (map_one Valued.v).le

/-- Inverse Artin on inertia with codomain restricted to integral units. -/
def localArtinOnInertia {a : Weil h →* Fvˣ} (ha : IsLocalArtin K Ω (h := h) a) :
    Ine (F := K) A →* unitsLevel (K := K) v 0 :=
  inertiaUnitsOfValuation a ha.ord_eq

theorem localArtinOnInertia_surjective {a : Weil h →* Fvˣ}
    (ha : IsLocalArtin K Ω (h := h) a) : Function.Surjective (localArtinOnInertia ha) := by
  intro x
  obtain ⟨s, hs⟩ := ha.surj x.val
  have hv : ν (a s) = 1 := by
    rw [hs]
    exact MonoidHom.mem_ker.mp
      ((tameValHom_mem_ker_iff (Valued.v : Valuation Fv ℤᵐ⁰) x.val).mpr
        (mem_unitsLevel.mp x.2).1)
  have hd := ha.ord_eq s
  rw [hv] at hd
  have hsI : s.val ∈ Ine (F := K) A := deg_eq_zero_iff.mp (by
    change (0 : ℤ) = -deg s at hd
    omega)
  exact ⟨⟨s, hsI⟩, Subtype.ext hs⟩

theorem continuous_localArtinOnInertia {a : Weil h →* Fvˣ}
    (ha : IsLocalArtin K Ω (h := h) a) : Continuous (localArtinOnInertia ha) := by
  change Continuous (fun t => ⟨a (ineIncl h t), _⟩ : Ine (F := K) A → unitsLevel v 0)
  exact ha.cont.subtype_mk _

private theorem inertia_reduction_isOpen {a : Weil h →* Fvˣ}
    (ha : IsLocalArtin K Ω (h := h) a) :
    IsOpen (((finiteCompletionUnitReduction v).comp (localArtinOnInertia ha)).ker :
      Set (Ine (F := K) A)) := by
  have hx : (((finiteCompletionUnitReduction v).comp (localArtinOnInertia ha)).ker :
      Set (Ine (F := K) A)) = (fun t => a (ineIncl h t)) ⁻¹' (unitsLevel (K := K) v 1 : Set Fvˣ) := by
    ext t
    exact (finiteCompletionUnitReduction_eq_one_iff v (localArtinOnInertia ha t)).trans
      (mem_unitsLevel_one_iff_lt_one v _).symm
  rw [hx]
  exact (isOpen_unitsLevel (K := K) v 1).preimage ha.cont

private theorem valuation_residueChar (hV : IsPlaceOver A v)
    (p : ℕ) [CharP (𝓞 K ⧸ v.asIdeal) p] : A.valuation (p : Ω) < 1 := by
  have hm : (p : 𝓞 K) ∈ v.asIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_natCast]; exact CharP.cast_eq_zero _ _)
  have hv := (hV (p : 𝓞 K)).mpr hm
  simpa only [map_natCast] using hv

theorem artin_mem_unitsLevel_one_of_mem_wildInertia {a : Weil h →* Fvˣ}
    (hA : IsLocalArtin K Ω (h := h) a) (s : Weil h)
    (hs : s.val ∈ wildInertia A) : a s ∈ unitsLevel (K := K) v 1 := by
  let R := 𝓞 K ⧸ v.asIdeal
  letI := v.isMaximal
  letI : Field R := Ideal.Quotient.field v.asIdeal
  letI : Finite R := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Fintype R := Fintype.ofFinite _
  let p := ringChar R
  letI : CharP R p := ringChar.charP R
  obtain ⟨d, hprime, hc⟩ := FiniteField.card R p
  letI : Fact p.Prime := ⟨hprime⟩
  let f := (finiteCompletionUnitReduction v).comp (localArtinOnInertia hA)
  let t : Ine (F := K) A := ⟨s, wildInertia_le_inertia A hs⟩
  have hp := valuation_residueChar h p
  have hpn : p.Coprime (Fintype.card R - 1) := by
    rw [hc]
    exact coprime_pow_sub_one (p := p) d.pos
  have hpow (u : Ine (F := K) A) : f u ^ (Fintype.card R - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
  have hf := inertiaHom_eq_one_of_wild_of_coprime_exponent A hp f
    (inertia_reduction_isOpen hA) hpn hpow t hs
  have hlt := (finiteCompletionUnitReduction_eq_one_iff v (localArtinOnInertia hA t)).mp hf
  exact (mem_unitsLevel_one_iff_lt_one v _).mpr hlt

private theorem pow_eq_one_on_inertia_of_kills_wild
    (ξ : Weil h →* ℂˣ) (hw : ∀ s : Weil h, s.val ∈ wildInertia A → ξ s = 1)
    (p : ℕ) [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    (t : Ine (F := K) A) : ξ (ineIncl h t) ^ (normV v - 1) = 1 := by
  let φ := frob h
  let s := ineIncl h t
  let q := normV v
  let δ := (s ^ q)⁻¹ * (φ * s * φ⁻¹)
  have hδ := frobenius_conj_div_wild_of_card A hp t.2 (isFrob_frob (h := h))
  have e : ξ δ = 1 := hw δ ((mem_wildInertia_iff _ _).mpr hδ.2)
  change ξ ((s ^ q)⁻¹ * (φ * s * φ⁻¹)) = 1 at e
  simp only [map_mul, map_inv, map_pow] at e
  have he : ξ s = ξ s ^ q := by
    rw [inv_mul_eq_one, mul_comm (ξ φ), mul_inv_cancel_right] at e
    exact e.symm
  have hq : 1 ≤ q := (one_lt_normV v).le
  have hcalc : ξ s ^ (q - 1) * ξ s = 1 * ξ s := by
    rw [← pow_succ, Nat.sub_add_cancel hq, one_mul]
    exact he.symm
  exact mul_right_cancel hcalc

theorem localArtin_char_kills_wild_iff {a : Weil h →* Fvˣ}
    (hA : IsLocalArtin K Ω (h := h) a) (χ : Fvˣ →* ℂˣ) :
    (∀ s : Weil h, s.val ∈ wildInertia A → χ (a s) = 1) ↔
      ∀ u : Fvˣ, u ∈ unitsLevel (K := K) v 1 → χ u = 1 := by
  constructor
  · intro hw u hu
    let R := 𝓞 K ⧸ v.asIdeal
    letI := v.isMaximal
    letI : Field R := Ideal.Quotient.field v.asIdeal
    letI : Finite R := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype R := Fintype.ofFinite _
    let p := ringChar R
    letI : CharP R p := ringChar.charP R
    letI : Fact p.Prime := ⟨CharP.char_is_prime R p⟩
    let q := normV v
    have hq : 1 < q := one_lt_normV v
    have hR : (q : R) = 0 := by
      change (Nat.card R : R) = 0
      rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    have hm : ((q - 1 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      intro hm
      have he := Ideal.Quotient.eq_zero_iff_mem.mpr hm
      rw [map_natCast, Nat.cast_sub hq.le, hR, Nat.cast_one, zero_sub, neg_eq_zero] at he
      exact one_ne_zero he
    have hv : Valued.v ((q - 1 : ℕ) : Fv) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 K) Fv)]
      exact le_antisymm (valued_algebraMap_int_le_one v _)
        (le_of_not_gt fun ht => hm ((valued_algebraMap_int_lt_one_iff v _).mp ht))
    obtain ⟨d, -, hd, hroot⟩ := exists_unitsLevel_pow_roots v (q - 1) (Nat.sub_ne_zero_of_lt hq)
    obtain rfl := hd hv
    obtain ⟨z, hz, hzu⟩ := hroot u hu
    obtain ⟨t, ht⟩ := localArtinOnInertia_surjective hA ⟨z, hz⟩
    have htz : a (ineIncl h t) = z := congrArg Subtype.val ht
    have hp := valuation_residueChar h p
    have hχ := pow_eq_one_on_inertia_of_kills_wild (χ.comp a) hw p hp t
    change χ (a (ineIncl h t)) ^ (q - 1) = 1 at hχ
    rwa [← hzu, map_pow, ← htz]
  · intro hu s hs
    exact hu _ (artin_mem_unitsLevel_one_of_mem_wildInertia hA s hs)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.localArtin_char_kills_wild_iff
