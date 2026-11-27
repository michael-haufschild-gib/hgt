import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwoPlaceInertiaIntersection
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility

/-! An exponent-one tame representative of a coupled generator at a split
place reduces to the first finite-field label. Congruence therefore determines
its value under characters trivial on principal units. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.Gal
open WindowedLandauTheory.ConjugateSelfDual WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.NormalizedTypes GlobalTheory.GLq

namespace GlobalTheory.TameKummer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def TameRep (v : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : G E Ω) (u : 𝓞 E) : Prop :=
  ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ σ ∈ Ine (F := E) A ∧
    ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧
      π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) ∧
      A.valuation (σ π / π - (algebraMap E Ω (u : E)) ^ e) < 1

theorem valuation_le_of_uniformizer {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}
    (hA : IsPlaceOver A v) {a b : 𝓞 E} (ha : a ∈ v.asIdeal)
    (hb : b ∈ v.asIdeal) (hb₂ : b ∉ v.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hb)
  have hnot : ¬ J ≤ v.asIdeal := fun h => hb₂ (by
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
    exact Ideal.mul_mono_right h)
  obtain ⟨s, hsJ, hsv⟩ := Set.not_subset.mp hnot
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (hJ ▸ Ideal.mul_mem_mul ha hsJ)
  have hle (c : 𝓞 E) : A.valuation (algebraMap E Ω (c : E)) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr
      (mem_of_isIntegral_int A (c.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom))
  have hs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (hle s) (le_of_not_gt (fun h => hsv ((hA s).mp h)))
  have h := congrArg (fun c : 𝓞 E => A.valuation (algebraMap E Ω (c : E))) ht
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at h hs ⊢
  rw [hs, mul_one] at h
  rw [h]
  exact mul_le_of_le_one_right' (hle t)

theorem exists_nat_sub_mem_of_prime_norm (v : HeightOneSpectrum (𝓞 E)) (p : ℕ)
    [Fact p.Prime] (hN : normV v = p) (hpv : (p : 𝓞 E) ∈ v.asIdeal) (u : 𝓞 E) :
    ∃ a : ℕ, a < p ∧ u - (a : 𝓞 E) ∈ v.asIdeal := by
  have hp : p.Prime := Fact.out
  letI := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : CharP (𝓞 E ⧸ v.asIdeal) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpv
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal) = p := hN
  letI : Finite (𝓞 E ⧸ v.asIdeal) :=
    Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
  let f : ZMod p →+* 𝓞 E ⧸ v.asIdeal := ZMod.castHom (dvd_refl p) _
  have hsurj : Function.Surjective f :=
    (Function.Injective.bijective_of_nat_card_le f.injective (by rw [hcard, Nat.card_zmod])).2
  obtain ⟨x, hx⟩ := hsurj (Ideal.Quotient.mk v.asIdeal u)
  refine ⟨x.val, ZMod.val_lt x, Ideal.Quotient.eq.mp ?_⟩
  rw [← hx, map_natCast, ← map_natCast f, ZMod.natCast_zmod_val]

variable {p : ℕ} [Fact p.Prime]

theorem redThrough_eq_of_valuation_sub_lt {A : ValuationSubring Ω}
    (κ : ResidueField A ≃+* Fbar p) {z w : Ω} (hz : z ∈ A) (hw : w ∈ A)
    (h : A.valuation (z - w) < 1) : redThrough A κ z = redThrough A κ w := by
  rw [redThrough, dif_pos hz, redThrough, dif_pos hw]
  congr 1
  apply Ideal.Quotient.eq.mpr
  exact (A.valuation_lt_one_iff (⟨z, hz⟩ - ⟨w, hw⟩)).mpr h

private theorem redThrough_natCast (A : ValuationSubring Ω) (κ : ResidueField A ≃+* Fbar p)
    (a : ℕ) : redThrough A κ (a : Ω) = (a : Fbar p) := by
  rw [redThrough, dif_pos (natCast_mem A a)]
  change κ (residue A (a : A)) = _
  rw [map_natCast, map_natCast]

omit [NumberField E] in
private theorem coupled_ne_one [IsAlgClosed Ω] [CharZero Ω] (A : ValuationSubring Ω)
    (κ : ResidueField A ≃+* Fbar p) (σ : G E Ω) (L : LabelDatum p)
    (hT : TameCoupled A κ σ L.gen) : σ ≠ 1 := by
  rintro rfl
  have hp : p.Prime := Fact.out
  have hpow : 1 < p ^ 2 := Nat.one_lt_pow (by decide) hp.one_lt
  have hn : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt hpow
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) hn
  have hy₀ : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hy.symm
  have h := hT 2 (by decide) y hy
  rw [AlgEquiv.one_apply, div_self hy₀, ← Nat.cast_one, redThrough_natCast, Nat.cast_one] at h
  have hord := L.gen_order 2 (by decide)
  rw [← h, orderOf_one] at hord
  have hp₂ : 4 ≤ p ^ 2 := by
    simpa using Nat.pow_le_pow_left hp.two_le 2
  omega

/-- Inertia gives congruent ratios on two elements of equal nonzero value. -/
private theorem ratio_valuation_sub_lt {A : ValuationSubring Ω} {σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) A) {π y : Ω} (hπ : π ≠ 0) (hy : y ≠ 0)
    (hval : A.valuation π = A.valuation y) (hσy : A.valuation (σ y / y) ≤ 1) :
    A.valuation (σ π / π - σ y / y) < 1 := by
  have hw : A.valuation (π / y) = 1 := by
    rw [map_div₀, hval, div_self (by simpa using hy)]
  have hsmall : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw.le
  have key : σ π / π - σ y / y =
      (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    have hσy₀ : σ y ≠ 0 := by simpa using hy
    rw [map_div₀]
    field_simp
  rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw, div_one]
  exact (mul_le_of_le_one_left' hσy).trans_lt hsmall

/-- A tame representative of the prescribed generator reduces to its first label. -/
theorem tameRep_residue [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hAv : IsPlaceOver A v)
    (hN : normV v = p) (hpv : (p : 𝓞 E) ∈ v.asIdeal) (hp₂ : (p : 𝓞 E) ∉ v.asIdeal ^ 2)
    (κ : ResidueField A ≃+* Fbar p) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A)
    (L : LabelDatum p) (hT : TameCoupled A κ σ L.gen) {u : 𝓞 E} (hu : TameRep v 1 σ u) :
    ∃ a : ℕ, a.Coprime p ∧ u - (a : 𝓞 E) ∈ v.asIdeal ∧
      algebraMap (ZMod p) (Fbar p) (a : ZMod p) = L.gen 1 := by
  letI := IsAlgClosure.isAlgClosed E (K := Ω)
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hp : p.Prime := Fact.out
  have hn : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hp₀ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨B, hBv, hσB, ϖ, π, hϖ, hϖ₂, hπ, hrep⟩ := hu
  have hAB := GlobalTheory.InertiaLift.eq_of_nontrivial_common_inertia A B v hAv hBv
    hpv hσ hσB (coupled_ne_one A κ σ L hT)
  rw [← hAB, zpow_one] at hrep
  rw [hN] at hπ
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) hn
  have hy₀ : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact hp₀ hy.symm
  have hπ₀ : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at hπ
    exact hϖ₂ (by rw [hπ]; exact zero_mem _)
  have hϖp : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (p : Ω) := by
    rw [show (p : Ω) = algebraMap E Ω ((p : 𝓞 E) : E) by simp]
    exact le_antisymm (valuation_le_of_uniformizer hAv hϖ hpv hp₂)
      (valuation_le_of_uniformizer hAv hpv hϖ hϖ₂)
  have hπy : A.valuation π = A.valuation y := by
    apply (pow_left_inj hn.ne').mp
    rw [← map_pow, ← map_pow, hπ, hy, hϖp]
  have hpow := ratio_pow_eq_one σ hp₀ hy
  have hratio : A.valuation (σ y / y) = 1 := valuation_eq_one_of_pow_eq_one A hn.ne' hpow
  have hs := ratio_valuation_sub_lt hσ hπ₀ hy₀ hπy hratio.le
  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem_of_prime_norm v p hN hpv u
  have hva : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 :=
    by simpa using (hAv (u - (a : 𝓞 E))).mpr hua
  have hv : A.valuation (σ y / y - (a : Ω)) < 1 := by
    rw [show σ y / y - (a : Ω) = -(σ π / π - σ y / y) +
        (σ π / π - algebraMap E Ω (u : E)) + (algebraMap E Ω (u : E) - (a : Ω)) by ring]
    exact Valuation.map_add_lt _ (Valuation.map_add_lt _ (by simpa only [Valuation.map_neg] using hs) hrep) hva
  have hlabel := hT 1 one_pos y (by simpa only [pow_one] using hy)
  have hcast : L.gen 1 = (a : Fbar p) := by
    rw [← hlabel, redThrough_eq_of_valuation_sub_lt κ ((A.valuation_le_one_iff _).mp hratio.le)
      (natCast_mem A a) hv, redThrough_natCast]
  refine ⟨a, Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr ?_), hua, by rw [map_natCast, hcast]⟩
  intro ha
  have hzero : (a : Fbar p) = 0 := (CharP.cast_eq_zero_iff (Fbar p) p a).mpr ha
  have h := pow_orderOf_eq_one (L.gen 1)
  rw [L.gen_order 1 one_pos, pow_one p, hcast, hzero, zero_pow hn.ne'] at h
  exact zero_ne_one h

/-- Equality of the residues of two integral representatives suffices to
compare their images under any tame local character. -/
theorem localCharacter_eq_of_sub_mem {E M : Type*} [Field E] [NumberField E] [Group M]
    (v : HeightOneSpectrum (𝓞 E)) (χ : (v.adicCompletion E)ˣ →* M)
    (hχ : ∀ x : (v.adicCompletion E)ˣ, Valued.v (x : v.adicCompletion E) = 1 →
      Valued.v ((x : v.adicCompletion E) - 1) ≤ WithZero.exp (-1 : ℤ) → χ x = 1)
    {a b : 𝓞 E} (hb : b ∉ v.asIdeal) (hab : a - b ∈ v.asIdeal)
    (U V : Eˣ) (hU : (U : E) = (a : E)) (hV : (V : E) = (b : E)) :
    χ (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom U) =
      χ (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom V) := by
  let j := algebraMap E (v.adicCompletion E)
  let jU := Units.map j.toMonoidHom
  have ha : a ∉ v.asIdeal := fun h => hb (by simpa using v.asIdeal.sub_mem h hab)
  have hva := (v.intValuation_eq_one_iff_mem_primeCompl a).mpr ha
  have hvb := (v.intValuation_eq_one_iff_mem_primeCompl b).mpr hb
  have hvab : v.intValuation (a - b) ≤ WithZero.exp (-1 : ℤ) := by
    change v.intValuation (a - b) ≤ WithZero.exp (-((1 : ℕ) : ℤ))
    rw [v.intValuation_le_pow_iff_mem (a - b) 1, pow_one]
    exact hab
  have hr : ((jU (U / V) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      j ((a : E) / (b : E)) := by simp [jU, hU, hV]
  have hb₀ : (b : E) ≠ 0 := hV ▸ V.ne_zero
  have hratio : (a : E) / (b : E) - 1 = ((a - b : 𝓞 E) : E) / (b : E) := by
    exact div_sub_one hb₀
  have hv (c : 𝓞 E) : v.valuation E (c : E) = v.intValuation c :=
    v.valuation_of_algebraMap c
  have hv' (x : E) : Valued.v (j x) = v.valuation E x :=
    v.valuedAdicCompletion_eq_valuation' x
  have h : χ (jU (U / V)) = 1 := by
    apply hχ
    · rw [hr, hv', map_div₀, hv, hv, hva, hvb, div_one]
    · rw [hr, ← map_one j, ← map_sub, hv', hratio,
        map_div₀, hv, hv, hvb, div_one]
      exact hvab
  rw [map_div, map_div, div_eq_one] at h
  exact h

/-- A specified residue character evaluates an exponent-one representative
at the first generator of the coupled system. -/
theorem localCharacter_of_tameRep [IsAlgClosure E Ω] {M : Type} [Group M]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (hAv : IsPlaceOver A v)
    (hN : normV v = p) (hpv : (p : 𝓞 E) ∈ v.asIdeal) (hp₂ : (p : 𝓞 E) ∉ v.asIdeal ^ 2)
    (κ : ResidueField A ≃+* Fbar p) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A)
    (L : LabelDatum p) (hT : TameCoupled A κ σ L.gen)
    (χ : (v.adicCompletion E)ˣ →* M) (η : (ZMod p)ˣ →* M)
    (hχ : ∀ x : (v.adicCompletion E)ˣ, Valued.v (x : v.adicCompletion E) = 1 →
      Valued.v ((x : v.adicCompletion E) - 1) ≤ WithZero.exp (-1 : ℤ) → χ x = 1)
    (hη : ∀ (a : ℕ) (ha : a.Coprime p) (x : Eˣ), (x : E) = (a : E) →
      χ (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom x) = η (ZMod.unitOfCoprime a ha))
    {u : 𝓞 E} (hu : TameRep v 1 σ u) (U : Eˣ) (hU : (U : E) = (u : E)) :
    ∃ b : (ZMod p)ˣ, algebraMap (ZMod p) (Fbar p) (b : ZMod p) = L.gen 1 ∧
      χ (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom U) = η b := by
  obtain ⟨a, ha, hua, hgen⟩ := tameRep_residue A v hAv hN hpv hp₂ κ hσ L hT hu
  have hpA : A.valuation (p : Ω) < 1 := by simpa using (hAv (p : 𝓞 E)).mpr hpv
  have hav : (a : 𝓞 E) ∉ v.asIdeal := fun h =>
    natCast_valuation_not_lt_one A hpA ha.symm (by simpa using (hAv (a : 𝓞 E)).mpr h)
  have ha₀ : (a : E) ≠ 0 := by
    intro h
    have he : (a : 𝓞 E) = 0 := RingOfIntegers.coe_injective (by simpa using h)
    exact hav (by rw [he]; exact zero_mem _)
  let V : Eˣ := Units.mk0 (a : E) ha₀
  refine ⟨ZMod.unitOfCoprime a ha, by simpa using hgen, ?_⟩
  exact (localCharacter_eq_of_sub_mem v χ hχ hav hua U V hU (by simp [V])).trans (hη a ha V rfl)

end GlobalTheory.TameKummer
