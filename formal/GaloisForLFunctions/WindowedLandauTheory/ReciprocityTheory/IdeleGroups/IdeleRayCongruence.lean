import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration
import GaloisForLFunctions.HeckeLFunctions.TheRayClassGroupIsFinite

/-! Local congruence conditions on ideles restrict to the native ray
group on diagonal elements. -/

noncomputable section

open Topology NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open GaloisForLFunctions.HeckeLFunctions UniqueFactorizationMonoid

namespace GlobalTheory.Reciprocity

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

def positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)}
  one_mem' w _ := by simp
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (ha w hw)

theorem mem_positiveAt {S : Set {w : InfinitePlace K // w.IsReal}} {x : IdeleGroup K} :
    x ∈ positiveAt S ↔ ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) :=
  Iff.rfl

theorem isOpen_positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) :
    IsOpen (positiveAt S : Set (IdeleGroup K)) := by
  have : (positiveAt S : Set (IdeleGroup K)) = ⋂ w ∈ S, (fun x : IdeleGroup K ↦
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)) ⁻¹' Set.Ioi 0 := by
    ext x
    simp [mem_positiveAt]
  rw [this]
  refine S.toFinite.isOpen_biInter fun w _ ↦ isOpen_Ioi.preimage ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    (Units.continuous_val.comp (continuous_infiniteProj w.1))

end IdeleGroup

open IdeleGroup

namespace IdeleRay

variable (𝔪 : Modulus K)

def exponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  multiplicity v.asIdeal 𝔪.fin

omit [NumberField K] in
theorem exponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) :
    exponent 𝔪 v = 0 ↔ ¬ v.asIdeal ∣ 𝔪.fin :=
  multiplicity_eq_zero

omit [NumberField K] in
theorem one_le_exponent_iff (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ exponent 𝔪 v ↔ v.asIdeal ∣ 𝔪.fin := by
  rw [Nat.one_le_iff_ne_zero, Ne, exponent_eq_zero_iff, not_not]

omit [NumberField K] in

theorem asIdeal_pow_exponent_dvd (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ (exponent 𝔪 v) ∣ 𝔪.fin :=
  pow_multiplicity_dvd _ _

def idelesOneMod : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v.asIdeal ∣ 𝔪.fin),
    (unitsLevel v (exponent 𝔪 v)).comap (finiteProj v)) ⊓ positiveAt 𝔪.inf

theorem mem_idelesOneMod {x : IdeleGroup K} :
    x ∈ idelesOneMod 𝔪 ↔
      (∀ v, v.asIdeal ∣ 𝔪.fin → finiteProj v x ∈ unitsLevel v (exponent 𝔪 v)) ∧
        ∀ w ∈ 𝔪.inf, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  simp only [idelesOneMod, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_positiveAt]

def rayUnits : Subgroup Kˣ :=
  (idelesOneMod 𝔪).comap (diagonal K)

theorem mem_rayUnits {a : Kˣ} :
    a ∈ rayUnits 𝔪 ↔
      (∀ v, v.asIdeal ∣ 𝔪.fin → v.valuation K ((a : K) - 1) ≤ exp (-(exponent 𝔪 v : ℤ))) ∧
        ∀ w ∈ 𝔪.inf, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K) := by
  rw [rayUnits, Subgroup.mem_comap, mem_idelesOneMod]
  refine and_congr (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_)
    (forall_congr' fun w ↦ forall_congr' fun _ ↦ ?_)
  · have hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k := fun k ↦ by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [mem_unitsLevel_of_one_le ((one_le_exponent_iff 𝔪 v).2 hv), coe_finiteProj_diagonal,
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hc, hc,
      (algebraMap K (v.adicCompletion K)).map_sub, (algebraMap K (v.adicCompletion K)).map_one]
  · rw [coe_infiniteProj_diagonal]
    exact Iff.of_eq (congrArg (0 < ·) (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe _ _))

private theorem mem_fin_iff (r : 𝓞 K) :
    r ∈ 𝔪.fin ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
      v.intValuation r ≤ exp (-(exponent 𝔪 v : ℤ)) := by
  simp only [intValuation_le_pow_iff_mem]
  constructor
  · intro hr v _
    exact (Ideal.dvd_iff_le.mp (asIdeal_pow_exponent_dvd 𝔪 v)) hr
  · intro h
    rw [← Ideal.dvd_span_singleton, dvd_iff_emultiplicity_le 𝔪.fin_ne_bot]
    intro p hp
    by_cases hd : p ∣ 𝔪.fin
    · let v := HeightOneSpectrum.ofPrime hp
      have hf : FiniteMultiplicity p 𝔪.fin :=
        finiteMultiplicity_of_emultiplicity_eq_natCast
          (emultiplicity_eq_count_normalizedFactors hp.irreducible 𝔪.fin_ne_bot)
      rw [hf.emultiplicity_eq_multiplicity, ← pow_dvd_iff_le_emultiplicity, Ideal.dvd_span_singleton]
      exact h v hd
    · rw [emultiplicity_eq_zero.mpr hd]
      exact bot_le

private theorem valuation_sub_one_eq (α : Kˣ) {a b : 𝓞 K}
    (hab : algebraMap (𝓞 K) K b * (α : K) = algebraMap (𝓞 K) K a)
    (v : HeightOneSpectrum (𝓞 K)) (hb : b ∉ v.asIdeal) :
    v.valuation K ((α : K) - 1) = v.intValuation (a - b) := by
  have he := congrArg (v.valuation K)
    (show algebraMap (𝓞 K) K b * ((α : K) - 1) = algebraMap (𝓞 K) K (a - b) by
      rw [mul_sub, mul_one, hab, map_sub])
  rwa [map_mul, (valuation_eq_one_iff_notMem (K := K) v).mpr hb, one_mul,
    valuation_of_algebraMap] at he

/-- Multiplicative congruences in the completions agree with reduction of
a unit fraction modulo the finite ideal of the modulus. -/
theorem rayUnits_eq : rayUnits 𝔪 = rayGroup 𝔪 := by
  ext α
  have hprime (hα : α ∈ rayUnits 𝔪) : α ∈ primeToUnits 𝔪 := by
    intro v hv
    have h := ((mem_idelesOneMod 𝔪).mp hα).1 v hv
    have hv₁ := (mem_unitsLevel.mp h).1
    rwa [coe_finiteProj_diagonal, valuedAdicCompletion_eq_valuation'] at hv₁
  have he (hα : α ∈ primeToUnits 𝔪) : α ∈ rayUnits 𝔪 ↔
      rayHom 𝔪 ⟨α, hα⟩ = 1 := by
    obtain ⟨a, b, -, habs, hab⟩ := exists_unit_fraction 𝔪 hα
    have ha := fun v hv => (habs v hv).1
    have hb := fun v hv => (habs v hv).2
    have hfin : reduce 𝔪 ⟨α, hα⟩ = 1 ↔ a - b ∈ 𝔪.fin := by
      rw [reduce_eq 𝔪 _ ha hb hab, mul_inv_eq_one, Units.ext_iff]
      exact Ideal.Quotient.eq
    have hinf : signAtInf 𝔪 α = 1 ↔
        ∀ w ∈ 𝔪.inf, 0 < InfinitePlace.embedding_of_isReal w.2 (α : K) := by
      rw [funext_iff]
      simp only [signAtInf_apply, Pi.one_apply]
      constructor
      · intro h w hw
        specialize h ⟨w, hw⟩
        by_contra hh
        simp [hh] at h
      · intro h w
        rw [if_pos (h w.val w.2)]
    rw [mem_rayUnits]
    change _ ↔ (reduce 𝔪 ⟨α, hα⟩, signAtInf 𝔪 α) = (1, 1)
    rw [Prod.mk.injEq, hfin, hinf, mem_fin_iff]
    exact and_congr (forall₂_congr fun v hv => by
      rw [valuation_sub_one_eq α hab v (hb v hv)]) Iff.rfl
  constructor
  · intro h
    exact ⟨⟨α, hprime h⟩, (he (hprime h)).mp h, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact (he β.2).mpr hβ

end IdeleRay

end GlobalTheory.Reciprocity
