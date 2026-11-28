import GaloisForLFunctions.RHTower.Artin.ArtinSymbolOfACyclotomicCharacterIsTheNormResidue
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-! Away from the radical order, arithmetic Frobenius fixes a radical
of a unit congruent to one when the base contains the roots of unity. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions

namespace GlobalTheory.Kummer

private theorem eq_of_units_pow_eq_and_residue_eq {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) {n : ℕ} (hn : (n : R) ∉ P) (x y : Rˣ) (he : x ^ n = y ^ n)
    (hr : Ideal.Quotient.mk P x.val = Ideal.Quotient.mk P y.val) : x = y := by
  have hpow : (x / y) ^ n = 1 := by rw [div_pow, he, div_self']
  have hval : ((x / y).val) ^ n = 1 := congrArg Units.val hpow
  let r := Units.map (Ideal.Quotient.mk P).toMonoidHom
  have hxy : r x = r y := Units.ext hr
  have h : Ideal.Quotient.mk P (x / y).val = 1 := by
    change (r (x / y)).val = 1
    rw [map_div, hxy, div_self', Units.val_one]
  have hmem : (x / y).val - 1 ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h, map_one, sub_self]
  exact div_eq_one.mp (Units.ext (eq_one_of_pow_eq_one_of_sub_mem hval hn hmem))

private theorem primitiveRoot_mk_of_natCast_notMem {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) {n : ℕ} (hn : (n : R) ∉ P) {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (Ideal.Quotient.mk P ζ) n := by
  constructor
  · rw [← map_pow, hζ.pow_eq_one, map_one]
  · intro i hi
    apply hζ.dvd_of_pow_eq_one
    apply eq_of_pow_eq_one_of_sub_mem
      (show (ζ ^ i) ^ n = 1 by rw [← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow])
      (one_pow n) hn
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hi, map_one, sub_self]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local instance : SMulCommClass Gal(L/K) (𝓞 K) (𝓞 L) :=
  ⟨fun σ a x => RingOfIntegers.ext (by
    change σ (algebraMap K L (a : K) * (x : L)) = algebraMap K L (a : K) * σ (x : L)
    rw [map_mul, σ.commutes])⟩

private theorem gal_smul_algebraMap_integer (σ : Gal(L/K)) (a : 𝓞 K) :
    σ • algebraMap (𝓞 K) (𝓞 L) a = algebraMap (𝓞 K) (𝓞 L) a := by
  apply RingOfIntegers.ext
  change σ (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a)) =
    algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
    IsScalarTower.algebraMap_apply (𝓞 K) K L]
  exact σ.commutes (a : K)

theorem IsArithFrobAt.fixes_integer_radical_of_unit_congruent_one
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver v.asIdeal]
    {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] (hn : (n : 𝓞 K) ∉ v.asIdeal)
    {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ P)
    (u : (𝓞 K)ˣ) (hu : u.val - 1 ∈ v.asIdeal)
    {β : 𝓞 L} (hβ : β ^ n = algebraMap (𝓞 K) (𝓞 L) u.val) : σ • β = β := by
  letI := Ideal.Quotient.field P
  let m := Ideal.Quotient.mk P
  have hnP : (n : 𝓞 L) ∉ P := by
    rw [← map_natCast (algebraMap (𝓞 K) (𝓞 L))]
    exact fun h => hn ((Ideal.LiesOver.over (p := v.asIdeal) (P := P)).symm ▸ h)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  let ζK : 𝓞 K := ⟨ζ, hζ.isIntegral (NeZero.pos n)⟩
  let ζL := algebraMap (𝓞 K) (𝓞 L) ζK
  have hprim : IsPrimitiveRoot ζL n := by
    refine IsPrimitiveRoot.of_map_of_injective
      (f := algebraMap (𝓞 L) L) ?_ (IsFractionRing.injective (𝓞 L) L)
    change IsPrimitiveRoot (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) ζK)) n
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact hζ.map_of_injective (algebraMap K L).injective
  have hred : IsPrimitiveRoot (m ζL) n := primitiveRoot_mk_of_natCast_notMem P hnP hprim
  let q := Nat.card (𝓞 K ⧸ P.under (𝓞 K))
  have hFrob (x : 𝓞 L) : m (σ • x) = m x ^ q := by
    rw [← map_pow]
    exact Ideal.Quotient.eq.mpr (hσ x)
  have hζq : m ζL ^ q = m ζL := by
    rw [← hFrob, gal_smul_algebraMap_integer]
  have hβred : m β ^ n = 1 := by
    rw [← map_pow, hβ, ← map_one m]
    apply Ideal.Quotient.eq.mpr
    rw [← map_one (algebraMap (𝓞 K) (𝓞 L)), ← map_sub]
    change u.val - 1 ∈ P.under (𝓞 K)
    rwa [← Ideal.LiesOver.over (p := v.asIdeal) (P := P)]
  have hβfix : m (σ • β) = m β := by
    obtain ⟨i, -, hi⟩ := hred.eq_pow_of_pow_eq_one hβred
    rw [hFrob, ← hi, ← pow_mul, mul_comm i q, pow_mul, hζq]
  have hb : IsUnit β := (isUnit_pow_iff (NeZero.ne n)).mp (hβ.symm ▸ u.isUnit.map _)
  let βu := hb.unit
  let σu := Units.map (MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) σ).toMonoidHom βu
  have hp : (σ • β) ^ n = β ^ n := by
    change (MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) σ β) ^ n = β ^ n
    rw [← map_pow, hβ]
    exact gal_smul_algebraMap_integer σ u.val
  have hσβ : σu.val = σ • β := by
    change σ • βu.val = σ • β
    rw [IsUnit.unit_spec]
  have he : σu ^ n = βu ^ n := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hσβ, βu, IsUnit.unit_spec] using hp
  have hr : m σu.val = m βu.val := by
    simpa only [hσβ, βu, IsUnit.unit_spec] using hβfix
  have heq := eq_of_units_pow_eq_and_residue_eq P hnP σu βu he hr
  simpa only [hσβ, βu, IsUnit.unit_spec] using congrArg Units.val heq

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.IsArithFrobAt.fixes_integer_radical_of_unit_congruent_one
