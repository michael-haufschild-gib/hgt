import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclotomicRadicalDescent
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteRadicalFieldOfIntegerUnits
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FrobeniusFixesUnitRadical
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteDegreeOneFrobenius
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! A congruence of global units can force them to be prime-power
powers while its modulus avoids any prescribed finite prime support. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions GlobalTheory.Kummer

namespace GlobalTheory.Reciprocity

private theorem exists_modulus_detecting_unit_radicals
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n b : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] (hb : 0 < b) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime b ∧ ∀ u : (𝓞 K)ˣ, (c : 𝓞 K) ∣ u.val - 1 →
      ∀ y : L, y ^ n = algebraMap K L ((u : 𝓞 K) : K) → y ∈ Set.range (algebraMap K L) := by
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | ((n * b : ℕ) : 𝓞 K) ∈ v.asIdeal}
  have hS : S.Finite := by
    have hn : ((n * b : ℕ) : 𝓞 K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (mul_ne_zero (NeZero.ne n) hb.ne')
    refine (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn)).subset ?_
    exact fun v hv => Ideal.dvd_span_singleton.mpr hv
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  choose v hv _hvPrime P hmax hlie hFrob using fun σ : Gal(L/K) =>
    GlobalTheory.DegreeOneFrobenius.exists_arithmeticFrobenius_away K L σ S hS
  have hnv (σ : Gal(L/K)) : (n : 𝓞 K) ∉ (v σ).asIdeal :=
    fun h => hv σ (by simpa only [S, Set.mem_setOf_eq, Nat.cast_mul] using
      Ideal.mul_mem_right _ _ h)
  have hbv (σ : Gal(L/K)) : (b : 𝓞 K) ∉ (v σ).asIdeal :=
    fun h => hv σ (by simpa only [S, Set.mem_setOf_eq, Nat.cast_mul] using
      Ideal.mul_mem_left _ _ h)
  let c := ∏ σ : Gal(L/K), (v σ).asIdeal.absNorm
  have hc : 0 < c := Finset.prod_pos fun σ _ => Nat.pos_of_ne_zero (fun h =>
    (v σ).ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  refine ⟨c, hc, Nat.Coprime.prod_left (fun σ _ => absNorm_coprime_of_natCast_notMem (v σ) (hbv σ)),
    fun u hu y hy => ?_⟩
  have hIy : IsIntegral ℤ y := IsIntegral.of_pow (NeZero.pos n) (by
    rw [hy]
    exact u.val.isIntegral_coe.algebraMap)
  let z : 𝓞 L := ⟨y, hIy⟩
  have hz : z ^ n = algebraMap (𝓞 K) (𝓞 L) u.val := by
    apply RingOfIntegers.ext
    change y ^ n = algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) u.val)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact hy
  apply (IsGalois.mem_range_algebraMap_iff_fixed y).mpr
  intro σ
  letI : (P σ).IsMaximal := hmax σ
  letI : (P σ).LiesOver (v σ).asIdeal := hlie σ
  have hcσ : (c : 𝓞 K) ∈ (v σ).asIdeal := by
    have hd : (v σ).asIdeal.absNorm ∣ c := Finset.dvd_prod_of_mem _ (Finset.mem_univ σ)
    obtain ⟨e, he⟩ := hd
    rw [he, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hU : u.val - 1 ∈ (v σ).asIdeal := by
    obtain ⟨a, ha⟩ := hu
    rw [ha]
    exact Ideal.mul_mem_right _ _ hcσ
  exact congrArg Subtype.val
    (GlobalTheory.Kummer.IsArithFrobAt.fixes_integer_radical_of_unit_congruent_one
      (v σ) (P σ) (hnv σ) (hFrob σ) u hU hz)

private theorem exists_integerUnit_pow_eq_of_field_pow_eq {E : Type} [Field E] [NumberField E]
    (u : (𝓞 E)ˣ) {n : ℕ} (hn : 0 < n) (y : E) (hy : y ^ n = (u.val : E)) :
    ∃ z : (𝓞 E)ˣ, z ^ n = u := by
  have hI : IsIntegral ℤ y := IsIntegral.of_pow hn (by rw [hy]; exact u.val.isIntegral_coe)
  let z : 𝓞 E := ⟨y, hI⟩
  have hz : z ^ n = u.val := RingOfIntegers.ext hy
  have hun : IsUnit (z ^ n) := hz.symm ▸ u.isUnit
  have hu := (isUnit_pow_iff hn.ne').mp hun
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz])⟩

theorem exists_coprime_congruence_for_primePower_units (E : Type) [Field E] [NumberField E]
    (p r b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (c : 𝓞 E) ∣ u.val - 1 →
      ∃ z : (𝓞 E)ˣ, z ^ (p ^ r) = u := by
  obtain ⟨n, hn, -, hdesc⟩ := exists_pow_descent_cyclotomic E p r hp
  letI : NeZero n := ⟨hn.ne'⟩
  let Ω := AlgebraicClosure E
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  let K := IntermediateField.adjoin E {ζ}
  letI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  letI : NumberField K := NumberField.of_module_finite E K
  let ξ : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hξ : IsPrimitiveRoot ξ n := IsPrimitiveRoot.of_map_of_injective
    (f := algebraMap K Ω) hζ (algebraMap K Ω).injective
  letI : HasEnoughRootsOfUnity K n := ⟨⟨ξ, hξ⟩, rootsOfUnity.isCyclic K n⟩
  obtain ⟨L, hL, hLG, hf⟩ := exists_finite_galois_contains_roots_of_integer_units (E := E) (K := K) (Ω := Ω) n
  letI := hL
  letI := hLG
  letI : NumberField L := NumberField.of_module_finite K L
  obtain ⟨c, hc, hcb, hdetect⟩ := exists_modulus_detecting_unit_radicals (K := K) (L := L) n b hb
  refine ⟨c, hc, hcb, fun u hu => ?_⟩
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u.val : E)) hn
  let Y : L := ⟨y, hf u hy⟩
  let U : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 E) (𝓞 K)).toMonoidHom u
  have hU : (c : 𝓞 K) ∣ U.val - 1 := by
    rw [show U.val = algebraMap (𝓞 E) (𝓞 K) u.val from rfl, ← map_one (algebraMap (𝓞 E) (𝓞 K)),
      ← map_sub, ← map_natCast (algebraMap (𝓞 E) (𝓞 K))]
    exact map_dvd _ hu
  have hY : Y ^ n = algebraMap K L (U.val : K) := by
    apply Subtype.ext
    change y ^ n = algebraMap K Ω (U.val : K)
    rw [hy, show (U.val : K) = algebraMap E K (u.val : E) from rfl,
      ← IsScalarTower.algebraMap_apply E K Ω]
  obtain ⟨k, hk⟩ := hdetect U hU Y hY
  have hyK : y ∈ K := by
    have hk' : (k : Ω) = y := congrArg Subtype.val hk
    rw [← hk']
    exact k.2
  obtain ⟨z, hz⟩ := hdesc Ω ζ hζ (u.val : E) y hyK hy
  exact exists_integerUnit_pow_eq_of_field_pow_eq u (pow_pos hp.pos _) z hz

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_coprime_congruence_for_primePower_units
