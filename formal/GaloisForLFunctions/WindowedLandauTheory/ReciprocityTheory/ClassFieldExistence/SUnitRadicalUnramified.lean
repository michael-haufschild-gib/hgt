import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitRadicalDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.KummerUnramified
import GaloisForLFunctions.RHTower.Artin.FrobeniusElementsRestrictToASubextension

/-! The radical field of S-units is unramified away from S and the
exponent. Inertia restricts trivially to every monogenic radical field. -/

noncomputable section

open GaloisForLFunctions NumberField IsDedekindDomain IntermediateField
open scoped IsMulCommutative

namespace GlobalTheory.Kummer

universe u

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- A monogenic radical extension has trivial inertia where the
ramification criterion for its defining power applies. -/
theorem inertia_eq_bot_of_radical {L : Type u} [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] {n : ℕ} (a : Kˣ) {β : L}
    (hβ : β ^ n = algebraMap K L (a : K)) (hgen : K⟮β⟯ = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver v.asIdeal] : P.inertia Gal(L/K) = ⊥ := by
  classical
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have he := ramificationIdx_eq_one_of_pow_eq a hβ hgen v hnv hav P
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(L/K), he] at hc
  exact Subgroup.card_eq_one.mp hc

variable {G : Type*} [Group G] [MulSemiringAction G K]
attribute [local instance] primeMulAction
variable (S : SubMulAction G (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

local notation "Δ" => sUnitRadicalClasses K G S n
local notation "M" => radicalField (Ω := Ω) Δ

local instance : NumberField M := NumberField.of_module_finite K M
local instance : IsAbelianGalois K M := radicalField_isAbelianGalois Δ
local instance : Fintype Gal(M/K) := Fintype.ofFinite _

private theorem inertia_fixes_sUnit_root
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] [Q.LiesOver v.asIdeal]
    {σ : Gal(M/K)} (hσ : σ ∈ Q.inertia Gal(M/K)) (a : Kˣ)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) {β : M}
    (hβ : β ^ n = algebraMap K M (a : K)) : σ β = β := by
  let L := K⟮β⟯
  let y : L := ⟨β, mem_adjoin_simple_self K _⟩
  let P := Q.under (𝓞 L)
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsAbelianGalois K L := IsAbelianGalois.of_algHom (L.val)
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : P.IsMaximal := inferInstance
  letI : P.LiesOver v.asIdeal := Ideal.under_liesOver_of_liesOver (𝓞 L) Q v.asIdeal
  have hy : y ^ n = algebraMap K L (a : K) := Subtype.ext hβ
  have hgen : K⟮y⟯ = ⊤ := lift_injective _ (by rw [lift_adjoin_simple, lift_top])
  have hres := restrictHom_mem_inertia K L M (G := Gal(L/K)) hσ
  change IsGaloisGroup.restrictHom Gal(M/K) Gal(L/K) K L M σ ∈ P.inertia Gal(L/K) at hres
  rw [inertia_eq_bot_of_radical a hy hgen v hnv hav P, Subgroup.mem_bot] at hres
  have he := IsGaloisGroup.algebraMap_restrictHom_smul Gal(M/K) Gal(L/K) K L M σ y
  rw [hres, one_smul] at he
  exact he.symm

/-- Primes outside S that do not divide the exponent are unramified
in the full S-unit radical field. -/
theorem sUnitRadicalField_unramified (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) : IsUnramifiedPrime K M Gal(M/K) v := by
  intro Q hQ hQv
  letI := hQ
  letI := hQv
  refine eq_bot_iff.mpr fun σ hσ => Subgroup.mem_bot.mpr ?_
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M)
    (s := {x : Ω | ∃ b : Kˣ, (b : PowerClasses K n) ∈ Δ ∧ x ^ n = algebraMap K Ω (b : K)})
    rfl ?_
  rintro x ⟨b, ⟨a, ha⟩, hx⟩
  let c : Kˣ := (sUnits K G S).subtype (Multiplicative.toAdd a)
  have hc : (c : PowerClasses K n) = (b : PowerClasses K n) := ha
  have hv₁ : v.valuation K (c : K) = 1 :=
    (GaloisForLFunctions.ordAt_eq_zero_iff K v c).mp ((Multiplicative.toAdd a).2 v hv)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (c : K)) (NeZero.pos n)
  have hcy : (c : PowerClasses K n) ∈ Δ := ⟨a, rfl⟩
  let β : M := ⟨y, mem_radicalField hcy hy⟩
  have hf : σ β = β :=
    inertia_fixes_sUnit_root S v hnv Q hσ c (by rw [hv₁, WithZero.log_one]; exact dvd_zero _) (Subtype.ext hy)
  obtain ⟨d, hd⟩ := exists_scalar_mul_of_same_class hc.symm hx hy
  have harg : (⟨x, mem_radicalField (Ω := Ω) (show (b : PowerClasses K n) ∈ Δ from ⟨a, ha⟩) hx⟩ : M) =
      algebraMap K M d * β := Subtype.ext hd
  change σ _ = _
  rw [harg, map_mul, AlgEquiv.commutes, hf]
  rfl

end GlobalTheory.Kummer
