import GaloisForLFunctions.RHTower.Artin.NormResiduesOfIdealsAreRayClassCharacters

/-!
# The reciprocity law for cyclotomic characters

Let `L/K` be a Galois extension of number fields with group `G`, `ζ ∈ 𝓞_L` a primitive `m`-th
root of unity, `κ : G → (ℤ/m)ˣ` the cyclotomic character, and `ψ₀` a character of `(ℤ/m)ˣ`.

* **Reciprocity** (`artinSymbol_cyclotomic_eq_heckeValue`): at every prime `v ∤ m` of `K`, the
  Artin symbol of `ψ₀ ∘ κ` is the value of the ray class character `ψ₀ ∘ N̄` modulo `(m) ∞`.
  Both are `ψ₀(N(v) mod m)`.
* **The `L`-series** (`artinEulerProduct_cyclotomic_eq_heckeL_mul`): for `Re s > 1`,
  `L(s, ψ₀ ∘ κ, L/K) = L(s, ψ₀ ∘ N̄) · Π_{v | m} (1 − (ψ₀ ∘ κ, v) N(v)^{-s})^{-1}`. This holds for
  every linear character whose Artin symbol is a ray class value outside the modulus
  (`artinEulerProduct_linearCharacter_eq_heckeL_mul`).
* **Cyclotomic extensions** (`exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top`): if
  `L = K(ζ)`, the cyclotomic character is injective (`cyclotomicCharacter_injective`), so every
  linear character of `G` is `ψ₀ ∘ κ` (`exists_eq_comp_cyclotomicCharacter`). Hence the Artin
  Euler product of every linear character of `Gal(K(ζ)/K)` is a Hecke `L`-series, up to the
  Euler factors at the primes `v | m`.
-/

open scoped Classical BigOperators NumberField
open IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

/-- A ray class character vanishes at the primes dividing its modulus. -/
theorem heckeValue_eq_zero_of_dvd {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.fin) :
    heckeValue 𝔪 ψ v.asIdeal = 0 := by
  apply heckeValue_of_not_mem
  rintro ⟨hI, hm⟩
  have h := hm v hv
  rw [coe_idealUnit, FractionalIdeal.count_self] at h
  exact one_ne_zero h

variable (K L : Type u) {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **An Artin Euler product with ray class values outside the modulus is a Hecke `L`-series
up to the Euler factors at the modulus.** If `(χ, v) = ψ(v)` for every prime `v ∤ 𝔪`, then
`L(s, χ, L/K) = L(s, ψ) · Π_{v | 𝔪} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`. -/
theorem artinEulerProduct_linearCharacter_eq_heckeL_mul (χ : LinearCharacter G)
    (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin →
      artinSymbol K L χ v = heckeValue 𝔪 ψ v.asIdeal)
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
      (linearCharacterLine χ) s = heckeL 𝔪 ψ s *
        ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
          (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by
  -- the Euler factors of `χ` at the primes of the modulus
  let F (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
    if v.asIdeal ∣ 𝔪.fin then (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹
    else 1
  have hF : HasProd F (∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
      (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) := by
    have h0 : HasProd F (∏ v ∈ (finite_primes_dvd 𝔪).toFinset, F v) :=
      hasProd_prod_of_ne_finset_one fun v hv => by
        rw [Set.Finite.mem_toFinset] at hv
        exact if_neg hv
    convert h0 using 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Set.Finite.mem_toFinset] at hv
    exact (if_pos hv).symm
  have hA : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (linearCharacterLine χ) v s)
      (numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
        (linearCharacterLine χ) s) :=
    (hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
      (K := K) (L := L) (linearCharacterLine χ)).hasProd
      (show s ∈ artinEulerAbsoluteHalfPlane from hs)
  -- factor by factor: the Hecke factor times the factor at the modulus
  have hfun : (fun v : HeightOneSpectrum (𝓞 K) =>
      numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) (linearCharacterLine χ) v s) =
      fun v => (1 - heckePrimeTerm 𝔪 ψ s v)⁻¹ * F v := by
    funext v
    rw [numberFieldFinitePlaceArtinEulerReciprocal_linearCharacterLine, heckePrimeTerm]
    by_cases hv : v.asIdeal ∣ 𝔪.fin
    · rw [heckeValue_eq_zero_of_dvd 𝔪 ψ hv, zero_mul, sub_zero, inv_one, one_mul]
      exact (if_pos hv).symm
    · rw [← h v hv, show F v = 1 from if_neg hv, mul_one]
  rw [hfun] at hA
  exact hA.unique ((heckeL_eulerProduct_hasProd 𝔪 ψ hs).mul hF)

variable {m : ℕ} [NeZero m] {ζ : 𝓞 L}

/-- **Reciprocity for cyclotomic characters**: at a prime `v ∤ m`, the Artin symbol of `ψ₀ ∘ κ`
is the value of the norm residue character `ψ₀ ∘ N̄` modulo `(m) ∞`. -/
theorem artinSymbol_cyclotomic_eq_heckeValue (hζ : IsPrimitiveRoot ζ m)
    (ψ₀ : (ZMod m)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (hv : (m : 𝓞 K) ∉ v.asIdeal) :
    artinSymbol K L (ψ₀.comp (cyclotomicCharacter (G := G) hζ)) v =
      heckeValue (normModulus K m) (normHeckeCharacter K m ψ₀) v.asIdeal := by
  rw [artinSymbol_cyclotomic K L hζ ψ₀ v hv, heckeValue_normHeckeCharacter, dif_neg hv]

/-- **The Artin Euler product of a cyclotomic character is a Hecke `L`-series**, up to the Euler
factors at the primes dividing `m`: for `Re s > 1`,
`L(s, ψ₀ ∘ κ, L/K) = L(s, ψ₀ ∘ N̄) · Π_{v | m} (1 − (ψ₀ ∘ κ, v) N(v)^{-s})^{-1}`. -/
theorem artinEulerProduct_cyclotomic_eq_heckeL_mul (hζ : IsPrimitiveRoot ζ m)
    (ψ₀ : (ZMod m)ˣ →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
      (linearCharacterLine (ψ₀.comp (cyclotomicCharacter (G := G) hζ))) s =
      heckeL (normModulus K m) (normHeckeCharacter K m ψ₀) s *
        ∏ v ∈ (finite_primes_dvd (normModulus K m)).toFinset,
          (1 - artinSymbol K L (ψ₀.comp (cyclotomicCharacter (G := G) hζ)) v *
            (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ :=
  artinEulerProduct_linearCharacter_eq_heckeL_mul K L _ _ _
    (fun v hv => artinSymbol_cyclotomic_eq_heckeValue K L hζ ψ₀ v
      fun h => hv ((dvd_normModulus_fin_iff K m v).mpr h)) hs

/-! ### Cyclotomic extensions -/

section Cyclotomic

variable {K L}

omit [NumberField L] [Fintype G] in
/-- An element in the kernel of the cyclotomic character fixes the root of unity. -/
theorem smul_eq_of_cyclotomicCharacter_eq_one (hζ : IsPrimitiveRoot ζ m) {σ : G}
    (h : cyclotomicCharacter hζ σ = 1) : σ • ζ = ζ := by
  have h1 := pow_cyclotomicCharacter_val hζ σ
  have h2 : ζ ^ (1 % m) = ζ := by
    have h3 := pow_mod_orderOf ζ 1
    rwa [← hζ.eq_orderOf, pow_one] at h3
  rw [h, Units.val_one, ZMod.val_one_eq_one_mod, h2] at h1
  exact h1.symm

omit [NumberField K] [NumberField L] [Fintype G] in
/-- **If `L = K(ζ)`, the cyclotomic character is injective**: an element of its kernel fixes
`K(ζ)`, and the Galois group acts faithfully. -/
theorem cyclotomicCharacter_injective (hζ : IsPrimitiveRoot ζ m)
    (hL : IntermediateField.adjoin K {(ζ : L)} = ⊤) :
    Function.Injective (cyclotomicCharacter (G := G) hζ) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : σ • (ζ : L) = ζ :=
    congrArg (fun x : 𝓞 L => (x : L)) (smul_eq_of_cyclotomicCharacter_eq_one hζ hσ)
  haveI : FaithfulSMul G L := IsGaloisGroup.faithful K
  -- the fixed field of the stabilizer of `ζ` contains `K(ζ) = L`
  have hle : IntermediateField.adjoin K {(ζ : L)} ≤
      (FixedPoints.intermediateField (MulAction.stabilizer G (ζ : L)) : IntermediateField K L) :=
    IntermediateField.adjoin_simple_le_iff.mpr fun g => g.2
  rw [hL] at hle
  refine eq_of_smul_eq_smul fun x : L => ?_
  rw [one_smul]
  exact hle IntermediateField.mem_top ⟨σ, hfix⟩

omit [NumberField L] [Fintype G] in
/-- If the cyclotomic character is injective, every linear character of the Galois group
factors through it: a character of a subgroup of `(ℤ/m)ˣ` extends to `(ℤ/m)ˣ`. -/
theorem exists_eq_comp_cyclotomicCharacter (hζ : IsPrimitiveRoot ζ m)
    (hκ : Function.Injective (cyclotomicCharacter (G := G) hζ)) (χ : LinearCharacter G) :
    ∃ ψ₀ : (ZMod m)ˣ →* ℂˣ, χ = ψ₀.comp (cyclotomicCharacter hζ) := by
  obtain ⟨ψ₀, hψ₀⟩ := MonoidHom.restrict_surjective ℂ (cyclotomicCharacter (G := G) hζ).range
    (χ.comp (MonoidHom.ofInjective hκ).symm.toMonoidHom)
  refine ⟨ψ₀, MonoidHom.ext fun g => ?_⟩
  have h := DFunLike.congr_fun hψ₀ (MonoidHom.ofInjective hκ g)
  simp only [MonoidHom.restrictHom_apply, MonoidHom.restrict_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply] at h
  rw [MonoidHom.comp_apply, h]

/-- **Abelian Artin Euler products of a cyclotomic extension are Hecke `L`-series.** If
`L = K(ζ)` for a primitive `m`-th root of unity `ζ`, then for every linear character `χ` of the
Galois group there is a ray class character `ψ` modulo `(m) ∞` with
`L(s, χ, L/K) = L(s, ψ) · Π_{v | m} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`. -/
theorem exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m)
    (hL : IntermediateField.adjoin K {(ζ : L)} = ⊤) (χ : LinearCharacter G) :
    ∃ ψ : HeckeCharacter (normModulus K m), ∀ s : ℂ, 1 < s.re →
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
        (linearCharacterLine χ) s = heckeL (normModulus K m) ψ s *
          ∏ v ∈ (finite_primes_dvd (normModulus K m)).toFinset,
            (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨ψ₀, rfl⟩ :=
    exists_eq_comp_cyclotomicCharacter hζ (cyclotomicCharacter_injective hζ hL) χ
  exact ⟨normHeckeCharacter K m ψ₀, fun s hs =>
    artinEulerProduct_cyclotomic_eq_heckeL_mul K L hζ ψ₀ hs⟩

end Cyclotomic

end GaloisForLFunctions
