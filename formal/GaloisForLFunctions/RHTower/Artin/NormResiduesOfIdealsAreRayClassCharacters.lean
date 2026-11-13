import GaloisForLFunctions.RHTower.Artin.ArtinSymbolOfACyclotomicCharacterIsTheNormResidue
import GaloisForLFunctions.RHTower.Artin.NormsOfTotallyPositiveElementsArePositive
import GaloisForLFunctions.HeckeLFunctions.RayClassesOfPrincipalIdealsAreReadByResidues

/-!
# Norm residues of ideals are ray class characters

Let `K` be a number field and `m ≥ 1`. The modulus `𝔪 = (m) ∞` (`normModulus`) has finite part
`m 𝓞_K` and contains every real place.

* A function `u` on the primes extends to a homomorphism on the group of fractional ideals,
  `I ↦ Π_v u(v)^{v(I)}` (`primeValuesHom`).
* **The norm residue** `N̄ : I^𝔪 → (ℤ/m)ˣ` (`normResidueHom`) has `N̄(v) = N(v) mod m` at the
  primes `v ∤ m`. On an integral ideal prime to `m` it is the residue of the norm
  (`coe_primeValuesHom_normResidueUnit_idealUnit`).
* **The norm residue is trivial on the ray** (`normResidueHom_eq_one_of_mem`): let
  `α ≡ 1 mod^× m` be totally positive, `α = a/b`. Then `N(a) ≡ N(b) mod m`, and `N(a)`, `N(b)`
  have the same sign, so `|N(a)| ≡ |N(b)|`.
* Hence a character `ψ₀` of `(ℤ/m)ˣ` gives the ray class character `ψ₀ ∘ N̄` modulo `𝔪`
  (`normHeckeCharacter`). Its value is `ψ₀(N(v) mod m)` at the primes `v ∤ m` and `0` at the
  primes `v | m` (`heckeValue_normHeckeCharacter`).
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

namespace GaloisForLFunctions

open HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Homomorphisms on fractional ideals from values on the primes -/

section PrimeValues

variable {A : Type*} [CommGroup A] (u : HeightOneSpectrum (𝓞 K) → A)

theorem finite_mulSupport_zpow_count (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v => u v ^ count K v I).Finite :=
  (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset fun v hv h0 =>
    hv (by show u v ^ count K v I = 1; rw [h0, zpow_zero])

/-- The homomorphism on the group of fractional ideals with given values on the primes:
`I ↦ Π_v u(v)^{v(I)}`. -/
def primeValuesHom : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* A where
  toFun I := ∏ᶠ v, u v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K)
  map_one' := by
    simp only [Units.val_one, count_one, zpow_zero, finprod_one]
  map_mul' I J := by
    rw [← finprod_mul_distrib (finite_mulSupport_zpow_count u _)
      (finite_mulSupport_zpow_count u _)]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, zpow_add]

theorem primeValuesHom_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    primeValuesHom u I = ∏ᶠ v, u v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

/-- The value at a prime. -/
theorem primeValuesHom_idealUnit_prime (v : HeightOneSpectrum (𝓞 K)) :
    primeValuesHom u (idealUnit v.ne_bot) = u v := by
  have h1 : ∀ w, w ≠ v → u w ^ count K w
      ((idealUnit v.ne_bot : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 1 :=
    fun w hw => by rw [coe_idealUnit, count_maximal_coprime K w hw.symm, zpow_zero]
  rw [primeValuesHom_apply, finprod_eq_single _ v h1, coe_idealUnit, count_self, zpow_one]

end PrimeValues

/-- Integers that are congruent modulo `m`, non-zero and of the same sign have congruent
absolute values. -/
theorem natCast_natAbs_eq_of_sign {m : ℕ} {x y : ℤ} (h : (x : ZMod m) = (y : ZMod m))
    (hs : 0 < x ↔ 0 < y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((x.natAbs : ℕ) : ZMod m) = ((y.natAbs : ℕ) : ZMod m) := by
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  by_cases hpos : 0 < x
  · rw [abs_of_pos hpos, abs_of_pos (hs.mp hpos), h]
  · have hx' : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    have hy' : y < 0 := lt_of_le_of_ne (not_lt.mp fun h' => hpos (hs.mpr h')) hy
    rw [abs_of_neg hx', abs_of_neg hy', Int.cast_neg, Int.cast_neg, h]

/-! ### The norm residue -/

variable (K) (m : ℕ) [NeZero m]

/-- The modulus `(m) ∞`: finite part `m 𝓞_K`, and every real place. -/
def normModulus : Modulus K :=
  ⟨Ideal.span {(m : 𝓞 K)}, by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact NeZero.ne m, Set.univ⟩

theorem dvd_normModulus_fin_iff (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ (normModulus K m).fin ↔ (m : 𝓞 K) ∈ v.asIdeal :=
  Ideal.dvd_span_singleton

/-- The residue of the norm of a prime: `N(v) mod m` for `v ∤ m`, and `1` for `v | m`. -/
def normResidueUnit (v : HeightOneSpectrum (𝓞 K)) : (ZMod m)ˣ :=
  if h : (m : 𝓞 K) ∈ v.asIdeal then 1
  else ZMod.unitOfCoprime _ (absNorm_coprime_of_natCast_notMem v h)

/-- **On an integral ideal prime to `m`, the norm residue is the residue of the norm**, by
induction on the prime factors. -/
theorem coe_primeValuesHom_normResidueUnit_idealUnit {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hm : idealUnit hI ∈ idealGroup (normModulus K m)) :
    ((primeValuesHom (normResidueUnit K m) (idealUnit hI) : (ZMod m)ˣ) : ZMod m) =
      (Ideal.absNorm I : ZMod m) := by
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun I : Ideal (𝓞 K) => ∀ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup (normModulus K m) →
      ((primeValuesHom (normResidueUnit K m) (idealUnit hI) : (ZMod m)ˣ) : ZMod m) =
        (Ideal.absNorm I : ZMod m)) I ?_ ?_ ?_
  · intro hI
    exact (hI Ideal.zero_eq_bot).elim
  · intro J hJ hI _
    obtain rfl : J = ⊤ := Ideal.isUnit_iff.mp hJ
    have h1 : idealUnit hI = 1 :=
      Units.ext (by rw [coe_idealUnit, Units.val_one, coeIdeal_top])
    rw [h1, map_one, Units.val_one, Ideal.absNorm_top, Nat.cast_one]
  · intro J P hJ0 hP ih hI hm
    have hJ0' : J ≠ ⊥ := hJ0
    obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal = P :=
      ⟨⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩, rfl⟩
    obtain ⟨hmP, hmJ⟩ := (idealUnit_mul_mem_iff (normModulus K m) v.ne_bot hJ0').mp hm
    -- `v` does not divide `m`
    have hv : (m : 𝓞 K) ∉ v.asIdeal := fun h => by
      have h0 := hmP v ((dvd_normModulus_fin_iff K m v).mpr h)
      rw [coe_idealUnit, count_self] at h0
      exact one_ne_zero h0
    have hunit : idealUnit hI = idealUnit v.ne_bot * idealUnit hJ0' :=
      idealUnit_mul v.ne_bot hJ0'
    rw [hunit, map_mul (primeValuesHom (normResidueUnit K m)), Units.val_mul, ih hJ0' hmJ,
      primeValuesHom_idealUnit_prime, normResidueUnit, dif_neg hv, ZMod.coe_unitOfCoprime,
      map_mul Ideal.absNorm, Nat.cast_mul]

/-- The norm residue of the principal ideal of an integer prime to `m` is the residue of the
absolute value of its norm. -/
theorem coe_primeValuesHom_normResidueUnit_span {a : 𝓞 K} (hspan : Ideal.span {a} ≠ ⊥)
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K m).fin → a ∉ v.asIdeal) :
    ((primeValuesHom (normResidueUnit K m) (idealUnit hspan) : (ZMod m)ˣ) : ZMod m) =
      ((Algebra.norm ℤ a).natAbs : ZMod m) := by
  have hmem : idealUnit hspan ∈ idealGroup (normModulus K m) := fun v hv => by
    rw [coe_idealUnit, count_coe_eq_zero_iff hspan v, Ideal.dvd_span_singleton]
    exact ha v hv
  rw [coe_primeValuesHom_normResidueUnit_idealUnit K m hspan hmem, Ideal.absNorm_span_singleton]

/-- **The norm residue** on the ideals prime to `m`. -/
def normResidueHom : idealGroup (normModulus K m) →* (ZMod m)ˣ :=
  (primeValuesHom (normResidueUnit K m)).comp (idealGroup (normModulus K m)).subtype

/-- **The norm residue is trivial on the ray modulo `(m) ∞`.** -/
theorem normResidueHom_eq_one_of_mem (I : idealGroup (normModulus K m))
    (hI : I ∈ (rayPrincipal (normModulus K m)).subgroupOf (idealGroup (normModulus K m))) :
    normResidueHom K m I = 1 := by
  rw [Subgroup.mem_subgroupOf] at hI
  obtain ⟨α₀, hα₀, hαI⟩ := hI
  obtain ⟨α, hα, rfl⟩ := hα₀
  have hα' : rayHom (normModulus K m) α = 1 := hα
  rw [rayHom, MonoidHom.prod_apply, Prod.mk_eq_one] at hα'
  obtain ⟨hred, hsign⟩ := hα'
  -- a unit fraction `α = a/b`
  obtain ⟨hb0, hab, hfrac⟩ := unitFraction_spec (normModulus K m) α
  generalize (unitFraction (normModulus K m) α).1 = a at hab hfrac
  generalize (unitFraction (normModulus K m) α).2 = b at hb0 hab hfrac
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K m).fin → a ∉ v.asIdeal :=
    fun v hv => (hab v hv).1
  have hb : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ (normModulus K m).fin → b ∉ v.asIdeal :=
    fun v hv => (hab v hv).2
  have hαK : (((α : primeToUnits (normModulus K m)) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := fun h => by
    have hne : algebraMap (𝓞 K) K b * (((α : primeToUnits (normModulus K m)) : Kˣ) : K) ≠ 0 :=
      mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hb0) hαK
    rw [hfrac, h, map_zero] at hne
    exact hne rfl
  -- `a ≡ b` modulo `m`
  have hsub : a - b ∈ Ideal.span {(m : 𝓞 K)} := by
    have h1 : unitMod (normModulus K m) ha = unitMod (normModulus K m) hb :=
      mul_inv_eq_one.mp ((reduce_eq (normModulus K m) α ha hb hfrac).symm.trans hred)
    exact Ideal.Quotient.eq.mp (congrArg Units.val h1)
  -- `α` is positive at every real place, so its norm is positive
  have hNα : 0 < Algebra.norm ℚ (((α : primeToUnits (normModulus K m)) : Kˣ) : K) := by
    refine norm_pos_of_forall_isReal_pos hαK fun w hw => ?_
    by_contra hneg
    have h1 : signAtInf (normModulus K m) ((primeToUnits (normModulus K m)).subtype α)
        ⟨⟨w, hw⟩, Set.mem_univ _⟩ = 1 := congrFun hsign _
    have h2 : signAtInf (normModulus K m) ((primeToUnits (normModulus K m)).subtype α)
        ⟨⟨w, hw⟩, Set.mem_univ _⟩ = -1 := (signAtInf_apply _ _ _).trans (if_neg hneg)
    exact absurd (h2.symm.trans h1) (by decide)
  have hN : ((Algebra.norm ℤ b : ℤ) : ℚ) *
      Algebra.norm ℚ (((α : primeToUnits (normModulus K m)) : Kˣ) : K) =
      ((Algebra.norm ℤ a : ℤ) : ℚ) := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← map_mul (Algebra.norm ℚ)]
    exact congrArg (Algebra.norm ℚ) hfrac
  have hs : 0 < Algebra.norm ℤ a ↔ 0 < Algebra.norm ℤ b := by
    have h1 : (0 : ℚ) < ((Algebra.norm ℤ a : ℤ) : ℚ) ↔ (0 : ℚ) < ((Algebra.norm ℤ b : ℤ) : ℚ) := by
      rw [← hN]
      exact mul_pos_iff_of_pos_right hNα
    exact_mod_cast h1
  have hspana : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha0
  have hspanb : Ideal.span {b} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hb0
  -- `(α)(b) = (a)`, and `(a)`, `(b)` have the same norm residue
  have hmul : toPrincipalIdeal (𝓞 K) K ((primeToUnits (normModulus K m)).subtype α) *
      idealUnit hspanb = idealUnit hspana := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_toPrincipalIdeal, coe_idealUnit, coe_idealUnit,
      coeIdeal_span_singleton, coeIdeal_span_singleton, spanSingleton_mul_spanSingleton,
      ← hfrac, mul_comm]
    rfl
  have hval : primeValuesHom (normResidueUnit K m) (idealUnit hspana) =
      primeValuesHom (normResidueUnit K m) (idealUnit hspanb) := by
    refine Units.ext ?_
    rw [coe_primeValuesHom_normResidueUnit_span K m hspana ha,
      coe_primeValuesHom_normResidueUnit_span K m hspanb hb]
    exact natCast_natAbs_eq_of_sign (intCast_norm_eq_of_sub_mem hsub) hs
      ((Algebra.norm_ne_zero_iff).mpr ha0) ((Algebra.norm_ne_zero_iff).mpr hb0)
  have h1 := congrArg (primeValuesHom (normResidueUnit K m)) hmul
  rw [map_mul, hval, hαI] at h1
  exact mul_right_cancel (h1.trans (one_mul _).symm)

/-- The norm residue on the ray classes modulo `(m) ∞`. -/
def normResidueClass : RayClassGroup (normModulus K m) →* (ZMod m)ˣ :=
  QuotientGroup.lift _ (normResidueHom K m) fun I hI =>
    MonoidHom.mem_ker.mpr (normResidueHom_eq_one_of_mem K m I hI)

/-- **The ray class character of a norm residue character**: `ψ₀ ∘ N̄` modulo `(m) ∞`, for a
character `ψ₀` of `(ℤ/m)ˣ`. -/
def normHeckeCharacter (ψ₀ : (ZMod m)ˣ →* ℂˣ) : HeckeCharacter (normModulus K m) :=
  ψ₀.comp (normResidueClass K m)

/-- **The values of the norm residue character on the primes**: `ψ₀(N(v) mod m)` for `v ∤ m`,
and `0` for `v | m`. -/
theorem heckeValue_normHeckeCharacter (ψ₀ : (ZMod m)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    heckeValue (normModulus K m) (normHeckeCharacter K m ψ₀) v.asIdeal =
      if h : (m : 𝓞 K) ∈ v.asIdeal then 0
      else (ψ₀ (ZMod.unitOfCoprime _ (absNorm_coprime_of_natCast_notMem v h)) : ℂ) := by
  by_cases hv : (m : 𝓞 K) ∈ v.asIdeal
  · rw [dif_pos hv]
    apply heckeValue_of_not_mem
    rintro ⟨hI, hm⟩
    have h := hm v ((dvd_normModulus_fin_iff K m v).mpr hv)
    rw [coe_idealUnit, count_self] at h
    exact one_ne_zero h
  · rw [dif_neg hv]
    have hm : idealUnit v.ne_bot ∈ idealGroup (normModulus K m) := by
      intro w hw
      rw [coe_idealUnit]
      refine count_maximal_coprime K w fun h => hv ?_
      rw [h]
      exact (dvd_normModulus_fin_iff K m w).mp hw
    rw [heckeValue_of_mem _ _ v.ne_bot hm]
    show ((ψ₀ (primeValuesHom (normResidueUnit K m) (idealUnit v.ne_bot)) : ℂˣ) : ℂ) = _
    rw [primeValuesHom_idealUnit_prime, normResidueUnit, dif_neg hv]

end GaloisForLFunctions
