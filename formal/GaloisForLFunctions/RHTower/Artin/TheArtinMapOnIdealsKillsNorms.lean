import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfACyclotomicCharacterIsAHeckeLSeries
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# The Artin map on ideals kills norms

Let `L/K` be an abelian extension of number fields with group `G`.

* **The Frobenius element of an unramified prime** `v` of `K` does not depend on the prime of
  `L` above `v` (`arithFrobAt_eq_frobeniusElement`): the Frobenius elements of two primes above
  `v` are conjugate, hence equal modulo inertia.
* **The Artin map** `(·, L/K) : I_K → G` (`artinMap`) is the homomorphism on the fractional
  ideals of `K` with value `Frob_v` at the unramified primes and `1` at the ramified ones. The
  Artin symbol of a linear character `χ` at an unramified `v` is `χ(Frob_v)`
  (`artinSymbol_eq_apply_frobeniusElement`).
* **Norms are in the kernel** (`artinMap_idealUnit_relNorm`): `(N_{L/K} 𝔄, L/K) = 1` for every
  ideal `𝔄 ≠ 0` of `L`. For a prime `P` above `v`, `N(P) = v^f` and `Frob_v^f` acts trivially
  on the residue field of `P`, so it lies in the inertia group
  (`arithFrobAt_pow_inertiaDeg_mem_inertia`).
* **The reciprocity law in terms of the Artin map**
  (`artinEulerProduct_eq_heckeL_mul_of_rayPrincipal_le_ker`). If `𝔪` is divisible by the
  ramified primes and the Artin map is trivial on the ray modulo `𝔪`, then `χ ∘ (·, L/K)` is a
  ray class character `ψ` modulo `𝔪` (`artinHeckeCharacter`) and
  `L(s, χ, L/K) = L(s, ψ) · Π_{v | 𝔪} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors Pointwise
open Polynomial IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions

attribute [local instance] Ideal.Quotient.field

/-- The unit of a power of an ideal is the power of its unit. -/
theorem idealUnit_pow {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (n : ℕ) (hn : I ^ n ≠ ⊥) : idealUnit hn = idealUnit hI ^ n :=
  Units.ext (by rw [coe_idealUnit, Units.val_pow_eq_pow_val, coe_idealUnit, coeIdeal_pow])

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-! ### Frobenius elements -/

/-- The prime `v` of `K` is unramified in `L`: the primes of `L` above `v` have trivial inertia
groups. -/
def IsUnramifiedPrime (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.LiesOver v.asIdeal → Q.inertia G = ⊥

omit [NumberField L] in
/-- Every prime of `K` lies below a prime of `L`. -/
theorem exists_isMaximal_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ Q.LiesOver v.asIdeal :=
  haveI := v.isMaximal
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal

/-- A prime of `L` above the prime `v` of `K`. -/
def primeAbove (v : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 L) :=
  (exists_isMaximal_liesOver K L v).choose

instance primeAbove_isMaximal (v : HeightOneSpectrum (𝓞 K)) : (primeAbove K L v).IsMaximal :=
  (exists_isMaximal_liesOver K L v).choose_spec.1

instance primeAbove_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K L v).LiesOver v.asIdeal :=
  (exists_isMaximal_liesOver K L v).choose_spec.2

/-- The Frobenius element of `v`: the Frobenius element of a prime of `L` above `v`. -/
def frobeniusElement (v : HeightOneSpectrum (𝓞 K)) : G :=
  arithFrobAt (𝓞 K) G (primeAbove K L v)

variable {K L G}

/-- **The Frobenius element of an unramified prime does not depend on the prime above it.** -/
theorem arithFrobAt_eq_frobeniusElement {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsUnramifiedPrime K L G v) (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q.LiesOver v.asIdeal] :
    arithFrobAt (𝓞 K) G Q = frobeniusElement K L G v := by
  have hunder : (primeAbove K L v).under (𝓞 K) = Q.under (𝓞 K) := by
    rw [← Ideal.over_def (primeAbove K L v) v.asIdeal, ← Ideal.over_def Q v.asIdeal]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) G
    (primeAbove K L v) Q hunder
  -- the Frobenius element of the chosen prime is a Frobenius element at its conjugate `Q`
  have h1 := (IsArithFrobAt.arithFrobAt (𝓞 K) G (primeAbove K L v)).conj g
  rw [mul_comm g, mul_inv_cancel_right, ← hg] at h1
  have h2 := (IsArithFrobAt.arithFrobAt (𝓞 K) G Q).mul_inv_mem_inertia h1
  rw [hv Q inferInstance inferInstance, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.mp h2

/-- **The Artin symbol of a linear character at an unramified prime** is the value of the
character at the Frobenius element. -/
theorem artinSymbol_eq_apply_frobeniusElement (χ : LinearCharacter G)
    {v : HeightOneSpectrum (𝓞 K)} (hv : IsUnramifiedPrime K L G v) :
    artinSymbol K L χ v = χ (frobeniusElement K L G v) := by
  have h : ∀ τ ∈ (primeAbove K L v).inertia G, χ τ = 1 := fun τ hτ => by
    rw [hv _ inferInstance inferInstance, Subgroup.mem_bot] at hτ
    rw [hτ, map_one]
  rw [artinSymbol_eq_frobeniusValue K L χ v (primeAbove K L v), frobeniusValue, if_pos h]
  rfl

/-- **The power `Frob^f` of the Frobenius element of `Q` lies in the inertia group**, for `f`
the residue degree: it acts on the residue field, of `q^f` elements, as the power `q^f`. -/
theorem arithFrobAt_pow_inertiaDeg_mem_inertia (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥) :
    arithFrobAt (𝓞 K) G Q ^ Q.inertiaDeg (𝓞 K) ∈ Q.inertia G := by
  refine fun c => ?_
  have hcard : Nat.card (𝓞 L ⧸ Q) =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ Q.inertiaDeg (𝓞 K) := by
    have h := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K)
      (⟨Q, inferInstance, hQ0⟩ : HeightOneSpectrum (𝓞 L))
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] at h
  haveI : Fintype (𝓞 L ⧸ Q) := Fintype.ofFinite _
  refine Ideal.Quotient.eq.mp ?_
  rw [mk_pow_smul_eq_pow (IsArithFrobAt.arithFrobAt (𝓞 K) G Q), ← hcard,
    Nat.card_eq_fintype_card]
  exact FiniteField.pow_card _

/-! ### The Artin map -/

variable (K L G)

/-- The values of the Artin map on the primes: the Frobenius element at an unramified prime,
and `1` at a ramified one. -/
def frobeniusOrOne (v : HeightOneSpectrum (𝓞 K)) : G :=
  if IsUnramifiedPrime K L G v then frobeniusElement K L G v else 1

/-- **The Artin map** on the fractional ideals of `K`. -/
def artinMap : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* G := primeValuesHom (frobeniusOrOne K L G)

theorem artinMap_idealUnit_prime (v : HeightOneSpectrum (𝓞 K)) :
    artinMap K L G (idealUnit v.ne_bot) = frobeniusOrOne K L G v :=
  primeValuesHom_idealUnit_prime _ v

/-- The value of the Artin map at a prime is killed by the residue degree of a prime above. -/
theorem frobeniusOrOne_pow_inertiaDeg (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L))
    [Q.IsMaximal] [Q.LiesOver v.asIdeal] :
    frobeniusOrOne K L G v ^ Q.inertiaDeg (𝓞 K) = 1 := by
  unfold frobeniusOrOne
  split_ifs with hv
  · rw [← arithFrobAt_eq_frobeniusElement hv Q, ← Subgroup.mem_bot,
      ← hv Q inferInstance inferInstance]
    exact arithFrobAt_pow_inertiaDeg_mem_inertia Q
      (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  · exact one_pow _

/-- **The Artin map kills the norms of the ideals of `L`.** -/
theorem artinMap_idealUnit_relNorm (𝔄 : Ideal (𝓞 L)) (hN : Ideal.relNorm (𝓞 K) 𝔄 ≠ ⊥) :
    artinMap K L G (idealUnit hN) = 1 := by
  revert hN
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun 𝔄 : Ideal (𝓞 L) => ∀ hN : Ideal.relNorm (𝓞 K) 𝔄 ≠ ⊥,
      artinMap K L G (idealUnit hN) = 1) 𝔄 ?_ ?_ ?_
  · intro hN
    exact (hN (by rw [Ideal.zero_eq_bot, Ideal.relNorm_bot])).elim
  · intro J hJ hN
    obtain rfl : J = ⊤ := Ideal.isUnit_iff.mp hJ
    have h1 : idealUnit hN = 1 :=
      Units.ext (by rw [coe_idealUnit, Units.val_one, Ideal.relNorm_top, coeIdeal_top])
    rw [h1, map_one]
  · intro J P hJ0 hP ih hN
    have hJ0' : J ≠ ⊥ := hJ0
    haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hP
    have hP0 : P ≠ ⊥ := hP.ne_zero
    haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0
    -- the prime `v` of `K` below `P`: `N(P) = v^f`
    obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal = P.under (𝓞 K) :=
      ⟨(⟨P, hPprime, hP0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 K), rfl⟩
    haveI : P.LiesOver v.asIdeal := ⟨hv⟩
    haveI := v.isMaximal
    have hNP : Ideal.relNorm (𝓞 K) P = v.asIdeal ^ P.inertiaDeg (𝓞 K) :=
      Ideal.relNorm_eq_pow_of_isMaximal P v.asIdeal
    have hNJ : Ideal.relNorm (𝓞 K) J ≠ ⊥ := fun h => hJ0' (Ideal.relNorm_eq_bot_iff.mp h)
    have hunit : idealUnit hN = idealUnit v.ne_bot ^ P.inertiaDeg (𝓞 K) * idealUnit hNJ :=
      Units.ext (by
        rw [coe_idealUnit, Units.val_mul, Units.val_pow_eq_pow_val, coe_idealUnit,
          coe_idealUnit, map_mul, hNP, coeIdeal_mul, coeIdeal_pow])
    rw [hunit, map_mul, map_pow, artinMap_idealUnit_prime, ih hNJ, mul_one,
      frobeniusOrOne_pow_inertiaDeg K L G v P]

/-! ### The reciprocity law in terms of the Artin map -/

variable (𝔪 : Modulus K) (hrec : rayPrincipal 𝔪 ≤ (artinMap K L G).ker)

/-- The ray class character `χ ∘ (·, L/K)`, when the Artin map is trivial on the ray modulo
`𝔪`. -/
def artinHeckeCharacter (χ : LinearCharacter G) : HeckeCharacter 𝔪 :=
  QuotientGroup.lift _ (χ.comp ((artinMap K L G).comp (idealGroup 𝔪).subtype)) fun I hI =>
    MonoidHom.mem_ker.mpr (by
      show χ (artinMap K L G (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) = 1
      rw [MonoidHom.mem_ker.mp (hrec (Subgroup.mem_subgroupOf.mp hI)), map_one])

/-- The values of `χ ∘ (·, L/K)` at the primes outside the modulus are the Artin symbols of
`χ`. -/
theorem heckeValue_artinHeckeCharacter
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v)
    (χ : LinearCharacter G) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪.fin) :
    heckeValue 𝔪 (artinHeckeCharacter K L G 𝔪 hrec χ) v.asIdeal = artinSymbol K L χ v := by
  have hm : idealUnit v.ne_bot ∈ idealGroup 𝔪 := by
    intro w hw
    rw [coe_idealUnit]
    refine count_maximal_coprime K w fun h => hv ?_
    rw [h]
    exact hw
  rw [heckeValue_of_mem _ _ v.ne_bot hm, artinSymbol_eq_apply_frobeniusElement χ (hram v hv)]
  show ((χ (artinMap K L G (idealUnit v.ne_bot)) : ℂˣ) : ℂ) = _
  rw [artinMap_idealUnit_prime, frobeniusOrOne, if_pos (hram v hv)]

/-- **The reciprocity law in terms of the Artin map.** If the modulus `𝔪` is divisible by the
ramified primes and the Artin map is trivial on the ray modulo `𝔪`, the Euler product of a
linear character `χ` is the Hecke `L`-series of `χ ∘ (·, L/K)` up to the factors at `v | 𝔪`. -/
theorem artinEulerProduct_eq_heckeL_mul_of_rayPrincipal_le_ker
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v)
    (χ : LinearCharacter G) {s : ℂ} (hs : 1 < s.re) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L)
      (linearCharacterLine χ) s = heckeL 𝔪 (artinHeckeCharacter K L G 𝔪 hrec χ) s *
        ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
          (1 - artinSymbol K L χ v * (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ :=
  artinEulerProduct_linearCharacter_eq_heckeL_mul K L χ 𝔪 _
    (fun v hv => (heckeValue_artinHeckeCharacter K L G 𝔪 hrec hram χ v hv).symm) hs

end GaloisForLFunctions
