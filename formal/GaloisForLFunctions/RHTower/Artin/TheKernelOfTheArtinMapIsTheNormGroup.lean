import GaloisForLFunctions.RHTower.Artin.TheArtinMapOfAnAbelianExtensionIsTrivialOnARay
import GaloisForLFunctions.RHTower.Artin.RayClassesBelowDegreeOnePrimesHaveIndexAtMostTheDegree
import GaloisForLFunctions.RHTower.Artin.TheArtinMapIsSurjective

/-!
# The kernel of the Artin map is the norm group

Let `L/K` be an abelian extension of number fields with group `G`, `𝔪` a modulus of `K`,
`I^𝔪` the ideals prime to `𝔪`, `P_𝔪` the ray, and

  `H_𝔪 = I^𝔪 ∩ P_𝔪 · N_{L/K}(I_L)`  (`normIdealGroup`).

* The Artin map kills the norms of the fractional ideals of `L` (`artinMap_idealNormHom`).
* **The first inequality** (`index_normIdealGroup_le`): `[I^𝔪 : H_𝔪] ≤ [L : K]`, for every
  finite extension: a prime of `K` below a prime of `L` of the same norm is a norm.
* **The kernel of the Artin map** (`ker_artinMap_comp_subtype`): if `𝔪` is divisible by the
  ramified primes and the Artin map is trivial on `P_𝔪`, its kernel on `I^𝔪` is `H_𝔪`: the
  kernel contains `H_𝔪`, has the index `[L : K]` (the Artin map is onto), and `H_𝔪` has at most
  this index.
* **Artin's reciprocity law** (`exists_mulEquiv_quotient_normIdealGroup`): there is `c ≥ 1`,
  divisible by the ramified primes, such that the Artin map induces an isomorphism
  `I^𝔪 / H_𝔪 ≅ G` for `𝔪 = (c) ∞`, and `[I^𝔪 : H_𝔪] = [L : K]`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors
open NumberField IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

section Index

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The norm group modulo `𝔪`: the ideals prime to `𝔪` that are the product of an ideal of the
ray and of the norm of a fractional ideal of `L`. -/
def normIdealGroup (𝔪 : Modulus K) : Subgroup (idealGroup 𝔪) :=
  (rayPrincipal 𝔪 ⊔ (idealNormHom K L).range).subgroupOf (idealGroup 𝔪)

variable {K} in
/-- A prime of `K` below a prime of `L` of the same norm is the norm of that prime. -/
theorem idealUnit_under_mem_range_idealNormHom {P : Ideal (𝓞 L)} (hP : P.IsPrime)
    (hN : Ideal.absNorm P = Ideal.absNorm (P.under (𝓞 K))) (h0 : P.under (𝓞 K) ≠ ⊥) :
    idealUnit h0 ∈ (idealNormHom K L).range := by
  have hP0 : P ≠ ⊥ := fun h =>
    h0 (Ideal.absNorm_eq_zero_iff.mp (by rw [← hN, h, Ideal.absNorm_bot]))
  haveI := hP
  -- the residue degree is one
  have hpow : Ideal.absNorm P =
      Ideal.absNorm (P.under (𝓞 K)) ^ P.inertiaDeg (𝓞 K) :=
    absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 L))
  have h2 : 2 ≤ Ideal.absNorm (P.under (𝓞 K)) :=
    two_le_absNorm_of_isPrime (inferInstance : (P.under (𝓞 K)).IsPrime) h0
  have hf : P.inertiaDeg (𝓞 K) = 1 := Nat.pow_right_injective h2 (by
    show Ideal.absNorm (P.under (𝓞 K)) ^ P.inertiaDeg (𝓞 K) =
      Ideal.absNorm (P.under (𝓞 K)) ^ 1
    rw [pow_one, ← hpow, hN])
  have h : idealNormHom K L (idealUnit hP0) = idealUnit h0 ^ P.inertiaDeg (𝓞 K) :=
    idealNormHom_idealUnit_prime K L (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 L))
  rw [hf, pow_one] at h
  exact ⟨idealUnit hP0, h⟩

variable (𝔪 : Modulus K)

/-- The classes modulo the norm group form a quotient of the ray class group. -/
def rayClassToNormClass : RayClassGroup 𝔪 →* idealGroup 𝔪 ⧸ normIdealGroup K L 𝔪 :=
  QuotientGroup.lift _ (QuotientGroup.mk' (normIdealGroup K L 𝔪)) fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))

theorem rayClassToNormClass_surjective : Function.Surjective (rayClassToNormClass K L 𝔪) :=
  fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨rayClass 𝔪 x, rfl⟩

/-- The norm group has finite index in the ideals prime to `𝔪`. -/
theorem finite_quotient_normIdealGroup : Finite (idealGroup 𝔪 ⧸ normIdealGroup K L 𝔪) :=
  Finite.of_surjective _ (rayClassToNormClass_surjective K L 𝔪)

theorem index_normIdealGroup_ne_zero : (normIdealGroup K L 𝔪).index ≠ 0 :=
  haveI := finite_quotient_normIdealGroup K L 𝔪
  Subgroup.index_ne_zero_of_finite

/-- **The first inequality**: `[I^𝔪 : I^𝔪 ∩ P_𝔪 N(I_L)] ≤ [L : K]`. -/
theorem index_normIdealGroup_le : (normIdealGroup K L 𝔪).index ≤ Module.finrank K L := by
  haveI := finite_quotient_normIdealGroup K L 𝔪
  refine card_le_finrank_of_forall_degreeOne_eq_one (L := L) 𝔪 (rayClassToNormClass K L 𝔪)
    (rayClassToNormClass_surjective K L 𝔪) fun P hP hN h0 hm => ?_
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_right (idealUnit_under_mem_range_idealNormHom L hP hN h0)))

end Index

variable (K L : Type u) (G : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **The Artin map kills the norms of the fractional ideals of `L`.** -/
theorem artinMap_idealNormHom (𝔄 : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    artinMap K L G (idealNormHom K L 𝔄) = 1 := by
  show (artinMap K L G).comp (primeValuesHom fun w : HeightOneSpectrum (𝓞 L) =>
    idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K)) 𝔄 = 1
  rw [comp_primeValuesHom]
  refine Subgroup.mem_bot.mp (primeValuesHom_mem ⊥ 𝔄 fun w _ => Subgroup.mem_bot.mpr ?_)
  show artinMap K L G (idealUnit (w.under (𝓞 K)).ne_bot ^ w.asIdeal.inertiaDeg (𝓞 K)) = 1
  haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  haveI := w.isMaximal
  rw [map_pow, artinMap_idealUnit_prime]
  exact frobeniusOrOne_pow_inertiaDeg K L G (w.under (𝓞 K)) w.asIdeal

variable (𝔪 : Modulus K)

/-- **The kernel of the Artin map is the norm group**, for a modulus divisible by the ramified
primes on whose ray the Artin map is trivial. -/
theorem ker_artinMap_comp_subtype
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v)
    (hrec : rayPrincipal 𝔪 ≤ (artinMap K L G).ker) :
    ((artinMap K L G).comp (idealGroup 𝔪).subtype).ker = normIdealGroup K L 𝔪 := by
  -- the norm group lies in the kernel
  have hle : normIdealGroup K L 𝔪 ≤ ((artinMap K L G).comp (idealGroup 𝔪).subtype).ker :=
    fun I hI => by
      obtain ⟨𝔞, h𝔞, _, ⟨𝔄, rfl⟩, h⟩ := Subgroup.mem_sup.mp (Subgroup.mem_subgroupOf.mp hI)
      refine MonoidHom.mem_ker.mpr ?_
      show artinMap K L G (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1
      rw [← h, map_mul, MonoidHom.mem_ker.mp (hrec h𝔞), artinMap_idealNormHom, mul_one]
  -- the kernel has the index `[L : K]`, the norm group at most this index
  have hmul := Subgroup.relIndex_mul_index hle
  rw [index_ker_artinMap K L G 𝔪 hram] at hmul
  have hpos : 0 < Module.finrank K L := by
    rw [← IsGaloisGroup.card_eq_finrank G K L]
    exact Nat.card_pos
  have h1 : (normIdealGroup K L 𝔪).relIndex
      ((artinMap K L G).comp (idealGroup 𝔪).subtype).ker ≠ 0 := fun h =>
    index_normIdealGroup_ne_zero K L 𝔪 (by rw [← hmul, h, zero_mul])
  have h2 : (normIdealGroup K L 𝔪).relIndex
      ((artinMap K L G).comp (idealGroup 𝔪).subtype).ker * Module.finrank K L ≤
      1 * Module.finrank K L := by
    rw [hmul, one_mul]
    exact index_normIdealGroup_le K L 𝔪
  exact le_antisymm (Subgroup.relIndex_eq_one.mp
    (le_antisymm (Nat.le_of_mul_le_mul_right h2 hpos) (Nat.one_le_iff_ne_zero.mpr h1))) hle

/-- The Artin map induces an isomorphism of the ideals prime to `𝔪` modulo the norm group with
the Galois group. -/
theorem exists_mulEquiv_quotient_normIdealGroup_of_rayPrincipal_le_ker
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v)
    (hrec : rayPrincipal 𝔪 ≤ (artinMap K L G).ker) :
    ∃ e : idealGroup 𝔪 ⧸ normIdealGroup K L 𝔪 ≃* G,
      ∀ I : idealGroup 𝔪, e (QuotientGroup.mk I) =
        artinMap K L G (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_artinMap_comp_subtype K L G 𝔪 hram hrec).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (MonoidHom.range_eq_top.mp (range_artinMap_comp_subtype K L G 𝔪 hram))), fun _ => rfl⟩

/-- **Artin's reciprocity law for abelian extensions.** For an abelian extension `L/K` of
number fields with group `G` there is `c ≥ 1`, divisible by the ramified primes, such that for
`𝔪 = (c) ∞` the kernel of the Artin map on the ideals prime to `𝔪` is the norm group
`I^𝔪 ∩ P_𝔪 N(I_L)`; the norm group has the index `[L : K]`, and the Artin map induces an
isomorphism of the quotient with `G`. -/
theorem exists_mulEquiv_quotient_normIdealGroup :
    ∃ (c : ℕ) (_ : NeZero c),
      (∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∉ v.asIdeal → IsUnramifiedPrime K L G v) ∧
      ((artinMap K L G).comp (idealGroup (normModulus K c)).subtype).ker =
        normIdealGroup K L (normModulus K c) ∧
      (normIdealGroup K L (normModulus K c)).index = Module.finrank K L ∧
      ∃ e : idealGroup (normModulus K c) ⧸ normIdealGroup K L (normModulus K c) ≃* G,
        ∀ I : idealGroup (normModulus K c), e (QuotientGroup.mk I) =
          artinMap K L G (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  obtain ⟨c, hc, hram, hrec⟩ := exists_rayPrincipal_le_ker_artinMap K L G
  have hram' : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ (normModulus K c).fin →
      IsUnramifiedPrime K L G v := fun v hv =>
    hram v fun h => hv ((dvd_normModulus_fin_iff K c v).mpr h)
  have hker := ker_artinMap_comp_subtype K L G (normModulus K c) hram' hrec
  refine ⟨c, hc, hram, hker, ?_,
    exists_mulEquiv_quotient_normIdealGroup_of_rayPrincipal_le_ker K L G (normModulus K c)
      hram' hrec⟩
  rw [← hker]
  exact index_ker_artinMap K L G (normModulus K c) hram'

end GaloisForLFunctions
