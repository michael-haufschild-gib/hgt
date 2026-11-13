import GaloisForLFunctions.RHTower.Artin.TheArtinMapOnIdealsKillsNorms
import GaloisForLFunctions.RHTower.Artin.ExtensionsInWhichAlmostAllPrimesSplitCompletelyAreTrivial

/-!
# The Artin map is surjective

Let `L/K` be an abelian extension of number fields with group `G`.

* **The Frobenius elements generate** (`eq_top_of_forall_frobeniusElement_mem`). A subgroup
  `H` of `G` that contains the Frobenius elements of all primes of norm `> B`, all of them
  unramified, is `G`.
* **The Artin map is onto** (`exists_mem_idealGroup_artinMap_eq`): for a modulus `𝔪` divisible
  by the ramified primes, every element of `G` is the Artin symbol of an ideal prime to `𝔪`.
  The kernel on these ideals has index `[L : K]` (`index_ker_artinMap`).

Proof. Let `M` be the fixed field of `H` and `P` a prime of `M` above `v`, `N(v) > B`, below a
prime `Q` of `L`. The Frobenius element `σ` of `Q` lies in `H`, so it fixes `M`; it acts on the
residue field of `Q` as `x ↦ x^{N(v)}`, so `x^{N(v)} = x` on the residue field of `P`, which
therefore has at most `N(v)` elements: `N(P) = N(v)` (`absNorm_under_eq_of_isArithFrobAt_fixes`).
The ramification index of `Q` over `K` is the order of its inertia group, `1`, and it is
divisible by that of `P` (`ramificationIdx_under_eq_one_of_inertia_eq_bot`). So almost all
primes of `K` split completely in `M`, and `M = K`.
-/

open scoped Classical BigOperators NumberField nonZeroDivisors Pointwise
open Polynomial IsDedekindDomain FractionalIdeal

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

attribute [local instance] Ideal.Quotient.field

/-- A finite field on which `x ↦ x^q` is the identity has at most `q` elements. -/
theorem natCard_le_of_forall_pow_eq {F : Type*} [Field F] [Finite F] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  calc Nat.card F = (Finset.univ : Finset F).card := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ (X ^ q - X : F[X]).roots.toFinset.card := Finset.card_le_card fun x _ => by
        rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X, h x,
          sub_self]
    _ ≤ Multiset.card (X ^ q - X : F[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : F[X]).natDegree := card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq F hq

variable {K L : Type u} {G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-! ### Intermediate fields fixed by the Frobenius elements -/

section Intermediate

variable (M : Type u) [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]

omit [Fintype G] in
/-- **A prime of `M` below a prime of `L` whose Frobenius element fixes `M` has residue degree
one over `K`.** -/
theorem absNorm_under_eq_of_isArithFrobAt_fixes (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    {σ : G} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hfix : ∀ x : M, σ • algebraMap M L x = algebraMap M L x) :
    Ideal.absNorm (Q.under (𝓞 M)) = Ideal.absNorm (Q.under (𝓞 K)) := by
  let w : HeightOneSpectrum (𝓞 M) :=
    (⟨Q, inferInstance, hQ0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 M)
  have hw : w.asIdeal = Q.under (𝓞 M) := rfl
  haveI : (Q.under (𝓞 M)).IsMaximal := hw ▸ w.isMaximal
  have hunder : (Q.under (𝓞 M)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under _
  have h2M := two_le_absNorm_of_isPrime w.isPrime w.ne_bot
  have h2K := two_le_absNorm_of_isPrime (w.under (𝓞 K)).isPrime (w.under (𝓞 K)).ne_bot
  have hpow := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) w
  rw [hw] at h2M hpow
  change 2 ≤ Ideal.absNorm ((Q.under (𝓞 M)).under (𝓞 K)) at h2K
  change Ideal.absNorm (Q.under (𝓞 M)) =
    Ideal.absNorm ((Q.under (𝓞 M)).under (𝓞 K)) ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) at hpow
  rw [hunder] at h2K hpow
  -- `x^{N(v)} = x` on the residue field of `Q ∩ M`
  have hq : ∀ x : 𝓞 M ⧸ Q.under (𝓞 M), x ^ Ideal.absNorm (Q.under (𝓞 K)) = x := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : σ • algebraMap (𝓞 M) (𝓞 L) b = algebraMap (𝓞 M) (𝓞 L) b :=
      NumberField.RingOfIntegers.ext (hfix (b : M))
    have h1 := hσ (algebraMap (𝓞 M) (𝓞 L) b)
    rw [MulSemiringAction.toAlgHom_apply, hb, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, ← map_pow, ← map_sub] at h1
    rw [← map_pow]
    exact (Ideal.Quotient.eq.mpr h1).symm
  have hle : Ideal.absNorm (Q.under (𝓞 M)) ≤ Ideal.absNorm (Q.under (𝓞 K)) := by
    have h := natCard_le_of_forall_pow_eq (by omega) hq
    rwa [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h
  -- `N(Q ∩ M) = N(v)^f ≥ N(v)`
  have hf : (Q.under (𝓞 M)).inertiaDeg (𝓞 K) ≠ 0 := fun h0 => by
    rw [h0, pow_zero] at hpow
    omega
  exact le_antisymm hle (hpow ▸ Nat.le_self_pow hf _)

/-- **A prime of `M` below a prime of `L` with trivial inertia group is unramified over `K`.** -/
theorem ramificationIdx_under_eq_one_of_inertia_eq_bot (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hI : Q.inertia G = ⊥) : (Q.under (𝓞 M)).ramificationIdx (𝓞 K) = 1 := by
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under (𝓞 K)) Q
  have h2 := Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q G
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (Q.under (𝓞 M)) Q
  rw [hI, Subgroup.card_bot] at h1
  rw [← h2, ← h1] at h3
  exact Nat.eq_one_of_mul_eq_one_right h3.symm

/-- **A field fixed by the Frobenius elements of almost all primes is the base field.** -/
theorem finrank_eq_one_of_forall_frobeniusElement_fixes {B : ℕ}
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), B < Ideal.absNorm v.asIdeal →
      IsUnramifiedPrime K L G v ∧
        ∀ x : M, frobeniusElement K L G v • algebraMap M L x = algebraMap M L x) :
    Module.finrank K M = 1 := by
  refine finrank_eq_one_of_forall_split (B := B) fun P hPp hP0 hB => ?_
  haveI : P.IsMaximal := hPp.isMaximal hP0
  -- a prime `Q` of `L` above `P` and the prime `v` of `K` below
  obtain ⟨Q, hQmax, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP0 Q
  have hQM : Q.under (𝓞 M) = P := (Q.over_def P).symm
  have hQK : Q.under (𝓞 K) = P.under (𝓞 K) := by rw [← hQM, Ideal.under_under]
  let v : HeightOneSpectrum (𝓞 K) :=
    (⟨Q, hQmax.isPrime, hQ0⟩ : HeightOneSpectrum (𝓞 L)).under (𝓞 K)
  have hv : v.asIdeal = Q.under (𝓞 K) := rfl
  haveI : Q.LiesOver v.asIdeal := ⟨hv⟩
  obtain ⟨hunr, hfix⟩ := hM v (by rw [hv, hQK]; exact hB)
  have hfrob : arithFrobAt (𝓞 K) G Q = frobeniusElement K L G v :=
    arithFrobAt_eq_frobeniusElement hunr Q
  rw [← hQK, ← hQM]
  exact ⟨ramificationIdx_under_eq_one_of_inertia_eq_bot M Q (hunr Q hQmax inferInstance),
    absNorm_under_eq_of_isArithFrobAt_fixes M Q hQ0 (IsArithFrobAt.arithFrobAt (𝓞 K) G Q)
      (by rw [hfrob]; exact hfix)⟩

end Intermediate

/-! ### Surjectivity -/

/-- **The Frobenius elements generate the group of an abelian extension**: a subgroup that
contains the Frobenius elements of all primes of norm `> B`, all unramified, is the whole
group. -/
theorem eq_top_of_forall_frobeniusElement_mem (H : Subgroup G) {B : ℕ}
    (hH : ∀ v : HeightOneSpectrum (𝓞 K), B < Ideal.absNorm v.asIdeal →
      IsUnramifiedPrime K L G v ∧ frobeniusElement K L G v ∈ H) : H = ⊤ := by
  -- the fixed field of `H` is `K`
  have h1 : Module.finrank K (FixedPoints.intermediateField H : IntermediateField K L) = 1 :=
    finrank_eq_one_of_forall_frobeniusElement_fixes (G := G)
      (FixedPoints.intermediateField H : IntermediateField K L) (B := B) fun v hv =>
        ⟨(hH v hv).1, fun x => x.2 ⟨_, (hH v hv).2⟩⟩
  have h2 := IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup G K L H
  have h3 := Module.finrank_mul_finrank K
    (FixedPoints.intermediateField H : IntermediateField K L) L
  rw [h1, one_mul, h2, ← IsGaloisGroup.card_eq_finrank G K L] at h3
  exact (Subgroup.card_eq_iff_eq_top H).mp h3

/-- A prime that does not divide the modulus is prime to it. -/
theorem idealUnit_prime_mem_idealGroup (𝔪 : Modulus K) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.fin) : idealUnit v.ne_bot ∈ idealGroup 𝔪 := by
  intro w hw
  rw [coe_idealUnit]
  refine count_maximal_coprime K w fun h => hv ?_
  rw [h]
  exact hw

variable (K L G) (𝔪 : Modulus K)

/-- The range of the Artin map on the ideals prime to `𝔪` is the whole group. -/
theorem range_artinMap_comp_subtype
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v) :
    ((artinMap K L G).comp (idealGroup 𝔪).subtype).range = ⊤ := by
  refine eq_top_of_forall_frobeniusElement_mem (K := K) (L := L) _
    (B := Ideal.absNorm 𝔪.fin) fun v hv => ?_
  -- a prime of norm `> N(𝔪)` does not divide `𝔪`
  have hndvd : ¬ v.asIdeal ∣ 𝔪.fin := fun hdvd => by
    have hpos : 0 < Ideal.absNorm 𝔪.fin :=
      Nat.pos_of_ne_zero fun h => 𝔪.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact absurd (Nat.le_of_dvd hpos
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))) (not_le.mpr hv)
  refine ⟨hram v hndvd, ⟨⟨_, idealUnit_prime_mem_idealGroup 𝔪 hndvd⟩, ?_⟩⟩
  show artinMap K L G (idealUnit v.ne_bot) = _
  rw [artinMap_idealUnit_prime, frobeniusOrOne, if_pos (hram v hndvd)]

/-- **The Artin map is onto**: every element of `G` is the Artin symbol of an ideal prime to
`𝔪`. -/
theorem exists_mem_idealGroup_artinMap_eq
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v)
    (g : G) : ∃ I ∈ idealGroup 𝔪, artinMap K L G I = g := by
  obtain ⟨I, rfl⟩ := MonoidHom.mem_range.mp
    ((range_artinMap_comp_subtype K L G 𝔪 hram).symm ▸ Subgroup.mem_top g)
  exact ⟨I, I.2, rfl⟩

/-- **The kernel of the Artin map on the ideals prime to `𝔪` has index `[L : K]`.** -/
theorem index_ker_artinMap
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.fin → IsUnramifiedPrime K L G v) :
    ((artinMap K L G).comp (idealGroup 𝔪).subtype).ker.index = Module.finrank K L := by
  rw [Subgroup.index_ker, range_artinMap_comp_subtype K L G 𝔪 hram, Subgroup.card_top,
    IsGaloisGroup.card_eq_finrank G K L]

end GaloisForLFunctions
