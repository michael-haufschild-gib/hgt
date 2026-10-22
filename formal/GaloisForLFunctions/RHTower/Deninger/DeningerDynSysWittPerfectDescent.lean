import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCorrespondenceFactors
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectClosureFixed
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittLocalization

/-!
# The descent criterion for rational Witt vectors along a purely inseparable extension

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3.

Let `F` be a field of exponential characteristic `q`, let `L / F` be purely inseparable inside an
algebraically closed `E`.  Every normalized irreducible `β` over `L` is the image of a unique
normalized irreducible `α` over `F` up to a power, `α = β ^ d`, and the exponent `d` — recorded
here as `deningerDescentDegree F β` — is the degree of inseparability attached to `β`.

A rational Witt vector over `L` lies in the image of `W_rat (F)` exactly when it can be written as
a quotient of normalized polynomials each of whose irreducible factors occurs with multiplicity
divisible by that exponent.  This is Deninger's description of `ℤ̲κ / κ₀` as the integral
combinations `∑ n_r (r)` with `d_r ∣ n_r`.

Combined with the fixed-point identification `W_rat (E) ^ {Aut_{F} E} = W_rat (F^perf)` this gives
both rows of Proposition 1.3.
-/

namespace RHTower

noncomputable section

open Polynomial

variable {F : Type*} [Field F]

/-! ## The exponent of the correspondence -/

open Classical in
/-- **Deninger, §1.**  The exponent `d_β` of a normalized irreducible polynomial `β` over a purely
inseparable extension `L / F`: the unique `d` with `α = β ^ d` for the normalized irreducible `α`
over `F` lying under `β`. -/
noncomputable def deningerDescentDegree (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L]
    (β : Polynomial L) : ℕ :=
  if h : ∃ (d : ℕ) (α : Polynomial F), 0 < d ∧ α.coeff 0 = 1 ∧ Irreducible α ∧
      α.map (algebraMap F L) = β ^ d then h.choose else 1

theorem deningerDescentDegree_pos {L : Type*} [Field L] [Algebra F L] (β : Polynomial L) :
    0 < deningerDescentDegree F β := by
  rw [deningerDescentDegree]
  split
  · rename_i h
    exact h.choose_spec.choose_spec.1
  · exact Nat.one_pos

/-- A normalized irreducible polynomial has positive degree. -/
theorem deningerNatDegree_pos_of_normalized {β : Polynomial F} (hβ0 : β.coeff 0 = 1)
    (hβirr : Irreducible β) : 0 < β.natDegree := by
  rcases Nat.eq_zero_or_pos β.natDegree with h | h
  · exfalso
    have hβ : β = 1 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero h
      rwa [hβ0, map_one] at hC
    exact hβirr.not_isUnit (hβ ▸ isUnit_one)
  · exact h

/-- The defining property of `deningerDescentDegree`. -/
theorem deningerDescentDegree_spec {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    ∃ α : Polynomial F, α.coeff 0 = 1 ∧ Irreducible α ∧
      α.map (algebraMap F L) = β ^ deningerDescentDegree F β := by
  have h : ∃ (d : ℕ) (α : Polynomial F), 0 < d ∧ α.coeff 0 = 1 ∧ Irreducible α ∧
      α.map (algebraMap F L) = β ^ d :=
    deningerNormalizedIrreducible_exists_preimage (F := F) (L := L) (E := E) q hβ0 hβirr
  rw [deningerDescentDegree, dif_pos h]
  obtain ⟨α, _, hα0, hαirr, hmap⟩ := h.choose_spec
  exact ⟨α, hα0, hαirr, hmap⟩

/-- Any exponent realizing the correspondence at `β` is `deningerDescentDegree F β`. -/
theorem deningerDescentDegree_eq {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {α : Polynomial F} {β : Polynomial L} {d : ℕ}
    (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α)
    (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β)
    (hmap : α.map (algebraMap F L) = β ^ d) :
    d = deningerDescentDegree F β := by
  obtain ⟨α', hα'0, hα'irr, hmap'⟩ :=
    deningerDescentDegree_spec (F := F) (L := L) (E := E) q hβ0 hβirr
  have hαeq : α = α' :=
    deningerNormalizedIrreducible_map_injective hα0 hαirr hα'0 hα'irr hmap hmap'
  subst hαeq
  have hpow : β ^ d = β ^ deningerDescentDegree F β := by rw [← hmap, hmap']
  have hdeg := congrArg Polynomial.natDegree hpow
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow] at hdeg
  exact Nat.eq_of_mul_eq_mul_right (deningerNatDegree_pos_of_normalized hβ0 hβirr) hdeg

/-! ## Multiplicities in the image -/

theorem deningerProd_coeff_zero {S : Multiset (Polynomial F)}
    (hS : ∀ r ∈ S, r.coeff 0 = 1) : S.prod.coeff 0 = 1 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
      rw [Multiset.prod_cons]
      exact deningerMul_coeff_zero (hS a (Multiset.mem_cons_self a S))
        (ih fun r hr => hS r (Multiset.mem_cons_of_mem hr))

theorem deningerMap_coeff_zero {L : Type*} [Field L] [Algebra F L] {p : Polynomial F}
    (hp : p.coeff 0 = 1) : (p.map (algebraMap F L)).coeff 0 = 1 := by
  rw [Polynomial.coeff_map, hp, map_one]

/-- The image of a normalized irreducible is a power of a single normalized irreducible, so its
multiplicities are `0` or the descent degree. -/
theorem deningerNormalizedFactors_map_count_irreducible {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial L)]
    {α : Polynomial F} (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α)
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    deningerDescentDegree F β ∣
      (deningerNormalizedFactors (α.map (algebraMap F L))).count β := by
  obtain ⟨d, β', hd, hβ'0, hβ'irr, hpow⟩ :=
    deningerNormalizedIrreducible_map_eq_pow (F := F) (L := L) (E := E) q hα0 hαirr
  have hfac : deningerNormalizedFactors (α.map (algebraMap F L)) = Multiset.replicate d β' := by
    rw [hpow, deningerNormalizedFactors_pow hβ'0,
      deningerNormalizedFactors_irreducible hβ'0 hβ'irr, Multiset.nsmul_singleton]
  rw [hfac, Multiset.count_replicate]
  split
  · rename_i hββ
    subst hββ
    exact (deningerDescentDegree_eq (F := F) (L := L) (E := E) q hα0 hαirr hβ0 hβirr hpow) ▸
      dvd_refl _
  · exact dvd_zero _

theorem deningerNormalizedFactors_map_count_dvd_aux {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial L)]
    (S : Multiset (Polynomial F)) (hS : ∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r)
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    deningerDescentDegree F β ∣
      (deningerNormalizedFactors (S.prod.map (algebraMap F L))).count β := by
  induction S using Multiset.induction_on with
  | empty =>
      rw [Multiset.prod_zero, Polynomial.map_one, deningerNormalizedFactors_one,
        Multiset.count_zero]
      exact dvd_zero _
  | cons a S ih =>
      have ha := hS a (Multiset.mem_cons_self a S)
      have hSmem : ∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r :=
        fun r hr => hS r (Multiset.mem_cons_of_mem hr)
      have hprod : S.prod.coeff 0 = 1 := deningerProd_coeff_zero fun r hr => (hSmem r hr).1
      rw [Multiset.prod_cons, Polynomial.map_mul,
        deningerNormalizedFactors_mul (deningerMap_coeff_zero ha.1)
          (deningerMap_coeff_zero hprod),
        Multiset.count_add]
      exact dvd_add
        (deningerNormalizedFactors_map_count_irreducible (E := E) q ha.1 ha.2 hβ0 hβirr)
        (ih hSmem)

/-- **Deninger, Proposition 1.3 (`t26n`).**  In the image of a normalized polynomial every
irreducible factor occurs with multiplicity divisible by its descent degree. -/
theorem deningerNormalizedFactors_map_count_dvd {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial L)]
    (P₀ : Polynomial F) (hP₀ : P₀.coeff 0 = 1)
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    deningerDescentDegree F β ∣
      (deningerNormalizedFactors (P₀.map (algebraMap F L))).count β := by
  have hspec := deningerNormalizedFactors_spec hP₀
  have h := deningerNormalizedFactors_map_count_dvd_aux (E := E) q
    (deningerNormalizedFactors P₀) hspec.1 hβ0 hβirr
  rwa [hspec.2] at h

/-- **Deninger, Proposition 1.3 (`t26n`), converse.**  A normalized polynomial all of whose
multiplicities are divisible by the descent degree descends. -/
theorem deningerNormalized_descends_of_dvd {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial L)]
    (P : Polynomial L) (hP : P.coeff 0 = 1)
    (h : ∀ β ∈ deningerNormalizedFactors P,
      deningerDescentDegree F β ∣ (deningerNormalizedFactors P).count β) :
    ∃ P₀ : Polynomial F, P₀.coeff 0 = 1 ∧ P₀.map (algebraMap F L) = P := by
  refine deningerNormalized_descends P hP ?_
  intro β hβ
  obtain ⟨hβ0, hβirr⟩ := deningerNormalizedFactors_mem hP hβ
  obtain ⟨α, hα0, _, hpow⟩ := deningerDescentDegree_spec (F := F) (L := L) (E := E) q hβ0 hβirr
  exact deningerPow_mem_range_of_dvd hα0 hpow (h β hβ)

/-! ## The criterion for rational Witt vectors -/

/-- The multiplicity condition of Deninger's subring `ℤ̲κ / κ₀`. -/
def DeningerDescentAdmissible (F : Type*) [Field F] {L : Type*} [Field L] [Algebra F L]
    [DecidableEq (Polynomial L)] (P : Polynomial L) : Prop :=
  ∀ β ∈ deningerNormalizedFactors P,
    deningerDescentDegree F β ∣ (deningerNormalizedFactors P).count β

/-- **Deninger, Proposition 1.3 (`t26n`), lower row.**  A rational Witt vector over a purely
inseparable extension `L / F` comes from `W_rat (F)` exactly when it is the quotient of two
normalized polynomials whose irreducible factors all occur with multiplicity divisible by their
degree of inseparability. -/
theorem deningerCanonicalRationalWitt_mem_range_iff {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial L)] (w : DeningerCanonicalRationalWittRing L) :
    (∃ w₀ : DeningerCanonicalRationalWittRing F,
        deningerCanonicalRationalWittMap (algebraMap F L) w₀ = w)
      ↔ ∃ (P Q : Polynomial L) (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1),
          w = deningerCanonicalRationalWittNormalizedFraction P Q hP hQ ∧
            DeningerDescentAdmissible F P ∧ DeningerDescentAdmissible F Q := by
  constructor
  · rintro ⟨w₀, rfl⟩
    obtain ⟨P₀, Q₀, hP₀, hQ₀, hw₀⟩ :=
      deningerCanonicalRationalWitt_eq_normalizedFraction w₀
    subst hw₀
    refine ⟨P₀.map (algebraMap F L), Q₀.map (algebraMap F L),
      deningerMap_coeff_zero hP₀, deningerMap_coeff_zero hQ₀,
      deningerCanonicalRationalWittMap_normalizedFraction _ _ _ hP₀ hQ₀, ?_, ?_⟩
    · intro β hβ
      obtain ⟨hβ0, hβirr⟩ := deningerNormalizedFactors_mem (deningerMap_coeff_zero hP₀) hβ
      exact deningerNormalizedFactors_map_count_dvd (E := E) q P₀ hP₀ hβ0 hβirr
    · intro β hβ
      obtain ⟨hβ0, hβirr⟩ := deningerNormalizedFactors_mem (deningerMap_coeff_zero hQ₀) hβ
      exact deningerNormalizedFactors_map_count_dvd (E := E) q Q₀ hQ₀ hβ0 hβirr
  · rintro ⟨P, Q, hP, hQ, hw, hPadm, hQadm⟩
    obtain ⟨P₀, hP₀, hPmap⟩ := deningerNormalized_descends_of_dvd (E := E) q P hP hPadm
    obtain ⟨Q₀, hQ₀, hQmap⟩ := deningerNormalized_descends_of_dvd (E := E) q Q hQ hQadm
    refine ⟨deningerCanonicalRationalWittNormalizedFraction P₀ Q₀ hP₀ hQ₀, ?_⟩
    rw [deningerCanonicalRationalWittMap_normalizedFraction, hw]
    exact deningerCanonicalRationalWittNormalizedFraction_congr _ _ _ _ hPmap hQmap

open scoped DeningerWittRing in
/-- **Deninger, Proposition 1.3 (`t26n`), both rows.**  An `Aut_{F} (E)`-invariant rational Witt
vector over an algebraic closure `E` of `F` comes from the perfect closure of `F`, and it descends
all the way to `F` exactly under the multiplicity criterion. -/
theorem deningerCanonicalRationalWitt_prop13 {E : Type*} [Field E] [Algebra F E]
    [IsAlgClosure F E] (q : ℕ) [ExpChar F q]
    [DecidableEq (Polynomial (perfectClosure F E))]
    (w : DeningerCanonicalRationalWittRing E) (hw : ∀ σ : E ≃ₐ[F] E, σ • w = w) :
    ∃ w₁ : DeningerCanonicalRationalWittRing (perfectClosure F E),
      deningerCanonicalRationalWittMap (algebraMap (perfectClosure F E) E) w₁ = w ∧
        ((∃ w₀ : DeningerCanonicalRationalWittRing F,
            deningerCanonicalRationalWittMap (algebraMap F E) w₀ = w)
          ↔ ∃ (P Q : Polynomial (perfectClosure F E))
              (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1),
              w₁ = deningerCanonicalRationalWittNormalizedFraction P Q hP hQ ∧
                DeningerDescentAdmissible F P ∧ DeningerDescentAdmissible F Q) := by
  haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  obtain ⟨w₁, hw₁⟩ := deningerWittRing_fixed_eq_perfectClosure F E w hw
  refine ⟨w₁, hw₁, ?_⟩
  rw [← deningerCanonicalRationalWitt_mem_range_iff (F := F)
    (L := perfectClosure F E) (E := E) q w₁]
  constructor
  · rintro ⟨w₀, hw₀⟩
    refine ⟨w₀, ?_⟩
    apply deningerCanonicalRationalWittMap_injective
      (algebraMap (perfectClosure F E) E) (algebraMap (perfectClosure F E) E).injective
    rw [← deningerCanonicalRationalWittMap_comp, hw₁, ← hw₀,
      IsScalarTower.algebraMap_eq F (perfectClosure F E) E]
  · rintro ⟨w₀, hw₀⟩
    refine ⟨w₀, ?_⟩
    rw [IsScalarTower.algebraMap_eq F (perfectClosure F E) E,
      deningerCanonicalRationalWittMap_comp, hw₀, hw₁]

end

end RHTower
