/-
The auxiliary-factor reciprocity argument is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicPhaseLivesModuloTwo
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Cubic reciprocity at a common residue characteristic

The ramification-inertia degree identity bounds the number of primes above a
rational prime by two. For two distinct such primes with primary generators
`p,q`, every prime factor of `−(p+q)` has a different residue characteristic.
Primary factorization and the already proved Frobenius reciprocity therefore
supply reciprocity in the remaining case.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- A unit congruent to one modulo the square of the ramified prime is one. -/
theorem primary_unit_eq_one (u : Oˣ) (hu : lambda ^ 2 ∣ (u : O) - 1) :
    (u : O) = 1 := by
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_one] using hu
  rcases hunit with h | h
  · simp only [h, Units.val_one]
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      have heq : (-1 : O) - 1 = -2 := by ring
      have hn : lambda ^ 2 ∣ (-2 : O) := by
        simpa only [h, Units.val_neg, Units.val_one, heq] using hu
      simpa only [neg_neg] using dvd_neg.mpr hn
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))

/-- A primary element cannot vanish. -/
theorem primary_ne_zero (a : O) (ha : lambda ^ 2 ∣ a - 1) : a ≠ 0 := by
  intro hz
  have hneg : lambda ^ 2 ∣ (-1 : O) := by
    simpa only [hz, zero_sub] using ha
  have hone : lambda ∣ (1 : O) :=
    (dvd_pow_self lambda (by decide)).trans (dvd_neg.mp hneg)
  exact lambda_not_dvd_two (hone.trans (one_dvd 2))

/-- Primary congruence removes the unit ambiguity in an associated factorization. -/
theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone := primary_unit_eq_one u huprimary
  simpa only [huone, mul_one] using hu

/-- Products preserve the primary congruence. -/
theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

/-- Every nonzero primary element is exactly a product of primary primes. -/
theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      let r := primaryGenerator (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have hr := primaryGenerator_spec (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hr.1
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hr.2⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht

private theorem residue_char_mem (P : Ideal O) :
    (ringChar (O ⧸ P) : O) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast]
  exact CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))


section PrimeCover

local instance : Algebra ℤ K := Ring.toIntAlgebra K
private instance intTowerO :
    @IsScalarTower ℤ O K (Algebra.toSMul : SMul ℤ O)
      (Algebra.toSMul : SMul O K) (Algebra.toSMul : SMul ℤ K) :=
  IsScalarTower.of_algebraMap_eq' (by ext n; simp)
private instance intTowerQ :
    @IsScalarTower ℤ ℚ K (Algebra.toSMul : SMul ℤ ℚ)
      (Algebra.toSMul : SMul ℚ K) (Algebra.toSMul : SMul ℤ K) :=
  IsScalarTower.of_algebraMap_eq' (by ext n; simp)

private theorem field_finrank : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) K
    (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

/-- A quadratic number field has at most two primes above a rational prime. -/
theorem maximal_eq_or_eq_of_same_residue_char
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (hRP : ringChar (O ⧸ R) = ringChar (O ⧸ P)) : R = P ∨ R = Q := by
  let ℓ := ringChar (O ⧸ P)
  have hℓ : Nat.Prime ℓ := CharP.prime_ringChar (O ⧸ P)
  have hℓZ : Prime (ℓ : ℤ) := by
    rwa [Int.prime_iff_natAbs_prime, Int.natAbs_natCast]
  let p : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  letI : p.IsMaximal := hℓZ.isMaximal_span_singleton
  have hp0 : p ≠ ⊥ := by
    intro hz
    exact hℓZ.ne_zero (Ideal.span_singleton_eq_bot.mp hz)
  let S := IsDedekindDomain.primesOverFinset p O
  have hcard : S.card ≤ 2 := by
    simpa only [field_finrank] using
      (Ideal.card_primesOverFinset_le_finrank O ℚ K hp0)
  have hmem (T : Ideal O) [T.IsMaximal] (hT : ringChar (O ⧸ T) = ℓ) : T ∈ S := by
    apply (IsDedekindDomain.mem_primesOverFinset_iff hp0 O).mpr
    refine ⟨inferInstance, ?_⟩
    apply (Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top (inferInstance : T.IsMaximal)) hℓZ).mpr
    simpa only [map_natCast, ← hT] using residue_char_mem T
  by_contra h
  push Not at h
  have hsub : ({P, Q, R} : Finset (Ideal O)) ⊆ S := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hmem T rfl
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hmem T hPQ
    have hTR := Finset.mem_singleton.mp hT
    subst T
    exact hmem R hRP
  have hthree := Finset.card_le_card hsub
  have hsize : ({P, Q, R} : Finset (Ideal O)).card = 3 := by
    simp [hne, h.1.symm, h.2.symm]
  rw [hsize] at hthree
  omega

end PrimeCover

/-- A primary auxiliary divisor avoids the common residue characteristic. -/
theorem prime_divisor_residue_char_ne
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (t : O) (htP : t ∉ P) (htQ : t ∉ Q) (htR : t ∈ R) :
    ringChar (O ⧸ R) ≠ ringChar (O ⧸ P) := by
  intro hRP
  rcases maximal_eq_or_eq_of_same_residue_char P Q R hne hPQ hRP with rfl | rfl
  · exact htP htR
  · exact htQ htR

/-- The square of the ramified prime divides three. -/
theorem lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : O) := by
  have h := dvd_neg.mpr neg_two_primary
  convert h using 1; ring

/-- The negative sum of two primary elements is primary. -/
theorem neg_add_primary (p q : O)
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1) :
    lambda ^ 2 ∣ -(p + q) - 1 := by
  have hd := dvd_neg.mpr (dvd_add (dvd_add hp hq) lambda_sq_dvd_three)
  convert hd using 1; ring

private theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

/-- Cubic residue characters are unchanged by negating their argument. -/
theorem cubicChar_neg_one (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    cubicChar P hg (-1) = 1 := by
  let χ := cubicChar P hg
  have hcube : χ (-1) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hg]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1) = χ ((-1) ^ 3) := by rw [hminus]
    _ = χ (-1) ^ 3 := by rw [map_pow]
    _ = 1 := hcube

/-- Factoring the negative sum reduces common-characteristic reciprocity to different characteristics. -/
theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, cubicChar_neg_one, one_mul] at htval
  exact htval

/-- Cubic reciprocity for all primary Eisenstein primes away from three. -/
theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

/-- Canonical primary generators satisfy cubic reciprocity, including primes over the same rational prime. -/
theorem primaryGenerator_reciprocity_all (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q) :
    cubicChar P hP (Ideal.Quotient.mk P (primaryGenerator Q hQ)) =
      cubicChar Q hQ (Ideal.Quotient.mk Q (primaryGenerator P hP)) :=
  cubic_reciprocity_primary P Q hP hQ _ _
    (primaryGenerator_spec P hP).1 (primaryGenerator_spec Q hQ).1
    (primaryGenerator_spec P hP).2 (primaryGenerator_spec Q hQ).2

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.exists_primary_prime_factorization
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.maximal_eq_or_eq_of_same_residue_char
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.cubic_reciprocity_primary
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.primaryGenerator_reciprocity_all
