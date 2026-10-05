import Mathlib

/-!
# Unmixedness from an integral extension of a factorial ring

Let `A` be a Noetherian domain integral over a Noetherian factorial domain `B ⊆ A`, and suppose
that relatively prime `c, c' ∈ B` stay a regular sequence on `A`:
`c' x ∈ cA ⟹ x ∈ cA`.  Then every associated prime of `A/aA` (`a ≠ 0`) has height one.

* `height_le_height_comap_of_isIntegral` — **incomparability bounds heights**: contraction is
  strictly monotone on primes, so `ht Q ≤ ht (Q ∩ B)`.
* `height_eq_one_of_mem_associatedPrimes` — for `Q = ann(v̄)`, the contraction `I_B = Q ∩ B` lies in
  a principal prime `(p)`: otherwise prime avoidance gives `c, c' ∈ I_B` relatively prime, and then
  `c v = a w`, `c' v = a w'` force `c' w ∈ cA`, `w ∈ cA`, `v ∈ aA`, so `Q = A`.  Krull's principal
  ideal theorem bounds `ht (p) ≤ 1`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- **Incomparability bounds heights.** -/
theorem height_le_height_comap_of_isIntegral [Algebra.IsIntegral B A] (Q : Ideal A) [Q.IsPrime] :
    Q.height ≤ (Q.comap (algebraMap B A)).height := by
  have hf : StrictMono (PrimeSpectrum.comap (algebraMap B A)) := by
    intro x y hxy
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal, PrimeSpectrum.comap_asIdeal,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.IsIntegral.comap_lt_comap (R := B) ((PrimeSpectrum.asIdeal_lt_asIdeal x y).mpr hxy)
  have := Order.height_le_height_apply_of_strictMono _ hf (⟨Q, inferInstance⟩ : PrimeSpectrum A)
  rwa [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight,
    PrimeSpectrum.comap_asIdeal] at this

section Factorial

variable {B : Type*} [CommRing B] [UniqueFactorizationMonoid B]

/-- In a factorial domain, an ideal lying in no principal prime ideal `(p)` with `p ∣ c`, `c ≠ 0`,
contains an element relatively prime to `c`. -/
theorem exists_isRelPrime_of_not_le {I : Ideal B} {c : B} (hc0 : c ≠ 0)
    (hI : ∀ p ∈ UniqueFactorizationMonoid.factors c, ¬ I ≤ Ideal.span {p}) :
    ∃ c' ∈ I, IsRelPrime c c' := by
  classical
  set s := (UniqueFactorizationMonoid.factors c).toFinset
  have hprime : ∀ p ∈ s, (Ideal.span {p}).IsPrime := by
    intro p hp
    have hpp := UniqueFactorizationMonoid.prime_of_factor p (Multiset.mem_toFinset.mp hp)
    exact (Ideal.span_singleton_prime hpp.ne_zero).mpr hpp
  have hnot : ¬ ((I : Set B) ⊆ ⋃ p ∈ (s : Set B), (Ideal.span {p} : Set B)) := by
    intro hsub
    have hcases := (Ideal.subset_union_prime (s := s) (f := fun p => Ideal.span {p}) c c
      (fun p hp _ _ => hprime p hp)).mp hsub
    obtain ⟨p, hp, hle⟩ := hcases
    exact hI p (Multiset.mem_toFinset.mp hp) hle
  rw [Set.not_subset] at hnot
  obtain ⟨c', hc'I, hc'⟩ := hnot
  refine ⟨c', hc'I, fun d hdc hdc' => ?_⟩
  by_contra hd
  have hd0 : d ≠ 0 := fun h => hc0 (zero_dvd_iff.mp (h ▸ hdc))
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hd hd0
  obtain ⟨p, hp, hpq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hc0 hq
    (hqd.trans hdc)
  apply hc'
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  refine ⟨p, Multiset.mem_toFinset.mpr hp, Ideal.mem_span_singleton.mpr ?_⟩
  exact hpq.symm.dvd.trans (hqd.trans hdc')

end Factorial

variable [IsDomain A] [IsNoetherianRing A] [IsDomain B] [IsNoetherianRing B]
  [UniqueFactorizationMonoid B]

/-- **Associated primes of principal ideals have height one.** -/
theorem height_eq_one_of_mem_associatedPrimes [Algebra.IsIntegral B A]
    (hinj : Function.Injective (algebraMap B A))
    (hcop : ∀ c c' : B, IsRelPrime c c' → ∀ x : A,
      algebraMap B A c' * x ∈ Ideal.span {algebraMap B A c} → x ∈ Ideal.span {algebraMap B A c})
    {a : A} (ha : a ≠ 0) {Q : Ideal A} (hQ : Q ∈ associatedPrimes A (A ⧸ Ideal.span {a})) :
    Q.height = 1 := by
  classical
  obtain ⟨hQp, v', hv⟩ := (Submodule.isAssociatedPrime_iff).mp hQ
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v'
  have hmem : ∀ x : A, x ∈ Q ↔ x * v ∈ Ideal.span {a} := by
    intro x
    rw [hv, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- lower bound
  have haQ : a ∈ Q := (hmem a).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a))
  have hQ0 : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr fun h => ha (by rw [h] at haQ; exact haQ)
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have hlow := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
  rw [Ideal.height_bot, zero_add] at hlow
  -- upper bound through the contraction
  have hcomap := height_le_height_comap_of_isIntegral (B := B) Q
  set q := Q.comap (algebraMap B A) with hq
  have hqmem : ∀ c : B, c ∈ q ↔ algebraMap B A c * v ∈ Ideal.span {a} := fun c => hmem _
  have hup : q.height ≤ 1 := by
    by_cases hq0 : q = ⊥
    · rw [hq0, Ideal.height_bot]; exact zero_le_one
    obtain ⟨c, hcq, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    by_cases hp : ∃ p ∈ UniqueFactorizationMonoid.factors c, q ≤ Ideal.span {p}
    · obtain ⟨p, hpf, hle⟩ := hp
      have hpp := UniqueFactorizationMonoid.prime_of_factor p hpf
      exact (Ideal.height_mono hle).trans (Ideal.height_span_singleton_le_one hpp.not_unit)
    push Not at hp
    exfalso
    obtain ⟨c', hc'q, hcc'⟩ := exists_isRelPrime_of_not_le hc0 hp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp ((hqmem c).mp hcq)
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp ((hqmem c').mp hc'q)
    have hw'' : algebraMap B A c' * w = algebraMap B A c * w' := by
      apply mul_left_cancel₀ ha
      calc a * (algebraMap B A c' * w) = algebraMap B A c' * (w * a) := by ring
        _ = algebraMap B A c' * (algebraMap B A c * v) := by rw [hw]
        _ = algebraMap B A c * (algebraMap B A c' * v) := by ring
        _ = algebraMap B A c * (w' * a) := by rw [hw']
        _ = a * (algebraMap B A c * w') := by ring
    have hwmem := hcop c c' hcc' w (by
      rw [hw'']; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hwmem
    have hc0' : algebraMap B A c ≠ 0 := fun h => hc0 (hinj (h.trans (map_zero _).symm))
    have hv : v = u * a := by
      apply mul_left_cancel₀ hc0'
      rw [← hw, ← hu]; ring
    have h1 : (1 : A) ∈ Q := (hmem 1).mpr (by
      rw [one_mul, hv]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self a))
    exact hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  exact le_antisymm (hcomap.trans hup) hlow

end GaloisForLFunctions.HTGeometry
