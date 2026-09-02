import GaloisForLFunctions.RHTower.Sieve.PrimePowerSupport
import GaloisForLFunctions.RHTower.Sieve.VinogradovDiagonalMoment

/-!
# Factorial energy for powers of prime-supported Dirichlet polynomials

Unique factorization improves the crude `ell ^ ell` bound for an ordered prime-product fibre to
the sharp uniform bound `ell!`: every fibre consists of permutations of one prime multiset.  This
gives the corresponding factorial improvement in the convolution energy estimate.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A natural number bundled with a proof that it is prime. -/
abbrev CertifiedPrime := {p : ℕ // Nat.Prime p}

/-- Product of a multiset of certified primes. -/
def primeMultisetProduct (s : Multiset CertifiedPrime) : ℕ :=
  (s.map fun p : CertifiedPrime => (p : ℕ)).prod

/-- Prime factorization reads the multiplicity of each certified prime in a multiset product. -/
theorem factorization_primeMultisetProduct
    (s : Multiset CertifiedPrime) (p : CertifiedPrime) :
    (primeMultisetProduct s).factorization (p : ℕ) = s.count p := by
  induction s using Multiset.induction_on with
  | empty => simp [primeMultisetProduct]
  | @cons q s ih =>
      have hspos : 0 < primeMultisetProduct s := by
        rw [primeMultisetProduct]
        apply Multiset.prod_pos
        intro n hn
        obtain ⟨r, _hr, rfl⟩ := Multiset.mem_map.mp hn
        exact r.2.pos
      rw [primeMultisetProduct, Multiset.map_cons, Multiset.prod_cons]
      change ((q : ℕ) * primeMultisetProduct s).factorization (p : ℕ) = _
      rw [Nat.factorization_mul q.2.ne_zero (ne_of_gt hspos)]
      simp only [Finsupp.add_apply, ih, Multiset.count_cons]
      by_cases hpq : p = q
      · subst q
        rw [p.2.factorization_self, if_pos rfl]
        omega
      · have hfactor : (q : ℕ).factorization (p : ℕ) = 0 := by
          by_contra hne
          have heq : (q : ℕ) = (p : ℕ) := q.2.eq_of_factorization_pos hne
          exact hpq (Subtype.ext heq.symm)
        rw [hfactor, if_neg hpq]
        omega

/-- A multiset of certified primes is determined by its product. -/
theorem primeMultisetProduct_injective : Function.Injective primeMultisetProduct := by
  intro s t hprod
  apply Multiset.ext.mpr
  intro p
  rw [← factorization_primeMultisetProduct s p,
    ← factorization_primeMultisetProduct t p, hprod]

/-- A supported index, regarded as its certified shifted prime. -/
def primeSupportValue (N : ℕ) (q : ↑(primeSupport N)) : CertifiedPrime :=
  ⟨(q.1 : ℕ) + 1, by
    have hq := q.property
    change q.1 ∈ (Finset.univ : Finset (Fin N)).filter
      (fun n : Fin N => Nat.Prime ((n : ℕ) + 1)) at hq
    exact (Finset.mem_filter.mp hq).2⟩

theorem primeSupportValue_injective (N : ℕ) :
    Function.Injective (primeSupportValue N) := by
  intro p q hpq
  apply Subtype.ext
  apply Fin.ext
  exact Nat.add_right_cancel (congrArg Subtype.val hpq)

private theorem powFibreOn_primeSupport_card_le_factorial
    (N ell : ℕ) (j : Fin (N ^ ell)) :
    (powFibreOn N ell (primeSupport N) j).card ≤ ell.factorial := by
  classical
  let F := powFibreOn N ell (primeSupport N) j
  change F.card ≤ ell.factorial
  rcases Finset.eq_empty_or_nonempty F with hF | hF
  · change F = ∅ at hF
    rw [hF]
    exact Nat.zero_le _
  · obtain ⟨q₀, hq₀⟩ := hF
    let liftTuple : ↑F → Fin ell → ↑(primeSupport N) := fun p i =>
      ⟨p.1 i, by
        have hp := p.property
        change p.1 ∈ powFibreOn N ell (primeSupport N) j at hp
        rw [powFibreOn, Finset.mem_filter] at hp
        exact hp.2 i⟩
    have hproduct : ∀ p : ↑F,
        primeMultisetProduct
            (Multiset.map (primeSupportValue N) (List.ofFn (liftTuple p))) =
          (j : ℕ) + 1 := by
      intro p
      have hp := p.property
      change p.1 ∈ powFibreOn N ell (primeSupport N) j at hp
      rw [powFibreOn, Finset.mem_filter] at hp
      have hpidx := hp.1
      rw [Finset.mem_filter] at hpidx
      rw [primeMultisetProduct]
      simp only [Multiset.map_map, Function.comp_apply, primeSupportValue]
      have hpow := powIdx_val_add_one p.1
      rw [hpidx.2] at hpow
      simpa [liftTuple, List.prod_ofFn] using hpow.symm
    have hperm : ∀ p : ↑F,
        List.ofFn (liftTuple p) ∈ (List.ofFn (liftTuple ⟨q₀, hq₀⟩)).permutations := by
      intro p
      rw [List.mem_permutations]
      apply Multiset.coe_eq_coe.mp
      apply Multiset.map_injective (primeSupportValue_injective N)
      apply primeMultisetProduct_injective
      rw [hproduct p, hproduct ⟨q₀, hq₀⟩]
    let embed : ↑F ↪
        {l : List ↑(primeSupport N) //
          l ∈ (List.ofFn (liftTuple ⟨q₀, hq₀⟩)).permutations} :=
      { toFun := fun p => ⟨List.ofFn (liftTuple p), hperm p⟩
        inj' := by
          intro p q hpq
          apply Subtype.ext
          apply funext
          intro i
          have hlist := congrArg (fun z => z.1) hpq
          have htuple := List.ofFn_injective hlist
          exact congrArg (fun z => z.1) (congrFun htuple i) }
    have hcard := Fintype.card_le_of_embedding embed
    rw [Fintype.card_coe] at hcard
    exact hcard.trans
      (card_permutation_list_subtype_le_factorial
        (liftTuple ⟨q₀, hq₀⟩))

/-- Sharp factorial fibre bound for an `ell`-fold product of primes. -/
theorem powFibreOn_primeSupport_card_le_factorial_real
    (N ell : ℕ) (j : Fin (N ^ ell)) :
    ((powFibreOn N ell (primeSupport N) j).card : ℝ) ≤ (ell.factorial : ℝ) := by
  exact_mod_cast powFibreOn_primeSupport_card_le_factorial N ell j

/-- Every coefficient of a power of a unit-bounded prime-supported vector is bounded by `ell!`. -/
theorem norm_convPow_le_factorial_of_prime_support
    (N ell : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    (ha : ∀ n : Fin N, ‖a n‖ ≤ 1)
    (j : Fin (N ^ ell)) :
    ‖convPow N ell a j‖ ≤ (ell.factorial : ℝ) := by
  classical
  have hconv :
      convPow N ell a j =
        ∑ p ∈ powFibreOn N ell (primeSupport N) j,
          ∏ i : Fin ell, a (p i) := by
    rw [convPow, powFibreOn]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro p _ hp i
    rw [primeSupport, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsupp _
      ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))⟩
  rw [hconv]
  calc
    ‖∑ p ∈ powFibreOn N ell (primeSupport N) j,
        ∏ i : Fin ell, a (p i)‖ ≤
        ∑ p ∈ powFibreOn N ell (primeSupport N) j,
          ‖∏ i : Fin ell, a (p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ powFibreOn N ell (primeSupport N) j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ha (p i))
    _ = ((powFibreOn N ell (primeSupport N) j).card : ℝ) := by simp
    _ ≤ (ell.factorial : ℝ) :=
      powFibreOn_primeSupport_card_le_factorial_real N ell j

/-- The convolution energy of a prime-supported power loses only `ell!`, not `ell^ell`. -/
theorem primePowerSupportSum_normSq_convPow_le_factorial
    (N ell : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1)) :
    ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
      (ell.factorial : ℝ) * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ell :=
  sum_normSq_convPow_le_of_support N ell a (primeSupport N)
    (fun n hn => by
      rw [primeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hsupp n hn⟩)
    (powFibreOn_primeSupport_card_le_factorial_real N ell) (by positivity)

end

end RHTower.Sieve
