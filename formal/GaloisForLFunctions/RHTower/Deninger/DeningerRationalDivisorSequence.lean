import GaloisForLFunctions.RHTower.Deninger.DeningerSUnitEndpointPage
import GaloisForLFunctions.RHTower.Deninger.DeningerRestrictedPrimeSheaf

/-!
# The divisor sequence of the positive rationals

A nonzero rational has nonzero valuation at only finitely many primes, so its divisor is a finitely
supported family of integers.  Taking divisors is additive; on the positive units it has trivial
kernel, since a positive rational with trivial valuations is `1`; and every finitely supported
family is the divisor of the corresponding product of prime powers.  So the divisor map identifies
the positive rationals with the free abelian group on the primes — unique factorization in divisor
form.

Splitting the primes into those dividing `N` and the rest turns this into the divisor sequence of
`Spec ℤ[1/N]`: the units supported on the primes dividing `N` are exactly the families killed by
the valuations at the surviving primes, and those valuations are onto.

* `deningerDivisor`, `deningerDivisor_apply`, `deningerDivisor_mul` : the divisor map.
* `deningerDivisor_eq_zero_iff` : trivial kernel on positives.
* `deningerDivisor_divisorProduct`, `deningerDivisor_surjective` : every family is a divisor.
* `deningerDivisor_vanishing_off_iff` : the cofinite divisor sequence `(5)`--`(6)`.
-/

namespace RHTower

section Divisor

/-- The valuation family of a rational unit has finite support. -/
theorem deningerValuationSupport_finite (u : ℚˣ) :
    (Function.support fun p : Nat.Primes => padicValRat ((p : ℕ)) ((u : ℚ))).Finite := by
  classical
  have hu : ((u : ℚ)) ≠ 0 := u.ne_zero
  have hfin := deningerPadicValRat_support_finite hu
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun a b h => Subtype.ext h
  refine Set.Finite.subset (Set.Finite.preimage hinj.injOn hfin) ?_
  intro p hp
  exact ⟨p.2, hp⟩

/-- The divisor of a rational unit: its family of valuations. -/
noncomputable def deningerDivisor (u : ℚˣ) : Nat.Primes →₀ ℤ :=
  Finsupp.ofSupportFinite _ (deningerValuationSupport_finite u)

@[simp]
theorem deningerDivisor_apply (u : ℚˣ) (p : Nat.Primes) :
    deningerDivisor u p = padicValRat ((p : ℕ)) ((u : ℚ)) := rfl

/-- **Taking divisors is additive.** -/
theorem deningerDivisor_mul (u v : ℚˣ) :
    deningerDivisor (u * v) = deningerDivisor u + deningerDivisor v := by
  refine Finsupp.ext fun p => ?_
  haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
  show padicValRat _ (((u * v : ℚˣ) : ℚ)) = padicValRat _ ((u : ℚ)) + padicValRat _ ((v : ℚ))
  rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]

/-- **The divisor map has trivial kernel on the positive units.** -/
theorem deningerDivisor_eq_zero_iff {u : ℚˣ} (hu : 0 < ((u : ℚ))) :
    deningerDivisor u = 0 ↔ u = 1 := by
  constructor
  · intro h
    refine Units.ext ?_
    refine deningerRat_eq_one_of_valuations hu fun p => ?_
    have := congrArg (fun f : Nat.Primes →₀ ℤ => f p) h
    simpa using this
  · rintro rfl
    refine Finsupp.ext fun p => ?_
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    show padicValRat _ (((1 : ℚˣ) : ℚ)) = 0
    rw [Units.val_one, padicValRat.one]

/-- The product of prime powers with a prescribed exponent family. -/
noncomputable def deningerDivisorProduct (n : Nat.Primes →₀ ℤ) : ℚˣ :=
  ∏ p ∈ n.support, deningerPrimeUnit p ^ n p

/-- **Every finitely supported family is a divisor.** -/
theorem deningerDivisor_divisorProduct (n : Nat.Primes →₀ ℤ) :
    deningerDivisor (deningerDivisorProduct n) = n := by
  classical
  refine Finsupp.ext fun q => ?_
  haveI : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  show padicValRat ((q : ℕ)) ((deningerDivisorProduct n : ℚˣ) : ℚ) = n q
  rw [deningerDivisorProduct, deningerPadicValRat_prod]
  have hterm : ∀ p ∈ n.support,
      padicValRat ((q : ℕ)) (((deningerPrimeUnit p ^ n p : ℚˣ) : ℚ))
        = if p = q then n p else 0 := by
    intro p _
    rw [Units.val_zpow_eq_zpow_val, padicValRat.zpow, deningerPadicValRat_primeUnit]
    by_cases h : p = q
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hq : q ∈ n.support
  · rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro p _ hne
      exact if_neg hne
    · intro hcon
      exact absurd hq hcon
  · have hzero : n q = 0 := by
      by_contra hcon
      exact hq (Finsupp.mem_support_iff.mpr hcon)
    rw [hzero]
    refine Finset.sum_eq_zero fun p hp => ?_
    refine if_neg fun hpq => ?_
    rw [hpq] at hp
    exact hq hp

/-- The realizing product is positive. -/
theorem deningerDivisorProduct_pos (n : Nat.Primes →₀ ℤ) :
    0 < ((deningerDivisorProduct n : ℚˣ) : ℚ) := by
  classical
  rw [deningerDivisorProduct]
  have hgen : ∀ s : Finset Nat.Primes,
      0 < (((∏ p ∈ s, deningerPrimeUnit p ^ n p : ℚˣ) : ℚ)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      refine mul_pos ?_ ih
      rw [Units.val_zpow_eq_zpow_val, deningerPrimeUnit_val]
      refine zpow_pos ?_ _
      exact_mod_cast a.2.pos
  exact hgen n.support

/-- **The divisor map is onto the free abelian group on the primes.** -/
theorem deningerDivisor_surjective (n : Nat.Primes →₀ ℤ) :
    ∃ u : ℚˣ, 0 < ((u : ℚ)) ∧ deningerDivisor u = n :=
  ⟨deningerDivisorProduct n, deningerDivisorProduct_pos n, deningerDivisor_divisorProduct n⟩

/-- **The cofinite divisor sequence `(5)`--`(6)`.**  A positive unit is an `S`-unit exactly when
its divisor is supported in `S`, i.e. exactly when the valuations at the surviving primes kill
it. -/
theorem deningerDivisor_vanishing_off_iff {S : Finset Nat.Primes} {u : ℚˣ}
    (hu : 0 < ((u : ℚ))) :
    (∀ p ∉ S, deningerDivisor u p = 0) ↔ u ∈ deningerSUnits S := by
  constructor
  · intro h
    exact ⟨hu, fun p hp => h p hp⟩
  · rintro ⟨_, h⟩ p hp
    exact h p hp

/-- **Surjectivity at the surviving primes.**  Any family supported off `S` is the divisor of a
positive unit whose valuations on `S` vanish. -/
theorem deningerDivisor_surjective_off (S : Finset Nat.Primes) (n : Nat.Primes →₀ ℤ)
    (hn : ∀ p ∈ S, n p = 0) :
    ∃ u : ℚˣ, 0 < ((u : ℚ)) ∧ deningerDivisor u = n ∧ ∀ p ∈ S, deningerDivisor u p = 0 := by
  refine ⟨deningerDivisorProduct n, deningerDivisorProduct_pos n,
    deningerDivisor_divisorProduct n, fun p hp => ?_⟩
  rw [deningerDivisor_divisorProduct n]
  exact hn p hp

end Divisor

end RHTower
