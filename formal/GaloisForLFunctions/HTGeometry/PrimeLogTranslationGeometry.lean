import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# Prime-log translation geometry

The prime-log divisor is an additive Sidon carrier: two oriented differences coincide only for the
same ordered pair, apart from the common diagonal value zero.  Consequently, two distinct complex
translates of the divisor share at most one pole, and every member of a finite translation packet
has infinitely many private poles.

This is source geometry, not yet translation hypertranscendence.  Its role is to reduce any finite
translation relation to infinitely many one-carrier local tests without pole collisions.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Exact additive Sidon law for prime logarithms, including the degenerate diagonal. -/
theorem primeLogSupport_sub_eq_sub_iff
    (p q r s : Nat.Primes) :
    primeLogSupport p - primeLogSupport q =
        primeLogSupport r - primeLogSupport s ↔
      (p = r ∧ q = s) ∨ (p = q ∧ r = s) := by
  constructor
  · intro h
    by_cases hpq : p = q
    · right
      refine ⟨hpq, ?_⟩
      apply primeLogSupport_injective
      rw [hpq, sub_self] at h
      linarith
    · left
      have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
      have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.2.pos
      have hr0 : (0 : ℝ) < (r : ℕ) := by exact_mod_cast r.2.pos
      have hs0 : (0 : ℝ) < (s : ℕ) := by exact_mod_cast s.2.pos
      have hratio : ((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) =
          ((r : ℕ) : ℝ) / ((s : ℕ) : ℝ) := by
        have hexp := congrArg Real.exp h
        simpa [primeLogSupport, Real.exp_sub, Real.exp_log hp0, Real.exp_log hq0,
          Real.exp_log hr0, Real.exp_log hs0] using hexp
      have hmulReal : ((p : ℕ) : ℝ) * ((s : ℕ) : ℝ) =
          ((r : ℕ) : ℝ) * ((q : ℕ) : ℝ) :=
        (div_eq_div_iff (ne_of_gt hq0) (ne_of_gt hs0)).mp hratio
      have hmul : (p : ℕ) * (s : ℕ) = (r : ℕ) * (q : ℕ) := by
        exact_mod_cast hmulReal
      have hpdiv : (p : ℕ) ∣ (r : ℕ) * (q : ℕ) := by
        rw [← hmul]
        exact dvd_mul_right _ _
      rcases p.2.dvd_mul.mp hpdiv with hpr | hpqdiv
      · have hprEq : p = r := by
          apply Subtype.ext
          exact (Nat.prime_dvd_prime_iff_eq p.2 r.2).mp hpr
        subst r
        have hqsEq : q = s := by
          apply Subtype.ext
          exact Nat.eq_of_mul_eq_mul_left p.2.pos hmul.symm
        exact ⟨rfl, hqsEq⟩
      · exfalso
        apply hpq
        apply Subtype.ext
        exact (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hpqdiv
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp

/-- Source poles of the `h`-translate that collide with the `k`-translate. -/
def primeLogComplexShiftCollisionPrimes (h k : ℂ) : Set Nat.Primes :=
  {p | ∃ q : Nat.Primes,
    (primeLogSupport p : ℂ) - h = (primeLogSupport q : ℂ) - k}

/-- Any two distinct complex translates of the prime-log divisor share at most one pole. -/
theorem primeLogComplexShiftCollisionPrimes_subsingleton {h k : ℂ} (hhk : h ≠ k) :
    (primeLogComplexShiftCollisionPrimes h k).Subsingleton := by
  intro p hp p' hp'
  rcases hp with ⟨q, hpq⟩
  rcases hp' with ⟨q', hpq'⟩
  have hdiffComplex :
      (primeLogSupport p : ℂ) - (primeLogSupport q : ℂ) =
        (primeLogSupport p' : ℂ) - (primeLogSupport q' : ℂ) := by
    linear_combination hpq - hpq'
  have hdiff : primeLogSupport p - primeLogSupport q =
      primeLogSupport p' - primeLogSupport q' := by
    exact congrArg Complex.re hdiffComplex
  rcases (primeLogSupport_sub_eq_sub_iff p q p' q').mp hdiff with hsame | hdiag
  · exact hsame.1
  · exfalso
    apply hhk
    rw [hdiag.1] at hpq
    linear_combination -hpq

theorem primeLogComplexShiftCollisionPrimes_finite {h k : ℂ} (hhk : h ≠ k) :
    (primeLogComplexShiftCollisionPrimes h k).Finite :=
  (primeLogComplexShiftCollisionPrimes_subsingleton hhk).finite

/-- The finite exceptional source set for one member of a finite complex-translation packet. -/
def primeLogComplexBadPrimes (H : Finset ℂ) (h : ℂ) : Set Nat.Primes :=
  ⋃ k ∈ (H.erase h : Set ℂ), primeLogComplexShiftCollisionPrimes h k

theorem primeLogComplexBadPrimes_finite (H : Finset ℂ) (h : ℂ) :
    (primeLogComplexBadPrimes H h).Finite := by
  apply Set.Finite.biUnion (H.erase h).finite_toSet
  intro k hk
  exact primeLogComplexShiftCollisionPrimes_finite
    (Ne.symm (Finset.ne_of_mem_erase hk))

/-- Outside the exceptional set, a pole of the `h`-translate belongs to no other translate in the
packet. -/
theorem primeLogComplex_private_of_notMem_bad
    (H : Finset ℂ) (h : ℂ) {p : Nat.Primes}
    (hp : p ∉ primeLogComplexBadPrimes H h) :
    ∀ k ∈ H, k ≠ h → ∀ q : Nat.Primes,
      (primeLogSupport p : ℂ) - h ≠ (primeLogSupport q : ℂ) - k := by
  intro k hkH hkh q heq
  apply hp
  simp only [primeLogComplexBadPrimes, Set.mem_iUnion]
  exact ⟨k, ⟨Finset.mem_erase.mpr ⟨hkh, hkH⟩, ⟨q, heq⟩⟩⟩

/-- Every translate in a finite complex packet has infinitely many private poles. -/
theorem infinite_primeLogComplex_privatePrimes (H : Finset ℂ) (h : ℂ) :
    (primeLogComplexBadPrimes H h)ᶜ.Infinite := by
  rw [show (primeLogComplexBadPrimes H h)ᶜ =
      Set.univ \ primeLogComplexBadPrimes H h by ext; simp]
  exact Set.infinite_univ.sdiff (primeLogComplexBadPrimes_finite H h)

end GaloisForLFunctions.HTGeometry
