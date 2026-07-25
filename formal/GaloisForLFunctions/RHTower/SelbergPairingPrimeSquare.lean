import Mathlib

/-!
# The Selberg pairing is the additivity defect of the prime-square coefficient

Selberg's orthogonality conjecture concerns the bilinear prime sums
`∑_{p ≤ x} a_F(p) conj(a_G(p)) / p`, where `a_F`, `a_G` are the Dirichlet coefficients of two
elements of the Selberg class.  The Selberg class is a monoid under multiplication of Dirichlet
series, i.e. under Dirichlet convolution of coefficients, and the prime-coefficient map is
*additive* for that operation: `a_{FG}(p) = a_F(p) + a_G(p)`.  The pairing above is *bilinear*,
so it is invisible to the monoid structure at primes.

At prime squares the situation is different.  Dirichlet convolution has an exact three-term
expansion at `p²`, and it produces the product `a_F(p) a_G(p)` as its middle term.  Consequently
the bilinear pairing is exactly the failure of additivity of the *linear* functional
`H ↦ a_H(p²)`:

`a_F(p) conj(a_G(p)) = a_{F · conj G}(p²) − a_F(p²) − conj(a_G(p²))`.

Summing over primes turns a statement about a pair of Dirichlet series into a statement about
single Dirichlet series evaluated at prime squares.

Everything here is unconditional and purely algebraic: no analytic axiom of the Selberg class is
used, only `a(1) = 1` and multiplicativity of Dirichlet convolution.
-/

open ArithmeticFunction Finset

namespace RHTower

noncomputable section

/-- The divisor pairs of a prime square are exactly `(1,p²)`, `(p,p)` and `(p²,1)`. -/
theorem divisorsAntidiagonal_prime_sq {p : ℕ} (hp : p.Prime) :
    (p ^ 2).divisorsAntidiagonal = {(1, p ^ 2), (p, p), (p ^ 2, 1)} := by
  ext xy
  rw [Nat.mem_divisorsAntidiagonal]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hprod, hne⟩
    have hdvd : xy.1 ∣ p ^ 2 := ⟨xy.2, hprod.symm⟩
    obtain ⟨m, hm, hxm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hp0 : p ≠ 0 := hp.ne_zero
    interval_cases m
    · left
      refine Prod.ext ?_ ?_
      · simpa using hxm
      · simp only [pow_zero] at hxm
        rw [hxm, one_mul] at hprod
        exact hprod
    · right; left
      refine Prod.ext ?_ ?_
      · simpa using hxm
      · simp only [pow_one] at hxm
        show xy.2 = p
        have h2 : p * xy.2 = p * p := by
          calc p * xy.2 = xy.1 * xy.2 := by rw [hxm]
            _ = p ^ 2 := hprod
            _ = p * p := by ring
        exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    · right; right
      refine Prod.ext ?_ ?_
      · simpa using hxm
      · show xy.2 = 1
        have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
        have h2 : p ^ 2 * xy.2 = p ^ 2 * 1 := by
          rw [mul_one]
          calc p ^ 2 * xy.2 = xy.1 * xy.2 := by rw [hxm]
            _ = p ^ 2 := hprod
        exact Nat.eq_of_mul_eq_mul_left hpos h2
  · rintro (h | h | h) <;> subst h <;>
      exact ⟨by ring, pow_ne_zero 2 hp.ne_zero⟩

/-- Exact three-term expansion of Dirichlet convolution at a prime square. -/
theorem arithmeticFunction_mul_apply_prime_sq {R : Type*} [CommSemiring R]
    (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) :
    (f * g) (p ^ 2) = f 1 * g (p ^ 2) + f p * g p + f (p ^ 2) * g 1 := by
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 1 < p ^ 2 := by nlinarith [hp.two_le]
  rw [ArithmeticFunction.mul_apply, divisorsAntidiagonal_prime_sq hp]
  have h1 : ((1 : ℕ), p ^ 2) ≠ (p, p) := fun h => hp1.ne (congrArg Prod.fst h)
  have h2 : ((1 : ℕ), p ^ 2) ≠ (p ^ 2, 1) := fun h => hp2.ne (congrArg Prod.fst h)
  have h3 : ((p : ℕ), p) ≠ (p ^ 2, 1) := fun h => hp1.ne' (congrArg Prod.snd h)
  rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_insert (by simp [h3]),
    Finset.sum_singleton]
  ring

/-- Complex conjugation of the coefficients of an arithmetic function. -/
def conjArith (g : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := starRingEnd ℂ (g n)
  map_zero' := by simp

@[simp] theorem conjArith_apply (g : ArithmeticFunction ℂ) (n : ℕ) :
    conjArith g n = starRingEnd ℂ (g n) := rfl

/-- **The Selberg pairing identity.**  For normalised coefficient systems the prime-coefficient
product `a_F(p) · conj a_G(p)` — the summand of Selberg's orthogonality conjecture — equals the
failure of additivity, at `p²`, of the linear coefficient functional.  No analytic hypothesis is
used. -/
theorem selberg_pairing_prime_sq (f g : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (hg : g 1 = 1) {p : ℕ} (hp : p.Prime) :
    f p * starRingEnd ℂ (g p)
      = (f * conjArith g) (p ^ 2) - f (p ^ 2) - starRingEnd ℂ (g (p ^ 2)) := by
  have hcg : conjArith g 1 = 1 := by simp [hg]
  rw [arithmeticFunction_mul_apply_prime_sq f (conjArith g) hp, hf, hcg]
  simp only [conjArith_apply]
  ring

/-- The weighted prime sum of Selberg's orthogonality conjecture, over any finite set of primes,
is a difference of three prime-square sums of single coefficient systems. -/
theorem selberg_pairing_sum_eq (f g : ArithmeticFunction ℂ)
    (hf : f 1 = 1) (hg : g 1 = 1) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, f p * starRingEnd ℂ (g p) / (p : ℂ)
      = (∑ p ∈ P, (f * conjArith g) (p ^ 2) / (p : ℂ))
        - (∑ p ∈ P, f (p ^ 2) / (p : ℂ))
        - ∑ p ∈ P, starRingEnd ℂ (g (p ^ 2)) / (p : ℂ) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [selberg_pairing_prime_sq f g hf hg (hP p hp)]
  ring

end

end RHTower
