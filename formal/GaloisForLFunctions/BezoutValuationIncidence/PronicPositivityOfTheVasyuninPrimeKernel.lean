import GaloisForLFunctions.BezoutValuationIncidence.VasyuninCotangentSumsInThePrimePronicGram
import GaloisForLFunctions.BezoutValuationIncidence.ExplicitDilationProfileAtRationalScales

/-!
# Pronic positivity of the Vasyunin kernel on primes

On primes the energy-centered pronic Gram is an explicit combination of Vasyunin cotangent sums:

`G^{ec}(p, q) = K(p, q) := (p-1)(q-1)/4 - (π/2)(V(q,p) - V(1,p) + V(p,q) - V(1,q)) - D(p) D(q)`,

`D(p) = (p - 1)/2 - log p`. Since `G^{ec}` is a pronic inner product of the energy-centered
primitives, the kernel `K` is positive semidefinite on every finite set of primes. This yields
elementary inequalities for cotangent sums with no analytic input:

* `π V(1, p) ≥ D(p)² - (p - 1)²/4 = log² p - (p - 1) log p`, i.e.
  `Σ_{a<p} a cot(πa/p) ≥ (p/π)(log² p - (p - 1) log p)`, of the true leading order;
* `K(p, q)² ≤ K(p, p) K(q, q)`: the reciprocity combination `V(q,p) + V(p,q)` is determined by
  the explicit main terms up to `√(K(p,p) K(q,q))`.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The Vasyunin kernel on primes. -/
def vasyuninPrimeKernel (p q : ℕ) : ℝ :=
  ((p : ℝ) - 1) * ((q : ℝ) - 1) / 4 -
    Real.pi / 2 * (vasyuninSum q p - vasyuninSum 1 p + vasyuninSum p q - vasyuninSum 1 q) -
      sieveCenteringDiscrepancy p * sieveCenteringDiscrepancy q

theorem pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) : pmRamanujanEnergyCenteredGram p q = vasyuninPrimeKernel p q := by
  rw [pmRamanujanEnergyCenteredGram_eq_cotangentSawtoothForm hp.two_le hq.two_le,
    ← pmRamanujanMeanCenteredGram_eq_cotangentSawtoothForm hp.two_le hq.two_le,
    pmRamanujanMeanCenteredGram_prime_eq_vasyunin hp hq, vasyuninPrimeKernel]

/-- **The energy-centered pronic Gram is positive semidefinite.** -/
theorem sum_sum_mul_pmRamanujanEnergyCenteredGram_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p)
    (x : ℕ → ℝ) : 0 ≤ ∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q := by
  have hterm : ∀ p ∈ S, ∀ q ∈ S, HasSum (fun N : ℕ => x p * x q *
      (pmRamanujanEnergyCenteredPrimitive p N * pmRamanujanEnergyCenteredPrimitive q N /
        ((N : ℝ) * ((N : ℝ) + 1)))) (x p * x q * pmRamanujanEnergyCenteredGram p q) := by
    intro p hp q hq
    have h := hasSum_pmRamanujanEnergyCenteredGram (hS p hp) (hS q hq)
    rw [pmRamanujanPrimitiveGram_eq_energyCentered (hS p hp) (hS q hq), add_sub_cancel_left] at h
    exact h.mul_left _
  have hsum := hasSum_sum fun p hp => hasSum_sum fun q hq => hterm p hp q hq
  refine hsum.nonneg fun N => ?_
  have hsq : ∑ p ∈ S, ∑ q ∈ S, x p * x q * (pmRamanujanEnergyCenteredPrimitive p N *
      pmRamanujanEnergyCenteredPrimitive q N / ((N : ℝ) * ((N : ℝ) + 1))) =
      (∑ p ∈ S, x p * pmRamanujanEnergyCenteredPrimitive p N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
    rw [sq, sum_mul_sum, sum_div]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_div]
    exact sum_congr rfl fun q _ => by ring
  rw [hsq]
  positivity

/-- **The Vasyunin kernel is positive semidefinite on every finite set of primes.** -/
theorem sum_sum_mul_vasyuninPrimeKernel_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x : ℕ → ℝ) : 0 ≤ ∑ p ∈ S, ∑ q ∈ S, x p * x q * vasyuninPrimeKernel p q := by
  have h := sum_sum_mul_pmRamanujanEnergyCenteredGram_nonneg S (fun p hp => (hS p hp).one_lt) x
  rwa [sum_congr rfl fun p hp => sum_congr rfl fun q hq => by
    rw [pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel (hS p hp) (hS q hq)]] at h

/-- **Lower bound for the cotangent moment.** `π V(1, p) ≥ log² p - (p - 1) log p`. -/
theorem vasyuninSum_one_prime_ge {p : ℕ} (hp : p.Prime) :
    Real.log p ^ 2 - ((p : ℝ) - 1) * Real.log p ≤ Real.pi * vasyuninSum 1 p := by
  have h := sum_sum_mul_vasyuninPrimeKernel_nonneg {p} (by simpa using hp) fun _ => 1
  simp only [sum_singleton, one_mul] at h
  have hVpp : vasyuninSum p p = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [show (p : ℝ) * a / p = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  rw [vasyuninPrimeKernel, hVpp, sieveCenteringDiscrepancy, Nat.totient_prime hp,
    vonMangoldt_apply_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] at h
  nlinarith [Real.pi_pos]

/-- **Reciprocity inequality.** `K(p, q)² ≤ K(p, p) K(q, q)` for primes `p, q`. -/
theorem vasyuninPrimeKernel_sq_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    vasyuninPrimeKernel p q ^ 2 ≤ vasyuninPrimeKernel p p * vasyuninPrimeKernel q q := by
  have hsymm : vasyuninPrimeKernel q p = vasyuninPrimeKernel p q := by
    unfold vasyuninPrimeKernel
    ring
  rcases eq_or_ne p q with rfl | hpq
  · have h := sum_sum_mul_vasyuninPrimeKernel_nonneg {p} (by simpa using hp) fun _ => 1
    simp only [sum_singleton, one_mul] at h
    nlinarith [sq_nonneg (vasyuninPrimeKernel p p)]
  · have hquad : ∀ t : ℝ, 0 ≤ vasyuninPrimeKernel p p * (t * t) +
        2 * vasyuninPrimeKernel p q * t + vasyuninPrimeKernel q q := by
      intro t
      have h := sum_sum_mul_vasyuninPrimeKernel_nonneg {p, q}
        (by simp only [mem_insert, mem_singleton]; rintro r (rfl | rfl) <;> assumption)
        fun r => if r = p then t else 1
      rw [sum_pair hpq, sum_pair hpq, sum_pair hpq] at h
      simp only [if_neg (Ne.symm hpq), hsymm, if_true, one_mul, mul_one] at h
      nlinarith [h]
    have hd := discrim_le_zero hquad
    rw [discrim] at hd
    nlinarith [hd]

end

end GaloisForLFunctions.BezoutValuationIncidence
