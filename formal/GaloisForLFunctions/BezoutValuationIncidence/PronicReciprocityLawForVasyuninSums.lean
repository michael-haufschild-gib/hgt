import GaloisForLFunctions.BezoutValuationIncidence.TwoSidedCotangentMomentLawFromPronicEnergy

/-!
# A pronic reciprocity law for Vasyunin cotangent sums

For primes `p, q` write `L_p = log p`. The energy-centered pronic Gram on `{p, q}` is positive
semidefinite, so `|K(p, q)| ≤ (K(p, p) + K(q, q))/2`, and its diagonal is pinned by the
cotangent-moment law: `K(p, p) = π V(1, p) + (p - 1) L_p - L_p² ∈ [0, L_p² + p + (p-1)²/p]`.
Expanding `K(p, q)` in Vasyunin sums, all main terms cancel except one:

`(L_q - L_p)² ≤ π (V(q, p) + V(p, q)) + (q - p)(L_q - L_p)`
`           ≤ (L_q - L_p)² + 2 (L_p² + L_q² + p + q + (p-1)²/p + (q-1)²/q)`.

So `π (V(q/p) + V(p/q)) = -(q - p) log(q/p) + O(p + q)`, with explicit constants. This is an
elementary reciprocity law for the cotangent sums of the Nyman–Beurling Gram, obtained entirely from
pronic positivity.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The diagonal kernel in Vasyunin form: `K(p, p) = π V(1, p) + (p - 1) log p - log² p`. -/
theorem vasyuninPrimeKernel_diag {p : ℕ} (hp : p.Prime) :
    vasyuninPrimeKernel p p =
      Real.pi * vasyuninSum 1 p + ((p : ℝ) - 1) * Real.log p - Real.log p ^ 2 := by
  have hVpp : vasyuninSum p p = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [show (p : ℝ) * a / p = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  rw [vasyuninPrimeKernel, hVpp, sieveCenteringDiscrepancy, Nat.totient_prime hp,
    vonMangoldt_apply_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  ring

/-- `|K(p, q)| ≤ (K(p, p) + K(q, q))/2` from positivity at `x = (1, ±1)`. -/
theorem abs_vasyuninPrimeKernel_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |vasyuninPrimeKernel p q| ≤ (vasyuninPrimeKernel p p + vasyuninPrimeKernel q q) / 2 := by
  have hsymm : vasyuninPrimeKernel q p = vasyuninPrimeKernel p q := by
    unfold vasyuninPrimeKernel
    ring
  have hS : ∀ r ∈ ({p, q} : Finset ℕ), r.Prime := by
    simp only [mem_insert, mem_singleton]
    rintro r (rfl | rfl) <;> assumption
  have hplus := sum_sum_mul_vasyuninPrimeKernel_nonneg {p, q} hS fun _ => 1
  have hminus := sum_sum_mul_vasyuninPrimeKernel_nonneg {p, q} hS fun r => if r = p then -1 else 1
  rw [sum_pair hpq, sum_pair hpq, sum_pair hpq] at hplus hminus
  simp only [if_neg (Ne.symm hpq), hsymm, if_true, one_mul, mul_one] at hplus hminus
  rw [abs_le]
  constructor <;> nlinarith

/-- **Pronic reciprocity law for Vasyunin sums.** -/
theorem vasyunin_reciprocity_law {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (Real.log q - Real.log p) ^ 2 ≤
        Real.pi * (vasyuninSum q p + vasyuninSum p q) +
          ((q : ℝ) - p) * (Real.log q - Real.log p) ∧
      Real.pi * (vasyuninSum q p + vasyuninSum p q) + ((q : ℝ) - p) * (Real.log q - Real.log p) ≤
        (Real.log q - Real.log p) ^ 2 + 2 * (Real.log p ^ 2 + Real.log q ^ 2 + p + q +
          ((p : ℝ) - 1) ^ 2 / p + ((q : ℝ) - 1) ^ 2 / q) := by
  rcases eq_or_ne p q with rfl | hpq
  · have hVpp : vasyuninSum p p = 0 := by
      unfold vasyuninSum
      refine sum_eq_zero fun a _ => ?_
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [show (p : ℝ) * a / p = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
        show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [hVpp, sub_self, add_zero, mul_zero, zero_pow two_ne_zero, zero_add]
    exact ⟨le_rfl, by positivity⟩
  · have habs := abs_vasyuninPrimeKernel_le hp hq hpq
    have hdp := vasyuninPrimeKernel_diag hp
    have hdq := vasyuninPrimeKernel_diag hq
    -- diagonal upper bounds from the pronic energy estimate
    have hup_p := pmRamanujanEnergyCenteredGram_prime_diag_le hp
    have hup_q := pmRamanujanEnergyCenteredGram_prime_diag_le hq
    rw [pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel hp hp] at hup_p
    rw [pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel hq hq] at hup_q
    -- the off-diagonal kernel in Vasyunin form
    have hoff : vasyuninPrimeKernel p q =
        ((p : ℝ) - 1) * ((q : ℝ) - 1) / 4 - Real.pi / 2 * (vasyuninSum q p + vasyuninSum p q) +
          Real.pi / 2 * (vasyuninSum 1 p + vasyuninSum 1 q) -
          (((p : ℝ) - 1) / 2 - Real.log p) * (((q : ℝ) - 1) / 2 - Real.log q) := by
      rw [vasyuninPrimeKernel, sieveCenteringDiscrepancy, sieveCenteringDiscrepancy,
        Nat.totient_prime hp, Nat.totient_prime hq, vonMangoldt_apply_prime hp,
        vonMangoldt_apply_prime hq, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one]
      ring
    rw [abs_le, hoff] at habs
    obtain ⟨h1, h2⟩ := habs
    constructor <;> nlinarith [h1, h2, hdp, hdq, hup_p, hup_q]

end

end GaloisForLFunctions.BezoutValuationIncidence
