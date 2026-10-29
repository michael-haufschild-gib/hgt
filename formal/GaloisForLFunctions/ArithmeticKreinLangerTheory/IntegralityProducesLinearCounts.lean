import GaloisForLFunctions.RHTower.StepanovCharacterSum
import Mathlib.NumberTheory.Primorial

/-!
# Integrality produces linear counts

A **producer** is a construction that yields a one-sided count without assuming it. This module
records the two producers that exist and the precision each reaches, which is the gap the arithmetic
compressor of the programme has to close.

**Over `𝔽_q`: square-root precision for both parity classes** (`stepanov_parity_classes_upper`). For
`q = s²` odd and `h` squarefree, Stepanov's auxiliary polynomial bounds both Legendre parity classes
`{x : h(x)^{(q−1)/2} = ±1}` by `q/2 + (deg h + 1)√q`. The two classes are a curve and its quadratic
twist; the twist tower turns these upper counts into the Riemann hypothesis for the curve
(`unitary_iff_twistTower_upper`).

**Over `ℤ`: linear precision for the primes** (`sum_log_prime_le`). The primorial divides no less than
the product of the primes and is at most `4^n`, so `Σ_{p ≤ n} log p ≤ n log 4`: an integrality
certificate gives an upper count for the primes, a subset of the odd parity class, at relative
precision `log 4`. The global law needs the odd class at precision `x^{½+ε}`
(`negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).

Between them lies the producer problem: an auxiliary object over `ℤ` whose vanishing conditions, like
those of Stepanov's polynomial under `x^q = x`, cost less than the size of the counted set.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- **Stepanov's producer: both parity classes at square-root precision.** Over a finite field of
odd square order `q = s²`, for squarefree `h` of degree at most `s − 5`, each Legendre parity class
along `h` has at most `q/2 + (deg h + 1)√q` points. -/
theorem stepanov_parity_classes_upper {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    {p n : ℕ} [Fact p.Prime] [CharP E p] (hcard : Fintype.card E = p ^ n) {h : E[X]}
    (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree) {N s : ℕ} (hQ : p ^ n = 2 * N + 1)
    (hs : p ^ n = s ^ 2) (hsD : h.natDegree + 5 ≤ s) :
    2 * (univ.filter fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = 1).card ≤
        s ^ 2 + 2 * (h.natDegree + 1) * s ∧
      2 * (univ.filter fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = -1).card ≤
        s ^ 2 + 2 * (h.natDegree + 1) * s :=
  ⟨RHTower.Stepanov.stepanov_bound hcard hsq hdeg hQ hs hsD 1,
    RHTower.Stepanov.stepanov_bound hcard hsq hdeg hQ hs hsD (-1)⟩

/-- **The integrality producer: the primes at linear precision.** `Σ_{p ≤ n} log p ≤ n log 4`, from
the primorial bound `n# ≤ 4^n`. -/
theorem sum_log_prime_le (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p ≤ n * Real.log 4 := by
  have h := primorial_le_four_pow n
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have hlog : Real.log (primorial n) = ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2.ne_zero
  rw [← hlog, ← Real.log_pow]
  exact Real.log_le_log hpos (by exact_mod_cast h)

end GaloisForLFunctions.ArithmeticKreinLangerTheory
