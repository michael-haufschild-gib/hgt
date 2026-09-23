import GaloisForLFunctions.RHTower.Sieve.PhaseIntegral

/-!
# The squared modulus of a Dirichlet polynomial

`|F(t)|² = ∑_m ∑_n a_m conj(a_n) e^{it(log m - log n)}` for `F(t) = ∑_{n < N} a_n n^{it}`.

Each cross term is a pure phase at the frequency `log m - log n`, so integrating over `[0, T]` and
applying the dichotomy of `PhaseIntegral.lean` separates the diagonal — where the frequency vanishes
and the integral is `T` — from the off-diagonal, where it is at most `2/|log(m/n)|`.

The frequencies of distinct terms are distinct: `log` is injective on the positive reals, so
`m ≠ n` gives `log(m+1) ≠ log(n+1)` and the off-diagonal bound never divides by zero.
-/

namespace RHTower.Sieve

open Finset

/-- A phase times the conjugate of a phase is the phase of the difference. -/
theorem exp_phase_mul_conj (u v t : ℝ) :
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp (((t * v : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((t * (u - v) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Distinct indices give distinct frequencies. -/
theorem log_succ_injective {m n : ℕ} (h : m ≠ n) :
    Real.log ((m : ℝ) + 1) ≠ Real.log ((n : ℝ) + 1) := by
  intro hcon
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have heq : (m : ℝ) + 1 = (n : ℝ) + 1 := by
    have := congrArg Real.exp hcon
    rwa [Real.exp_log hm, Real.exp_log hn] at this
  have : (m : ℝ) = (n : ℝ) := by linarith
  exact h (by exact_mod_cast this)

/-- **The squared modulus of a Dirichlet polynomial, expanded.** -/
theorem normSq_dirPoly_eq (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ m : Fin N, ∑ n : Fin N, (a m * (starRingEnd ℂ) (a n))
          * Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) := by
  have hz : ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = dirPoly N a t * (starRingEnd ℂ) (dirPoly N a t) := by
    rw [mul_comm, conj_mul_self]
  rw [hz, dirPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul]
  calc a m * Complex.exp (((t * Real.log (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        * ((starRingEnd ℂ) (a n)
          * (starRingEnd ℂ) (Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ)
              * Complex.I)))
      = (a m * (starRingEnd ℂ) (a n))
        * (Complex.exp (((t * Real.log (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ)
              * Complex.I))) := by ring
    _ = (a m * (starRingEnd ℂ) (a n))
        * Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
            - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) := by
        rw [exp_phase_mul_conj]

end RHTower.Sieve
