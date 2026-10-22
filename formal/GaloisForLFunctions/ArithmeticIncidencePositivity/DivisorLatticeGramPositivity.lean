import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus

/-!
# The divisor-lattice Gram form and the blindness of the Möbius comb

The incidence face reads the critical form through the ratios of integers. Fix a modulus `q` and
weight its divisors by `c : ℕ → ℝ`; the comb `Σ_{d ∣ q} c d · F(· + log d)` has nonnegative energy,
so the **ratio-incidence matrix of a modulus is positive semidefinite**:

    0 ≤ Σ_{d, e ∣ q} c d · c e · A(log e − log d).

Every minor of that matrix is therefore an unconditional inequality among the charges at the ratios
of divisors of one modulus — the incidence data of a single modulus, with no family average.

Two readings. With the **Möbius row** `c = μ` the comb is the divisor-lattice difference operator,
and on the *resonant* direction — a test whose autocorrelation is maximal at every divisor ratio —
the form collapses to `(Σ_{d ∣ q} μ d)² A(0)`, which vanishes for every `q ≠ 1`: the Möbius comb is
blind exactly where the charges are largest. With the trivial row `c ≡ 1` the same collapse gives
`τ(q)² A(0)`, the maximal value. So on the divisor lattice of one modulus the Möbius row is the
weight that annihilates the resonant mode, and the deviation of the form from `0` measures how far
a test is from resonance.
-/

open MeasureTheory
open scoped ArithmeticFunction
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- The divisor comb of a modulus: `Σ_{d ∣ q} c d · F(· + log d)`. -/
def divisorComb (F : ℝ → ℝ) (q : ℕ) (c : ℕ → ℝ) : ℝ → ℝ :=
  finsetComb F q.divisors c (fun d => Real.log d)

/-- **The divisor-lattice Gram positivity.** For every modulus and every weighting of its divisors
the ratio-incidence matrix `[A(log e − log d)]_{d,e ∣ q}` is positive semidefinite. -/
theorem divisor_gram_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) (q : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ q.divisors, ∑ e ∈ q.divisors,
      c d * c e * autoCorr F (Real.log e - Real.log d) := by
  have h := testPairing_self_nonneg (divisorComb F q c)
  rwa [divisorComb, testPairing_finsetComb ⟨hF, hFc⟩] at h

/-- **On the resonant direction the form is the square of the total weight.** If the test
correlates maximally at every ratio of divisors of `q`, the divisor Gram form equals
`(Σ_{d ∣ q} c d)² A(0)`. -/
theorem divisor_gram_eq_of_resonant {q : ℕ} (c : ℕ → ℝ)
    (hres : ∀ d ∈ q.divisors, ∀ e ∈ q.divisors,
      autoCorr F (Real.log e - Real.log d) = autoCorr F 0) :
    ∑ d ∈ q.divisors, ∑ e ∈ q.divisors, c d * c e * autoCorr F (Real.log e - Real.log d)
      = (∑ d ∈ q.divisors, c d) ^ 2 * autoCorr F 0 := by
  have hrow : ∀ d ∈ q.divisors,
      ∑ e ∈ q.divisors, c d * c e * autoCorr F (Real.log e - Real.log d)
        = c d * ((∑ e ∈ q.divisors, c e) * autoCorr F 0) := by
    intro d hd
    have hterm : ∀ e ∈ q.divisors, c d * c e * autoCorr F (Real.log e - Real.log d)
        = c d * (c e * autoCorr F 0) := fun e he => by rw [hres d hd e he]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul]
  ring

/-- **The Möbius comb is blind on the resonant direction.** For every modulus `q ≠ 1` the Möbius
weighting of the divisor lattice gives energy `0` on a test that correlates maximally at every
divisor ratio, while the trivial weighting gives the maximal energy `τ(q)² A(0)`. So the Möbius row
is the weight that annihilates the resonant mode of a modulus. -/
theorem moebius_divisor_gram_eq_zero_of_resonant {q : ℕ} (hq : q ≠ 1) (hq0 : q ≠ 0)
    (hres : ∀ d ∈ q.divisors, ∀ e ∈ q.divisors,
      autoCorr F (Real.log e - Real.log d) = autoCorr F 0) :
    ∑ d ∈ q.divisors, ∑ e ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℝ)) * ((ArithmeticFunction.moebius e : ℝ)) * autoCorr F (Real.log e - Real.log d) = 0 := by
  have hsum : ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ)) = 0 := by
    have hz : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ)
        = ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) q) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply, if_neg hq] at hz
    have : ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ)) = ((∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [this, hz]
    norm_num
  rw [divisor_gram_eq_of_resonant _ hres, hsum]
  ring

end GaloisForLFunctions.ArithmeticIncidencePositivity
