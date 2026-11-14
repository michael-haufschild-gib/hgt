import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterCentralLimit

/-!
# Prime-power Eisenstein traces under Sato–Tate phase sampling

At a prime power, the divisor trace is a symmetric-power character at phase
`b log p`. Rescaling `b` to `θ/log p` transfers the exact local moments and
the independent-coordinate Gaussian limit to the existing arithmetic trace.
-/

open MeasureTheory ProbabilityTheory Filter
open GaloisForLFunctions.ArithmeticInnerFunctionTheory
open scoped BigOperators

namespace GaloisForLFunctions.CompletedArithmeticForms

noncomputable section

/-- Dividing by `log p` calibrates the prime-power trace to the angle itself. -/
theorem eisensteinTrace_phase (p : Nat.Primes) (m : ℕ) (θ : ℝ) :
    eisensteinTrace (θ / Real.log p.val) (p.val ^ m) = cosSum θ m := by
  rw [eisensteinTrace_prime_pow_eq_cosSum _ p.property,
    div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by exact_mod_cast p.property.one_lt)))]

/-- Prime-power traces at Sato–Tate phases have exact diagonal second moments. -/
theorem integral_eisensteinTrace_phase_mul (p : Nat.Primes) (m n : ℕ) :
    ∫ θ, eisensteinTrace (θ / Real.log p.val) (p.val ^ m) *
      eisensteinTrace (θ / Real.log p.val) (p.val ^ n) ∂satoTate =
        if m = n then 1 else 0 := by
  simp_rw [eisensteinTrace_phase]
  exact integral_cosSum_mul_cosSum m n

/-- The fourth moment of the degree `m` prime-power trace is `m+1`. -/
theorem integral_eisensteinTrace_phase_four (p : Nat.Primes) (m : ℕ) :
    ∫ θ, eisensteinTrace (θ / Real.log p.val) (p.val ^ m) ^ 4 ∂satoTate =
      (m : ℝ) + 1 := by
  simp_rw [eisensteinTrace_phase]
  exact integral_cosSum_four m

/-- Squared prime-power traces inherit the minimum-degree covariance kernel. -/
theorem integral_eisensteinTrace_phase_centered_sq_mul (p : Nat.Primes) (m n : ℕ) :
    ∫ θ, (eisensteinTrace (θ / Real.log p.val) (p.val ^ m) ^ 2 - 1) *
      (eisensteinTrace (θ / Real.log p.val) (p.val ^ n) ^ 2 - 1) ∂satoTate =
        (min m n : ℝ) := by
  simp_rw [eisensteinTrace_phase]
  exact integral_centered_cosSum_sq_mul m n

/-- Independent Sato–Tate phases give Gaussian prime-power trace sums for
any sequence of primes and every fixed positive symmetric-power degree. -/
theorem tendstoInDistribution_eisensteinTrace_phase (p : ℕ → Nat.Primes) (m : ℕ) :
    TendstoInDistribution
      (fun n (ω : ℕ → ℝ) => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        eisensteinTrace (ω i / Real.log (p i).val) ((p i).val ^ (m + 1)))
      atTop (id : ℝ → ℝ) (fun _ => satoTateSequenceMeasure) (gaussianReal 0 1) := by
  simp_rw [eisensteinTrace_phase]
  exact tendstoInDistribution_satoTateCharacter m

end

end GaloisForLFunctions.CompletedArithmeticForms
