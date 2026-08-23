import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Exact atoms of the Euler-log prime-power Herglotz carrier

This is the finite arithmetic core of the normalized prime-power carrier:
positive prime-power log times, positive weights, and the exact
log-position residue.  Infinite Herglotz convergence is intentionally not
modeled here.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The positive prime-power logarithmic support point `((k+1) log p)`. -/
def eulerLogPrimePowerTime (p : Nat.Primes) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)

/-- The normalized positive Euler-log weight `1 / ((k+1) p^(k+1))`. -/
def eulerLogPrimePowerWeight (p : Nat.Primes) (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1))

/-- Every prime-power logarithmic support point is strictly positive. -/
theorem eulerLogPrimePowerTime_pos (p : Nat.Primes) (k : ℕ) :
    0 < eulerLogPrimePowerTime p k := by
  unfold eulerLogPrimePowerTime
  refine mul_pos ?_ (Real.log_pos ?_)
  · exact_mod_cast Nat.succ_pos k
  · exact_mod_cast p.property.one_lt

/-- Every normalized Euler-log atom has strictly positive weight. -/
theorem eulerLogPrimePowerWeight_pos (p : Nat.Primes) (k : ℕ) :
    0 < eulerLogPrimePowerWeight p k := by
  unfold eulerLogPrimePowerWeight
  apply one_div_pos.mpr
  refine mul_pos ?_ ?_
  · exact_mod_cast Nat.succ_pos k
  · exact pow_pos (by exact_mod_cast p.property.pos) _

/-- Multiplication by log position recovers the exact prime-power residue. -/
theorem eulerLogPrimePowerTime_mul_weight (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerTime p k * eulerLogPrimePowerWeight p k =
      Real.log (p : ℝ) / (p : ℝ) ^ (k + 1) := by
  unfold eulerLogPrimePowerTime eulerLogPrimePowerWeight
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hp : ((p : ℝ) ^ (k + 1)) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  field_simp

end GaloisForLFunctions.RHTower

end
