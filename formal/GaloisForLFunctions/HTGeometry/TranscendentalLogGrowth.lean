import GaloisForLFunctions.HTGeometry.CentralIndexDivergence

/-!
# Transcendental growth in logarithmic form

A transcendental entire power series has a maximum term that outgrows every power of the radius.  In
logarithmic form: `log mu(s)` eventually exceeds any prescribed affine function of `log s`.  This is
the shape a growth-separation argument consumes, where one has to beat a fixed multiple of the
logarithm of an inner function's size.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **The log of the maximum term beats every affine function of `log s`.** -/
theorem eventually_log_maxTerm_ge (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) (k : ℕ) (C : ℝ) :
    ∀ᶠ s : ℝ in atTop, C + (k : ℝ) * Real.log s ≤ Real.log (maxTerm a s) := by
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  have htend := tendsto_maxTerm_div_pow_atTop ha htrans k
  have hev := htend.eventually_ge_atTop (Real.exp C)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with s hs hspos
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hspos hn₀
  have hspow : (0 : ℝ) < s ^ k := pow_pos hspos k
  have hdivpos : (0 : ℝ) < maxTerm a s / s ^ k := by positivity
  have hlogdiv : Real.log (maxTerm a s / s ^ k)
      = Real.log (maxTerm a s) - (k : ℝ) * Real.log s := by
    rw [Real.log_div (ne_of_gt hμpos) (ne_of_gt hspow), Real.log_pow]
  have hCle : C ≤ Real.log (maxTerm a s / s ^ k) :=
    (Real.le_log_iff_exp_le hdivpos).mpr hs
  rw [hlogdiv] at hCle
  linarith

end GaloisForLFunctions.HTGeometry
