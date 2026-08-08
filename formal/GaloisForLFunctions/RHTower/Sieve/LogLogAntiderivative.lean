import GaloisForLFunctions.RHTower.Sieve.CesaroKernelPrimitives

/-!
# The antiderivative of `1/(u log u)`

`log log` differentiates to `1/(u log u)` above `1`, so

`∫_a^b du/(u log u) = log log b − log log a`   for `1 < a ≤ b`.

This is the integral that makes the Cesàro Perron error finite.  Perron's lemma bounds the sharp-cutoff
error by `u^σ/(πT log u)`, whose factor `1/log u` diverges at the cutoff; under the logarithmic average
`du/u` it becomes `1/(u log u)`, whose integral from `1 + 1/T` to `2` is `log log 2 − log log(1 + 1/T)`,
that is `O(log T)` — a loss of one logarithm of the height in place of the factor `N` that the
sharp-cutoff route pays.
-/

noncomputable section
namespace RHTower.Sieve
open MeasureTheory

/-- `log log` differentiates to `1/(u log u)` above `1`. -/
theorem hasDerivAt_log_log {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun v : ℝ => Real.log (Real.log v)) (1 / (u * Real.log u)) u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogpos : (0 : ℝ) < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
  have h2 := (Real.hasDerivAt_log (ne_of_gt hlogpos)).comp u h1
  have hval : (Real.log u)⁻¹ * u⁻¹ = 1 / (u * Real.log u) := by
    field_simp
  rwa [hval] at h2

/-- `1/(u log u)` is continuous above `1`. -/
theorem continuousOn_inv_mul_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => 1 / (u * Real.log u)) (Set.uIcc a b) := by
  have hmem : ∀ u ∈ Set.uIcc a b, 1 < u := by
    intro u hu
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hu
    linarith [hu.1]
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · exact continuousOn_id.mul (Real.continuousOn_log.mono fun u hu => by
      have := hmem u hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at this
      linarith)
  · intro u hu
    have h1 := hmem u hu
    have hlogpos : (0 : ℝ) < Real.log u := Real.log_pos h1
    have hu0 : (0 : ℝ) < u := by linarith
    exact (mul_pos hu0 hlogpos).ne'

/-- **The antiderivative of `1/(u log u)`.** -/
theorem integral_inv_mul_log_eq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ u in a..b, 1 / (u * Real.log u))
      = Real.log (Real.log b) - Real.log (Real.log a) := by
  have hmem : ∀ u ∈ Set.uIcc a b, 1 < u := by
    intro u hu
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hu
    linarith [hu.1]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_log_log (hmem u hu))
    ((continuousOn_inv_mul_log ha hab).intervalIntegrable)

end RHTower.Sieve
end
