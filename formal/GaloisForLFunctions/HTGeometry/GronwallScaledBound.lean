import GaloisForLFunctions.HTGeometry.GronwallVariableCoefficient

/-!
# The variable-coefficient Grönwall inequality with an arbitrary initial size

`abs_le_exp_integral_of_volterra_bound` is normalized: it assumes `|h| ≤ 1 + ∫ φ|h|`.  A Volterra
inequality produced by an actual differential equation carries the initial size of the solution
instead of `1`, and that size may be zero.  Rescaling by `K + ε` and letting `ε` shrink removes the
normalization without a positivity hypothesis on `K`:

```text
|h| ≤ K + ∫ φ|h|   ⟹   |h| ≤ K · exp(∫ φ) .
```

The `K = 0` case is the uniqueness statement — a solution starting at zero stays zero.
-/

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Grönwall with an arbitrary initial size.** -/
theorem abs_le_const_mul_exp_of_volterra_bound {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    {h φ : ℝ → ℝ} (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hbd : ∀ x ∈ Icc a b, |h x| ≤ K + ∫ t in a..x, φ t * |h t|) :
    ∀ x ∈ Icc a b, |h x| ≤ K * Real.exp (∫ t in a..x, φ t) := by
  intro x hx
  have hEpos : 0 < Real.exp (∫ t in a..x, φ t) := Real.exp_pos _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / Real.exp (∫ t in a..x, φ t) with hεdef
  have hε : 0 < ε := by positivity
  have hKε : 0 < K + ε := by linarith
  have hscaled : ∀ y ∈ Icc a b,
      |(fun t => h t / (K + ε)) y| ≤ 1 + ∫ t in a..y, φ t * |(fun t => h t / (K + ε)) t| := by
    intro y hy
    have hb := hbd y hy
    simp only [abs_div, abs_of_pos hKε]
    have hdiv : (∫ t in a..y, φ t * (|h t| / (K + ε)))
        = (∫ t in a..y, φ t * |h t|) / (K + ε) := by
      rw [← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [hdiv, div_le_iff₀ hKε]
    have hnn : (0 : ℝ) ≤ ∫ t in a..y, φ t * |h t| := by
      refine intervalIntegral.integral_nonneg hy.1 fun t _ => ?_
      exact mul_nonneg (hφ0 t) (abs_nonneg _)
    have : (1 + (∫ t in a..y, φ t * |h t|) / (K + ε)) * (K + ε)
        = K + ε + ∫ t in a..y, φ t * |h t| := by
      field_simp
    rw [this]
    linarith
  have hmain := abs_le_exp_integral_of_volterra_bound hab (hh.div_const (K + ε)) hφ hφ0
    hscaled x hx
  simp only [abs_div, abs_of_pos hKε] at hmain
  rw [div_le_iff₀ hKε] at hmain
  have hδeq : ε * Real.exp (∫ t in a..x, φ t) = δ := by
    rw [hεdef]
    field_simp
  calc |h x| ≤ Real.exp (∫ t in a..x, φ t) * (K + ε) := hmain
    _ = K * Real.exp (∫ t in a..x, φ t) + ε * Real.exp (∫ t in a..x, φ t) := by ring
    _ = K * Real.exp (∫ t in a..x, φ t) + δ := by rw [hδeq]

end GaloisForLFunctions.HTGeometry
