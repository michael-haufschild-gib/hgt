import Mathlib

/-!
# Energy bound from an amplifier inequality

If a quantity `A` equals `c·P·B` on one side and is bounded by `K·√(2P)·√(P·B)` on the other, then the
energy `B` is bounded by an absolute multiple of `K²`, independently of `P`.

This is the shape produced by testing an identity against a mollified amplifier of length `P`: the
arithmetic side evaluates to `P` times the energy, the analytic side is bounded by a sup-norm `K`
times an `L¹` norm, and Cauchy–Schwarz on an interval of length `≍ P` converts that `L¹` norm into
`√P` times an `L²` norm which is itself `≍ √(P·B)`. The factors of `P` cancel and only `√B ≪ K`
survives.

Corpus check: no existing declaration in this repository states this inequality; the nearest
neighbours (`schwarzPairCauchyEnergy_*`, `AbstractSpectralMass`) are unrelated Gram/Szegő
computations.
-/

namespace HTGeometry

/-- **Amplifier energy bound.**  From `A = c·P·B` and `A ≤ K·√(2P)·√(P·B)` with `c, P > 0`, `B ≥ 0`,
`K ≥ 0`, one gets `B ≤ 2K²/c²` — no dependence on `P`. -/
theorem energy_le_of_amplifier {A B K P c : ℝ} (hP : 0 < P) (hc : 0 < c) (hB : 0 ≤ B)
    (hA : A = c * P * B) (hbound : A ≤ K * Real.sqrt (2 * P) * Real.sqrt (P * B)) :
    B ≤ 2 * K ^ 2 / c ^ 2 := by
  have hsq : Real.sqrt (2 * P) * Real.sqrt (P * B) = Real.sqrt 2 * P * Real.sqrt B := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * P)]
    have h : 2 * P * (P * B) = (Real.sqrt 2 * P) ^ 2 * B := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hb2 : c * P * B ≤ K * (Real.sqrt 2 * P * Real.sqrt B) := by
    have h := hbound
    rw [hA] at h
    calc c * P * B ≤ K * Real.sqrt (2 * P) * Real.sqrt (P * B) := h
      _ = K * (Real.sqrt (2 * P) * Real.sqrt (P * B)) := by ring
      _ = K * (Real.sqrt 2 * P * Real.sqrt B) := by rw [hsq]
  have hBsq : B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB).symm
  rcases eq_or_lt_of_le (Real.sqrt_nonneg B) with hz | hpos
  · have hb0 : B = 0 := by rw [hBsq, ← hz]; ring
    rw [hb0]; positivity
  · have hdiv : c * B ≤ K * (Real.sqrt 2 * Real.sqrt B) := by
      nlinarith [hb2, hP]
    have hstep : c * Real.sqrt B ≤ K * Real.sqrt 2 := by
      nlinarith [hdiv, hBsq, hpos]
    have hsB : Real.sqrt B ≤ K * Real.sqrt 2 / c := by
      rw [le_div_iff₀ hc]; linarith [hstep]
    calc B = Real.sqrt B ^ 2 := hBsq
      _ ≤ (K * Real.sqrt 2 / c) ^ 2 := by
          apply pow_le_pow_left₀ (Real.sqrt_nonneg B) hsB
      _ = 2 * K ^ 2 / c ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring

/-- Specialisation with `c = 1/(2π)`: the constant is `8π²K²`. -/
theorem energy_le_of_amplifier_twopi {A B K P : ℝ} (hP : 0 < P) (hB : 0 ≤ B)
    (hA : A = P * B / (2 * Real.pi))
    (hbound : A ≤ K * Real.sqrt (2 * P) * Real.sqrt (P * B)) :
    B ≤ 8 * Real.pi ^ 2 * K ^ 2 := by
  have hpi : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  have hA' : A = (1 / (2 * Real.pi)) * P * B := by rw [hA]; ring
  have := energy_le_of_amplifier hP hpi hB hA' hbound
  have hne : (2 * Real.pi) ≠ 0 := by positivity
  calc B ≤ 2 * K ^ 2 / (1 / (2 * Real.pi)) ^ 2 := this
    _ = 8 * Real.pi ^ 2 * K ^ 2 := by field_simp; ring

end HTGeometry
