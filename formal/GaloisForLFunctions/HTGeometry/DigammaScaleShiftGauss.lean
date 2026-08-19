import GaloisForLFunctions.HTGeometry.PolygammaMultiplication

/-!
# Gauss multiplication at a scaled and shifted argument

`ψ(n w + μ)` is a `ℂ`-combination of unit-scale shifted digammas `ψ(w + (μ+k)/n)`.  This is the
step that turns the commensurable-scale logarithmic derivative `G'/G = α + ∑_j λ_j ψ(λ_j s + μ_j)`
into an element of a shifted digamma jet field, where the boundary datum needs no hypothesis beyond
pairwise incongruence of the shifts.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Gauss multiplication with a shift.** -/
theorem digamma_scale_shift_eq_sum {n : ℕ} (hn : 0 < n) {w μ : ℂ}
    (hz : ∀ m : ℕ, (n : ℂ) * w + μ ≠ -(m : ℂ)) :
    (n : ℂ) * Complex.digamma ((n : ℂ) * w + μ)
      = (∑ k ∈ Finset.range n, Complex.digamma (w + (μ + (k : ℂ)) / (n : ℂ)))
        + (n : ℂ) * Complex.log (n : ℂ) := by
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hzz : ∀ m : ℕ, (n : ℂ) * (w + μ / (n : ℂ)) ≠ -(m : ℂ) := by
    intro m
    rw [mul_add, mul_div_cancel₀ _ hnne]
    exact hz m
  have h := digamma_multiplication_rescaled hn hzz
  rw [mul_add, mul_div_cancel₀ _ hnne] at h
  have hterm : ∀ k ∈ Finset.range n,
      Complex.digamma (w + μ / (n : ℂ) + (k : ℂ) / (n : ℂ))
        = Complex.digamma (w + (μ + (k : ℂ)) / (n : ℂ)) := by
    intro k _
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm] at h
  linear_combination -h

end

end GaloisForLFunctions.HTGeometry
