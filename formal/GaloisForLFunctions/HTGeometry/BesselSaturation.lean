import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

/-!
# Saturated Bessel inequality

An orthonormal family that recovers the full norm of one vector already sees everything that vector
can pair with: `x` is orthogonal to every vector the family annihilates.  This replaces the usual
orthogonal-projection argument for showing that a vector lies in the closed span of an orthonormal
family, and needs nothing beyond Bessel's inequality.

Applying Bessel to `x + c y`, where `y` is annihilated by the family, leaves the left side
unchanged, so the right side cannot have shrunk.  Choosing the phase of `c` against `⟪x, y⟫` and
letting its modulus go to zero forces `⟪x, y⟫ = 0`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- **Parseval for one vector forces orthogonality to the complement.**  If an orthonormal family
recovers the full norm of `x`, then `x` is orthogonal to everything the family annihilates.  The
proof is Bessel's inequality applied to `x + c y` with the phase of `c` aligned against
`⟪x, y⟫`. -/
theorem inner_eq_zero_of_bessel_saturates {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {v : ι → E} (hv : Orthonormal ℂ v) {x y : E}
    (hx : HasSum (fun i => ‖(inner ℂ (v i) x : ℂ)‖ ^ 2) (‖x‖ ^ 2))
    (hy : ∀ i, (inner ℂ (v i) y : ℂ) = 0) :
    (inner ℂ x y : ℂ) = 0 := by
  set A : ℂ := (inner ℂ x y : ℂ) with hA
  by_contra hne
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hne
  have hkey : ∀ t : ℝ, 0 < t → 2 * t * ‖A‖ ≤ t ^ 2 * ‖y‖ ^ 2 := by
    intro t ht
    set c : ℂ := (-t : ℂ) * (starRingEnd ℂ) A / ((‖A‖ : ℝ) : ℂ) with hc
    have hshift : ∀ i, (inner ℂ (v i) (x + c • y) : ℂ) = (inner ℂ (v i) x : ℂ) := by
      intro i
      rw [inner_add_right, inner_smul_right, hy i, mul_zero, add_zero]
    have hbessel := hv.tsum_inner_products_le (𝕜 := ℂ) (x + c • y)
    have hsum : (∑' i, ‖(inner ℂ (v i) (x + c • y) : ℂ)‖ ^ 2) = ‖x‖ ^ 2 := by
      rw [show (fun i => ‖(inner ℂ (v i) (x + c • y) : ℂ)‖ ^ 2)
          = fun i => ‖(inner ℂ (v i) x : ℂ)‖ ^ 2 from funext fun i => by rw [hshift i]]
      exact hx.tsum_eq
    rw [hsum] at hbessel
    have hexp : ‖x + c • y‖ ^ 2
        = ‖x‖ ^ 2 + 2 * (inner ℂ x (c • y) : ℂ).re + ‖c • y‖ ^ 2 := by
      rw [@norm_add_sq ℂ]
      rfl
    have hinner : (inner ℂ x (c • y) : ℂ) = c * A := by
      rw [inner_smul_right, hA]
    have hcA : (c * A).re = -(t * ‖A‖) := by
      rw [hc]
      have h1 : (starRingEnd ℂ) A * A = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hAne : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by
        simpa using ne_of_gt hApos
      rw [div_mul_eq_mul_div, mul_assoc, h1]
      rw [show ((-t : ℂ) * ((‖A‖ ^ 2 : ℝ) : ℂ) / ((‖A‖ : ℝ) : ℂ))
          = ((-(t * ‖A‖) : ℝ) : ℂ) by
        push_cast
        field_simp]
      simp
    have hcnorm : ‖c • y‖ ^ 2 = t ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_smul, mul_pow]
      congr 1
      rw [hc, norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hApos]
      rw [show ‖(-t : ℂ)‖ = t by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]]
      rw [mul_div_assoc, div_self (ne_of_gt hApos), mul_one]
    rw [hexp, hinner, hcA, hcnorm] at hbessel
    linarith
  have hkey' : ∀ t : ℝ, 0 < t → 2 * ‖A‖ ≤ t * ‖y‖ ^ 2 := by
    intro t ht
    have h := hkey t ht
    nlinarith
  have hden : (0 : ℝ) < ‖y‖ ^ 2 + 1 := by positivity
  have h2 := hkey' (‖A‖ / (‖y‖ ^ 2 + 1)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at h2
  have hy2 : (0 : ℝ) ≤ ‖y‖ ^ 2 := by positivity
  nlinarith

end GaloisForLFunctions.HTGeometry
