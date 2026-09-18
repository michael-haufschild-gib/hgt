import Mathlib.NumberTheory.Modular

/-!
# The horoball bound on the standard fundamental domain

For `z` in the closed fundamental domain `𝒟 = {1 ≤ |z|², |Re z| ≤ 1/2}` and `γ ∈ SL(2, ℤ)` with
lower-left entry `c ≠ 0`, the image `γ z` has imaginary part at most `1`:
`Im(γ z) = y / |cz + d|² ≤ 1`.  Equivalently `y ≤ (cy)² + (cx + d)²`.  Hence for `Y ≥ 1` the only
elements of `Γ_∞ \ Γ` moving a point of `𝒟` above height `Y` are the translations themselves.

The elementary inequality splits by the integer `c`: for `|c| ≥ 2`, `(cy)² ≥ 4y² ≥ y` since
`y ≥ √3/2`; for `|c| = 1` and `d = 0`, `y ≤ x² + y²`; for `|c| = 1` and `|d| ≥ 1`,
`(cx + d)² ≥ 1/4` and `y ≤ y² + 1/4`.
-/

open UpperHalfPlane Complex
open scoped MatrixGroups

namespace RHTower

/-- The real inequality behind the horoball bound. -/
theorem horoball_aux {x y c d : ℝ} (hy : 0 < y) (h1 : 1 ≤ x ^ 2 + y ^ 2) (hx : |x| ≤ 1 / 2)
    (hc : 4 ≤ c ^ 2 ∨ (c ^ 2 = 1 ∧ (d = 0 ∨ 1 ≤ d ^ 2))) :
    y ≤ (c * y) ^ 2 + (c * x + d) ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h := abs_le.mp hx
    nlinarith [h.1, h.2]
  have hy2 : 3 / 4 ≤ y ^ 2 := by linarith
  rcases hc with hc | ⟨hc1, hd⟩
  · have hy14 : 1 / 4 ≤ y := by nlinarith
    have h4 : 4 * y ^ 2 ≤ (c * y) ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg y]
    nlinarith [sq_nonneg (c * x + d)]
  · have hcabs : c = 1 ∨ c = -1 := by
      have h : (c - 1) * (c + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hd with rfl | hd
    · have hsq : (c * x + 0) ^ 2 = x ^ 2 := by
        rcases hcabs with rfl | rfl <;> ring
      have hcy : (c * y) ^ 2 = y ^ 2 := by
        rcases hcabs with rfl | rfl <;> ring
      rw [hsq, hcy]
      rcases le_or_gt y 1 with hy1 | hy1
      · nlinarith
      · nlinarith
    · have hdabs : 1 ≤ |d| := by
        have h : 1 ≤ |d| ^ 2 := by rw [sq_abs]; exact hd
        nlinarith [abs_nonneg d]
      have hcx : |c * x| ≤ 1 / 2 := by
        rw [abs_mul]
        have hc1' : |c| = 1 := by rcases hcabs with rfl | rfl <;> simp
        rw [hc1', one_mul]
        exact hx
      have habs : 1 / 2 ≤ |c * x + d| := by
        have := abs_add_le (c * x + d) (-(c * x))
        rw [abs_neg] at this
        have h' : |d| ≤ |c * x + d| + |c * x| := by
          calc |d| = |c * x + d + -(c * x)| := by ring_nf
            _ ≤ |c * x + d| + |c * x| := this
        linarith
      have hsq : 1 / 4 ≤ (c * x + d) ^ 2 := by
        have h : (1 / 2 : ℝ) ^ 2 ≤ |c * x + d| ^ 2 :=
          pow_le_pow_left₀ (by norm_num) habs 2
        rw [sq_abs] at h
        linarith
      have hcy : (c * y) ^ 2 = y ^ 2 := by
        rcases hcabs with rfl | rfl <;> ring
      rw [hcy]
      nlinarith [sq_nonneg (y - 1 / 2)]

/-- The integer dichotomy feeding `horoball_aux`. -/
theorem horoball_int_cases {c d : ℤ} (hc : c ≠ 0) :
    4 ≤ (c : ℝ) ^ 2 ∨ ((c : ℝ) ^ 2 = 1 ∧ ((d : ℝ) = 0 ∨ 1 ≤ (d : ℝ) ^ 2)) := by
  have hc1 : 1 ≤ c ∨ c ≤ -1 := by omega
  by_cases h4 : 4 ≤ c ^ 2
  · left
    exact_mod_cast h4
  · right
    have hcsq : c ^ 2 = 1 := by
      have h1 : 1 ≤ c ^ 2 := by rcases hc1 with h | h <;> nlinarith
      have h2 : c ^ 2 < 4 := by omega
      have h3 : c ≤ 1 := by nlinarith
      have h4' : -1 ≤ c := by nlinarith
      rcases hc1 with h | h <;> nlinarith
    refine ⟨by exact_mod_cast hcsq, ?_⟩
    by_cases hd : d = 0
    · left
      exact_mod_cast hd
    · right
      have hd1 : 1 ≤ d ∨ d ≤ -1 := by omega
      have : 1 ≤ d ^ 2 := by rcases hd1 with h | h <;> nlinarith
      exact_mod_cast this

/-- `|cz + d|² = (cy)² + (cx + d)²`. -/
theorem normSq_int_mul_add (c d : ℤ) (z : ℍ) :
    Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) =
      ((c : ℝ) * z.im) ^ 2 + ((c : ℝ) * z.re + (d : ℝ)) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- **Horoball bound**: on `𝒟`, `y ≤ |cz + d|²` for every integer pair with `c ≠ 0`. -/
theorem im_le_normSq_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) {c d : ℤ} (hc : c ≠ 0) :
    z.im ≤ Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
  rw [normSq_int_mul_add]
  have h1 : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz.1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith
  exact horoball_aux z.im_pos h1 hz.2 (horoball_int_cases hc)

/-- The image of a point of `𝒟` under a non-translation has imaginary part at most `1`. -/
theorem im_div_normSq_le_one_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) {c d : ℤ}
    (hc : c ≠ 0) :
    z.im / Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) ≤ 1 := by
  have hpos : 0 < Complex.normSq ((c : ℂ) * (z : ℂ) + (d : ℂ)) := by
    rw [normSq_int_mul_add]
    have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    positivity
  rw [div_le_one hpos]
  exact im_le_normSq_of_mem_fd hz hc

/-- The denominator of the Möbius action of `g ∈ SL(2, ℤ)` is `c z + d`. -/
theorem denom_SL2Z (g : SL(2, ℤ)) (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)) (z : ℂ) =
      ((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL]

/-- **Horoball bound** for the modular action: `Im(g z) ≤ 1` on `𝒟` when `g` is not a translation. -/
theorem im_smul_le_one_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) {g : SL(2, ℤ)}
    (hg : g 1 0 ≠ 0) : (g • z).im ≤ 1 := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_SL2Z]
  exact im_div_normSq_le_one_of_mem_fd hz hg

end RHTower
