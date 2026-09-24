import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv

/-!
# The exact sign law of a line-conjugate Hadamard pair

The partial fraction of the completed zeta pairs each zero `ρ` with its line conjugate
`1 - conj ρ`, which cancels the Hadamard constants.  In centred coordinates
`x = Re s - 1/2`, `δ = Re ρ - 1/2`, `y = Im s - Im ρ` the pair's resolvent real part is exactly

```text
2 x (x² - δ² + y²) / (((x-δ)² + y²) ((x+δ)² + y²)) ,
```

so for `x > 0` it is positive exactly outside the disk `δ² = x² + y²` and negative exactly inside
it.  Since every zero satisfies `δ² < 1/4`, the pair is unconditionally positive whenever
`x² + y² ≥ 1/4`: only zeros at nearby heights can contribute negatively.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact real-part formula for a line-conjugate resolvent pair. -/
theorem hadamardPair_re_formula {x δ y : ℝ}
    (h1 : (x - δ) ^ 2 + y ^ 2 ≠ 0) (h2 : (x + δ) ^ 2 + y ^ 2 ≠ 0) :
    (x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2) =
      2 * x * (x ^ 2 - δ ^ 2 + y ^ 2) /
        (((x - δ) ^ 2 + y ^ 2) * ((x + δ) ^ 2 + y ^ 2)) := by
  field_simp
  ring

/-- **The line-conjugate pair is positive exactly outside the off-line disk.** -/
theorem hadamardPair_re_pos {x δ y : ℝ} (hx : 0 < x)
    (h1 : (x - δ) ^ 2 + y ^ 2 ≠ 0) (h2 : (x + δ) ^ 2 + y ^ 2 ≠ 0)
    (hdisk : δ ^ 2 < x ^ 2 + y ^ 2) :
    0 < (x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2) := by
  rw [hadamardPair_re_formula h1 h2]
  have hp1 : 0 < (x - δ) ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h1)
  have hp2 : 0 < (x + δ) ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h2)
  have hnum : 0 < 2 * x * (x ^ 2 - δ ^ 2 + y ^ 2) := by nlinarith
  positivity

/-- **The line-conjugate pair is negative exactly inside the off-line disk.** -/
theorem hadamardPair_re_neg {x δ y : ℝ} (hx : 0 < x)
    (h1 : (x - δ) ^ 2 + y ^ 2 ≠ 0) (h2 : (x + δ) ^ 2 + y ^ 2 ≠ 0)
    (hdisk : x ^ 2 + y ^ 2 < δ ^ 2) :
    (x - δ) / ((x - δ) ^ 2 + y ^ 2) + (x + δ) / ((x + δ) ^ 2 + y ^ 2) < 0 := by
  rw [hadamardPair_re_formula h1 h2]
  have hp1 : 0 < (x - δ) ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h1)
  have hp2 : 0 < (x + δ) ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h2)
  have hnum : 2 * x * (x ^ 2 - δ ^ 2 + y ^ 2) < 0 := by nlinarith
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-- Centred form of the resolvent real part at a zero. -/
theorem re_inv_sub_eq (s ρ : ℂ) :
    ((s - ρ)⁻¹).re =
      ((s.re - 1 / 2) - (ρ.re - 1 / 2)) /
        (((s.re - 1 / 2) - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- Centred form of the resolvent real part at the line-conjugate zero. -/
theorem re_inv_sub_lineConj_eq (s ρ : ℂ) :
    ((s - (1 - (starRingEnd ℂ) ρ))⁻¹).re =
      ((s.re - 1 / 2) + (ρ.re - 1 / 2)) /
        (((s.re - 1 / 2) + (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring_nf

/-- **Exact sign law for a line-conjugate zero pair of the completed zeta.**  With centred
coordinates `x = Re s - 1/2`, `δ = Re ρ - 1/2`, `y = Im s - Im ρ`, the pair's resolvent real part
is `2x(x² - δ² + y²)` over a positive denominator: positive exactly outside the disk
`δ² = x² + y²`, negative exactly inside it. -/
theorem re_inv_add_re_inv_lineConj (s ρ : ℂ) (h1 : s - ρ ≠ 0)
    (h2 : s - (1 - (starRingEnd ℂ) ρ) ≠ 0) :
    ((s - ρ)⁻¹).re + ((s - (1 - (starRingEnd ℂ) ρ))⁻¹).re =
      2 * (s.re - 1 / 2) *
          ((s.re - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2) /
        ((((s.re - 1 / 2) - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) *
          (((s.re - 1 / 2) + (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2)) := by
  have hn1 : (((s.re - 1 / 2) - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h1
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im] at this
    intro hz
    nlinarith [this]
  have hn2 : (((s.re - 1 / 2) + (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h2
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im] at this
    intro hz
    nlinarith [this]
  rw [re_inv_sub_eq, re_inv_sub_lineConj_eq, hadamardPair_re_formula hn1 hn2]

theorem re_inv_add_re_inv_lineConj_pos {s ρ : ℂ} (h1 : s - ρ ≠ 0)
    (h2 : s - (1 - (starRingEnd ℂ) ρ) ≠ 0) (hx : 1 / 2 < s.re)
    (hdisk : (ρ.re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2) :
    0 < ((s - ρ)⁻¹).re + ((s - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
  rw [re_inv_sub_eq, re_inv_sub_lineConj_eq]
  have hn1 : (((s.re - 1 / 2) - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h1
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im] at this
    intro hz; nlinarith [this]
  have hn2 : (((s.re - 1 / 2) + (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h2
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im] at this
    intro hz; nlinarith [this]
  exact hadamardPair_re_pos (by linarith) hn1 hn2 hdisk

theorem re_inv_add_re_inv_lineConj_neg {s ρ : ℂ} (h1 : s - ρ ≠ 0)
    (h2 : s - (1 - (starRingEnd ℂ) ρ) ≠ 0) (hx : 1 / 2 < s.re)
    (hdisk : (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 < (ρ.re - 1 / 2) ^ 2) :
    ((s - ρ)⁻¹).re + ((s - (1 - (starRingEnd ℂ) ρ))⁻¹).re < 0 := by
  rw [re_inv_sub_eq, re_inv_sub_lineConj_eq]
  have hn1 : (((s.re - 1 / 2) - (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h1
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im] at this
    intro hz; nlinarith [this]
  have hn2 : (((s.re - 1 / 2) + (ρ.re - 1 / 2)) ^ 2 + (s.im - ρ.im) ^ 2) ≠ 0 := by
    have := Complex.normSq_pos.mpr h2
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im] at this
    intro hz; nlinarith [this]
  exact hadamardPair_re_neg (by linarith) hn1 hn2 hdisk

/-- **Unconditional positivity away from the zero's height.**  Every completed-zeta zero lies in
the open critical strip, so `(Re ρ - 1/2)^2 < 1/4`; hence a line-conjugate pair contributes
positively whenever `s` is at squared distance at least `1/4` from the critical-line point at the
zero's height.  Only zeros at nearby heights can contribute negatively, and by the displayed disk
they do so exactly when `(Re ρ - 1/2)^2` exceeds that squared distance. -/
theorem re_inv_add_re_inv_lineConj_pos_of_far {s ρ : ℂ} (h1 : s - ρ ≠ 0)
    (h2 : s - (1 - (starRingEnd ℂ) ρ) ≠ 0) (hx : 1 / 2 < s.re)
    (hstrip : (ρ.re - 1 / 2) ^ 2 < 1 / 4)
    (hfar : 1 / 4 ≤ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2) :
    0 < ((s - ρ)⁻¹).re + ((s - (1 - (starRingEnd ℂ) ρ))⁻¹).re :=
  re_inv_add_re_inv_lineConj_pos h1 h2 hx (by linarith)

end

end RHTower
