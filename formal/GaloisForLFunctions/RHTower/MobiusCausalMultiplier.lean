import GaloisForLFunctions.RHTower.InvZetaCriticalLaurent
import GaloisForLFunctions.RHTower.GammaDampedLaurentAtOne

/-!
# The coupled causal multiplier and its removable singularity

The Laplace transform of the coupled floor--Möbius causal source is

```text
M_ω(z) = ζ(1+z)/[(1+ω+z) ζ(1+2ω+z)] - 1/[(1+ω) z ζ(1+2ω)] .
```

Subtracting the pole of `ζ` in the completed normalisation, `ζ(1+z) = A(1+z) + 1/(z Γℝ(1+z))`,
splits it as

```text
M_ω(z) = A(1+z)/[(1+ω+z) ζ(1+2ω+z)] + G_ω(z)/z ,
G_ω(z) = 1/[Γℝ(1+z)(1+ω+z) ζ(1+2ω+z)] - 1/[(1+ω) ζ(1+2ω)] ,
```

where the gap `G_ω` vanishes at `z = 0` because `Γℝ(1) = 1`.  This is the exact form in which the
apparent singularity of `M_ω` at the origin is removable.
-/

namespace RHTower

noncomputable section

/-- The coupled causal multiplier. -/
def mobiusCausalMultiplier (ω : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) -
    1 / ((1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)))

/-- The pole gap of the coupled causal multiplier. -/
def mobiusCausalGap (ω : ℝ) (z : ℂ) : ℂ :=
  1 / (Complex.Gammaℝ (1 + z) * (1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) -
    1 / ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ)))

theorem mobiusCausalGap_zero (ω : ℝ) : mobiusCausalGap ω 0 = 0 := by
  rw [mobiusCausalGap]
  norm_num [Complex.Gammaℝ_one]

/-! ### The nonvanishing side conditions -/

theorem riemannZeta_one_add_two_mul_add_ne_zero {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    riemannZeta (1 + 2 * (ω : ℂ) + z) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
  linarith

theorem riemannZeta_one_add_two_mul_ne_zero {ω : ℝ} (hω : 0 < ω) :
    riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := by
  have h := riemannZeta_one_add_two_mul_add_ne_zero hω (z := 0) (by simp)
  simpa using h

theorem one_add_ofReal_add_ne_zero {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    (1 : ℂ) + (ω : ℂ) + z ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + (ω : ℂ) + z).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith

theorem gammaR_one_add_ne_zero {z : ℂ} (hz : 0 ≤ z.re) : Complex.Gammaℝ (1 + z) ≠ 0 := by
  refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-! ### The pole-subtracted form -/

/-- **The removable-singularity form of the coupled causal multiplier.** -/
theorem mobiusCausalMultiplier_eq {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    mobiusCausalMultiplier ω z
      = zetaPoleFree (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) +
        mobiusCausalGap ω z / z := by
  have hζ := riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hΓ := gammaR_one_add_ne_zero hz
  have hω0 : (1 : ℂ) + (ω : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (ω : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
    linarith
  have hzeta : riemannZeta (1 + z)
      = zetaPoleFree (1 + z) + 1 / z / Complex.Gammaℝ (1 + z) := by
    rw [zetaPoleFree]
    have : (1 : ℂ) + z - 1 = z := by ring
    rw [this]
    ring
  rw [mobiusCausalMultiplier, mobiusCausalGap, hzeta]
  field_simp
  ring

end

end RHTower
