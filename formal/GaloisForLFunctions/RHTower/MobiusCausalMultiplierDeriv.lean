import GaloisForLFunctions.RHTower.MobiusCausalMultiplier

/-!
# The parameter derivative of the coupled causal multiplier

For `ω > 0` the coupled causal multiplier is differentiable in the parameter, with

```text
∂_ω M_ω(z)
  = ζ(1+z)/[(1+ω+z)ζ(1+2ω+z)] · [ -1/(1+ω+z) - 2 ζ'(1+2ω+z)/ζ(1+2ω+z) ]
    + (1/z) · [ ζ(1+2ω) + 2(1+ω)ζ'(1+2ω) ] / [ (1+ω) ζ(1+2ω) ]² ,
```

which is the card's `(5)`--`(6)`.
-/

namespace RHTower

noncomputable section

/-- The parameter derivative of the coupled causal multiplier, in the card's form. -/
def mobiusCausalMultiplierDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) *
      (-(1 / (1 + (ω : ℂ) + z)) -
        2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z))
    + 1 / z * ((riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2)

theorem one_add_two_mul_add_ne_one {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    (1 : ℂ) + 2 * (ω : ℂ) + z ≠ 1 := by
  intro h
  have hre : ((1 : ℂ) + 2 * (ω : ℂ) + z).re = (1 : ℂ).re := by rw [h]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hre
  linarith

theorem hasDerivAt_linear_shift (c : ℂ) (z : ℂ) (ω : ℝ) :
    HasDerivAt (fun w : ℝ => 1 + c * (w : ℂ) + z) c ω := by
  have h : HasDerivAt (fun w : ℝ => ((w : ℝ) : ℂ)) 1 ω := Complex.ofRealCLM.hasDerivAt
  simpa using ((h.const_mul c).const_add (1 : ℂ)).add_const z

theorem hasDerivAt_zeta_shift {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    HasDerivAt (fun w : ℝ => riemannZeta (1 + 2 * (w : ℂ) + z))
      (2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z)) ω := by
  have hlin := hasDerivAt_linear_shift 2 z ω
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (1 + 2 * (ω : ℂ) + z))
      (1 + 2 * (ω : ℂ) + z) :=
    (differentiableAt_riemannZeta (one_add_two_mul_add_ne_one hω hz)).hasDerivAt
  have h := hζ.scomp ω hlin
  simpa [Function.comp, smul_eq_mul] using h

/-- **The card's `(5)`--`(6)`: the parameter derivative of `M_ω`.** -/
theorem hasDerivAt_mobiusCausalMultiplier {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re)
    (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℝ => mobiusCausalMultiplier w z) (mobiusCausalMultiplierDeriv ω z) ω := by
  have hζ := riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hω0 : (1 : ℂ) + (ω : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (ω : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
    linarith
  have hlin1 : HasDerivAt (fun w : ℝ => 1 + (w : ℂ) + z) 1 ω := by
    simpa using hasDerivAt_linear_shift 1 z ω
  have hD1 := hlin1.mul (hasDerivAt_zeta_shift hω hz)
  have hD1ne : (1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z) ≠ 0 :=
    mul_ne_zero hlin hζ
  have hT1 := (hasDerivAt_const ω (riemannZeta (1 + z))).div hD1 hD1ne
  have hzeta0 : HasDerivAt (fun w : ℝ => riemannZeta (1 + 2 * (w : ℂ)))
      (2 * deriv riemannZeta (1 + 2 * (ω : ℂ))) ω := by
    have h := hasDerivAt_zeta_shift (z := 0) hω (by simp)
    simpa using h
  have hlin2 : HasDerivAt (fun w : ℝ => (1 + (w : ℂ)) * z) (1 * z) ω := by
    have h : HasDerivAt (fun w : ℝ => ((w : ℝ) : ℂ)) 1 ω := Complex.ofRealCLM.hasDerivAt
    simpa using (h.const_add (1 : ℂ)).mul_const z
  have hD2 := hlin2.mul hzeta0
  have hD2ne : (1 + (ω : ℂ)) * z * riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hω0 hz0) hζ0
  have hT2 := (hasDerivAt_const ω (1 : ℂ)).div hD2 hD2ne
  have hsub := hT1.sub hT2
  have hζ' : riemannZeta (1 + (ω : ℂ) * 2 + z) ≠ 0 := by
    have hrw : (1 : ℂ) + (ω : ℂ) * 2 + z = 1 + 2 * (ω : ℂ) + z := by ring
    rw [hrw]
    exact hζ
  have hζ0' : riemannZeta (1 + (ω : ℂ) * 2) ≠ 0 := by
    have hrw : (1 : ℂ) + (ω : ℂ) * 2 = 1 + 2 * (ω : ℂ) := by ring
    rw [hrw]
    exact hζ0
  refine hsub.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [mobiusCausalMultiplierDeriv]
  field_simp
  ring

end

end RHTower
