import Mathlib
import GaloisForLFunctions.RHTower.RectangularWindowAmplitudeAnalytic

/-!
# The rectangular-window and tent Mellin factors

The elementary Mellin/Laplace factors of the prime-polar moving-tent tomography
(`prime-polar-moving-tent-divisor-tomography`, §2).  After the substitution `w = s − 1`, `u = eˣ`, the
box (rectangular-window) factor is the geometric integral

`A_L(w) = ∫₀ᴸ e^{-wx} dx = (1 − e^{-wL}) / w`,

with removable value `L` at `w = 0`, and the tent factor is its square `I_L(w) = A_L(w)²` (the tent
being the additive self-convolution of the box).  These are entire in `s` and supply the exact
`(1 − e^{-Lw})²/w²` shape of the completed window transform.
-/

open scoped Real
open intervalIntegral

namespace RHTower

/-- The primitive integral `∫ₐᵇ x e^{cx} dx = [(cx−1)e^{cx}/c²]ₐᵇ` (`c ≠ 0`), absent from mathlib. -/
theorem integral_id_mul_cexp (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, (x : ℂ) * Complex.exp (c * (x : ℂ)))
      = ((c * b - 1) * Complex.exp (c * b)) / c ^ 2
        - ((c * a - 1) * Complex.exp (c * a)) / c ^ 2 := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun t : ℝ => ((c * (t : ℂ) - 1) * Complex.exp (c * (t : ℂ))) / c ^ 2)
      ((x : ℂ) * Complex.exp (c * (x : ℂ))) x := by
    intro x
    have hx : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
        (Complex.exp (c * (x : ℂ)) * c) x := hx.cexp
    have hprod := (hx.sub_const (1 : ℂ)).mul hexp
    have hfin := hprod.div_const (c ^ 2)
    convert hfin using 1
    field_simp
    ring
  have hcont : Continuous (fun x : ℝ => (x : ℂ) * Complex.exp (c * (x : ℂ))) :=
    Complex.continuous_ofReal.mul ((Complex.continuous_ofReal.const_mul c).cexp)
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont.intervalIntegrable a b)]

/-- The tent (triangular) window of half-width `L`: `x` on `[0,L]`, `2L−x` on `[L,2L]`. -/
noncomputable def tentFn (L x : ℝ) : ℝ := if x ≤ L then x else 2 * L - x

/-- The box (rectangular-window) Laplace factor `A_L(w) = ∫₀ᴸ e^{-wx} dx`. -/
noncomputable def boxLaplace (L : ℝ) (w : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L, Complex.exp (-w * (x : ℂ))

/-- **Box Laplace factor, closed form.**  For `w ≠ 0`, `A_L(w) = (1 − e^{-wL}) / w`. -/
theorem boxLaplace_eq (L : ℝ) (w : ℂ) (hw : w ≠ 0) :
    boxLaplace L w = (1 - Complex.exp (-w * (L : ℂ))) / w := by
  rw [boxLaplace, integral_exp_mul_complex (neg_ne_zero.mpr hw)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **Removable value at `w = 0`.**  `A_L(0) = L`: the box factor extends continuously with value the
window length. -/
theorem boxLaplace_zero (L : ℝ) : boxLaplace L 0 = (L : ℂ) := by
  simp only [boxLaplace, neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    sub_zero]
  rw [Complex.real_smul, mul_one]

/-- **Tent Mellin factor `= box factor squared` (§2, eq. 10).**  The Laplace transform of the tent
window over `[0, 2L]` equals the square of the box factor: `∫₀²ᴸ τ_L(x) e^{-wx} dx = A_L(w)²`.  The
tent is `x` on `[0,L]` and `2L−x` on `[L,2L]`; splitting there and using `∫ e^{-wx}` and
`∫ x e^{-wx}` gives, after cancellation, `((1−e^{-wL})/w)²`. -/
theorem tentLaplace_eq_boxLaplace_sq (L : ℝ) (hL : 0 ≤ L) (w : ℂ) (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = (boxLaplace L w) ^ 2 := by
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have htcont : Continuous (fun x : ℝ => (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ))) := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_)
      ((Complex.continuous_ofReal.const_mul _).cexp)
    exact Continuous.if_le continuous_id (continuous_const.sub continuous_id) continuous_id
      continuous_const (fun x hx => by rw [hx]; ring)
  have h0L : (∫ x in (0 : ℝ)..L, (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = ∫ x in (0 : ℝ)..L, (x : ℂ) * Complex.exp (-w * (x : ℂ)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hL] at hx; simp [tentFn, hx.2]
  have hL2 : (∫ x in (L : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = ∫ x in (L : ℝ)..(2 * L),
          (((2 * L : ℝ) : ℂ) - (x : ℂ)) * Complex.exp (-w * (x : ℂ)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hx
    by_cases h : x ≤ L
    · have hxeq : x = L := le_antisymm h hx.1
      subst hxeq; simp only [tentFn, le_refl, if_true]; push_cast; ring
    · simp only [tentFn, if_neg h]; push_cast; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := L)
      (htcont.intervalIntegrable 0 L) (htcont.intervalIntegrable L (2 * L)), h0L, hL2]
  have hsub : (∫ x in (L : ℝ)..(2 * L), (((2 * L : ℝ) : ℂ) - (x : ℂ)) * Complex.exp (-w * (x : ℂ)))
      = ((2 * L : ℝ) : ℂ) * (∫ x in (L : ℝ)..(2 * L), Complex.exp (-w * (x : ℂ)))
        - ∫ x in (L : ℝ)..(2 * L), (x : ℂ) * Complex.exp (-w * (x : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    · exact (Complex.continuous_ofReal.const_mul _).cexp.const_mul _ |>.intervalIntegrable _ _
    · exact (Complex.continuous_ofReal.mul
        (Complex.continuous_ofReal.const_mul _).cexp).intervalIntegrable _ _
  rw [hsub, integral_id_mul_cexp (-w) hnw 0 L, integral_id_mul_cexp (-w) hnw L (2 * L),
    integral_exp_mul_complex hnw, boxLaplace_eq L w hw]
  have hE2 : Complex.exp (-w * ((2 * L : ℝ) : ℂ)) = Complex.exp (-w * (L : ℂ)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hE2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  push_cast
  field_simp
  ring

/-- The integral box factor coincides with the entire `rectangularWindowAmplitude` (the closed-form
`A_L` with its removable value at the origin). -/
theorem boxLaplace_eq_rectangularWindowAmplitude (L : ℝ) (w : ℂ) :
    boxLaplace L w = rectangularWindowAmplitude L w := by
  by_cases hw : w = 0
  · rw [hw, boxLaplace_zero, rectangularWindowAmplitude_zero]
  · rw [boxLaplace_eq L w hw, rectangularWindowAmplitude_eq_div hw,
      show (-w * (L : ℂ)) = (-(L : ℂ) * w) from by ring]

/-- **Tent Mellin factor `= A_L²` (eq. 11).**  Restating `(10)` with the entire closed-form amplitude:
`∫₀²ᴸ τ_L(x) e^{-wx} dx = A_L(w)²` where `A_L = rectangularWindowAmplitude`. -/
theorem tentLaplace_eq_rectangularWindowAmplitude_sq (L : ℝ) (hL : 0 ≤ L) (w : ℂ) (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = (rectangularWindowAmplitude L w) ^ 2 := by
  rw [tentLaplace_eq_boxLaplace_sq L hL w hw, boxLaplace_eq_rectangularWindowAmplitude]

/-- **The tent Mellin factor is entire** (§2, `I_L(s) = A_L(s−1)²` is entire in `s`).  As the square
of the shifted entire amplitude `A_L`, `s ↦ A_L(s−1)²` is holomorphic on all of `ℂ`. -/
theorem tentMellinFactor_differentiable (L : ℝ) :
    Differentiable ℂ (fun s : ℂ => (rectangularWindowAmplitude L (s - 1)) ^ 2) :=
  ((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).pow 2

end RHTower
