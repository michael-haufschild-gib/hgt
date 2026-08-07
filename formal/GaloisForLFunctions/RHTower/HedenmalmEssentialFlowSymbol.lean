import GaloisForLFunctions.RHTower.HedenmalmTwoPrimeNormalFrame

/-!
# The essential inverse-flow symbol and the fixed-width Weil sample

In the compact reciprocal coordinate `μ = -1/z` of the source-derived inverse the fixed-width
tomography symbol is

`Φ_{a,L}(μ) = 2μ (sin(a/μ) - sin((a-L)/μ))`,

with an essential singularity at the compact spectral boundary `μ = 0`.  On a root block it
reproduces the fixed-width Xi--Weil sample

`F_{a,L}(w) = e^{aw} A_L(w) + e^{-aw} A_L(-w)`,  `A_L(w) = (1 - e^{-Lw})/w`,

at the corresponding spectral parameter `w = i z`.
-/

open Filter Topology

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

/-- The fixed-width tomography symbol in the compact reciprocal coordinate. -/
def essentialFlowSymbol (a L : ℝ) (μ : ℂ) : ℂ :=
  2 * μ * (Complex.sin (((a : ℝ) : ℂ) / μ) - Complex.sin ((((a - L : ℝ)) : ℂ) / μ))

/-- The fixed-width amplitude `A_L(w) = (1 - e^{-Lw})/w`. -/
def weilWidthAmplitude (L : ℝ) (w : ℂ) : ℂ := (1 - Complex.exp (-((L : ℝ) : ℂ) * w)) / w

/-- The fixed-width Weil sample `F_{a,L}(w) = e^{aw} A_L(w) + e^{-aw} A_L(-w)`. -/
def weilFixedWidthSample (a L : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (((a : ℝ) : ℂ) * w) * weilWidthAmplitude L w
    + Complex.exp (-(((a : ℝ) : ℂ) * w)) * weilWidthAmplitude L (-w)

/-- The common closed form of both sides on a root block. -/
def rootBlockForm (a L : ℝ) (z : ℂ) : ℂ :=
  Complex.I * z⁻¹ * (Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z)))
      - Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z))
      - Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z)))
      + Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)))

theorem essentialFlowSymbol_eq_rootBlockForm (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    essentialFlowSymbol a L (-z⁻¹) = rootBlockForm a L z := by
  have harg1 : ((a : ℝ) : ℂ) / (-z⁻¹) = -(((a : ℝ) : ℂ) * z) := by field_simp
  have harg2 : (((a - L : ℝ)) : ℂ) / (-z⁻¹) = -((((a - L : ℝ)) : ℂ) * z) := by field_simp
  have hs1 : Complex.exp ((-(((a : ℝ) : ℂ) * z)) * Complex.I)
      = Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z))) := by
    congr 1
    ring
  have hs2 : Complex.exp ((((a : ℝ) : ℂ) * z) * Complex.I)
      = Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z)) := by
    congr 1
    ring
  have hs3 : Complex.exp ((-((((a - L : ℝ)) : ℂ) * z)) * Complex.I)
      = Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z))) := by
    congr 1
    ring
  have hs4 : Complex.exp (((((a - L : ℝ)) : ℂ) * z) * Complex.I)
      = Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)) := by
    congr 1
    ring
  rw [essentialFlowSymbol, harg1, harg2, Complex.sin_neg, Complex.sin_neg,
    Complex.sin, Complex.sin, hs1, hs2, hs3, hs4, rootBlockForm]
  field_simp
  ring

theorem weilFixedWidthSample_eq_rootBlockForm (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    weilFixedWidthSample a L (Complex.I * z) = rootBlockForm a L z := by
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero hIne hz
  have hinv : (Complex.I * z)⁻¹ = -Complex.I * z⁻¹ := by
    rw [mul_inv, Complex.inv_I]
  have hinv' : (-(Complex.I * z))⁻¹ = Complex.I * z⁻¹ := by
    rw [inv_neg, hinv]
    ring
  have hUX : Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z))
        * Complex.exp (-((L : ℝ) : ℂ) * (Complex.I * z))
      = Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hVY : Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z)))
        * Complex.exp (-((L : ℝ) : ℂ) * -(Complex.I * z))
      = Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [weilFixedWidthSample, weilWidthAmplitude, weilWidthAmplitude, rootBlockForm,
    ← hUX, ← hVY, div_eq_mul_inv, div_eq_mul_inv, hinv, hinv']
  ring

/-- **The tomography symbol reproduces the fixed-width Weil sample on every root block.** -/
theorem essentialFlowSymbol_root (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    essentialFlowSymbol a L (-z⁻¹) = weilFixedWidthSample a L (Complex.I * z) := by
  rw [essentialFlowSymbol_eq_rootBlockForm a L hz, weilFixedWidthSample_eq_rootBlockForm a L hz]

end HedenmalmThetaSource

end

end RHTower
