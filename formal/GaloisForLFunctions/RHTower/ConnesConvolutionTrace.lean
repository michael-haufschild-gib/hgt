import GaloisForLFunctions.RHTower.ConnesConvolutionKernelField

/-!
# The trace of a product of convolution cut-off operators

§V (21)+(23) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Both operators occurring in the cut-off `R_Λ = P̂_Λ P_Λ` are of the form "multiply by `a`, after
convolving with a fixed `L²` function".  For that class the trace identity of
`ConnesKernelTracePairing` evaluates in closed form: translation preserves the inner product of
`L²(ℝ)`, so the fibre pairing is constant in `x` and

  `Trace(T_a,c^† ∘ T_b,d) = ⟪d, c⟫ · ∫ b(x) conj(a(x)) dx`,

which is exactly Connes' `∫∫ k(x,y) r^t(x,y) dx dy` for two convolution kernels.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance factOneLeTwoConvTrace : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance factTwoNeTopConvTrace : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- Translation preserves the inner product of `L²(ℝ)`. -/
theorem inner_connesL2Translate (x : ℝ) (c d : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (connesL2Translate x d) (connesL2Translate x c) : ℂ) = inner ℂ d c := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => (inner ℂ ((d : ℝ → ℂ) y) ((c : ℝ → ℂ) y) : ℂ)) x
  rw [← hshift]
  refine integral_congr_ae ?_
  filter_upwards [connesL2Translate_ae x c, connesL2Translate_ae x d] with y h1 h2
  rw [h1, h2]

/-- The Riesz vector of the convolution field. -/
theorem toDual_symm_connesConvField (a : ℝ → ℂ) (c : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).symm (connesConvField a c x)
      = (starRingEnd ℂ) (a x) • connesL2Translate x c := by
  have hforward : (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      ((starRingEnd ℂ) (a x) • connesL2Translate x c) = connesConvField a c x := by
    rw [connesConvField, map_smulₛₗ]
    simp
  rw [← hforward, LinearIsometryEquiv.symm_apply_apply]

/-- **§V (21)+(23) in closed form.**  The trace of the product of two convolution cut-off kernel
operators is the inner product of the two convolution profiles times the pairing of the two
multiplier profiles. -/
theorem connes_trace_convKernel {a b : ℝ → ℂ} (ha : MemLp a 2 (volume : Measure ℝ))
    (hb : MemLp b 2 (volume : Measure ℝ)) (c d : Lp ℂ 2 (volume : Measure ℝ)) :
    ContinuousLinearMap.opTrace
        ((ContinuousLinearMap.adjoint
            (connesKernelOperator (volume : Measure ℝ) (connesConvKernel ha c))) ∘L
          (connesKernelOperator (volume : Measure ℝ) (connesConvKernel hb d)))
      = (inner ℂ d c : ℂ) * ∫ x : ℝ, b x * (starRingEnd ℂ) (a x) := by
  rw [connes_opTrace_adjoint_kernel (volume : Measure ℝ) (connesConvKernel ha c)
    (connesConvKernel hb d)]
  have hpt : ∀ᵐ x ∂(volume : Measure ℝ),
      (inner ℂ ((InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).symm
          ((connesConvKernel hb d : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x))
        ((InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).symm
          ((connesConvKernel ha c : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x)) : ℂ)
      = (b x * (starRingEnd ℂ) (a x)) * (inner ℂ d c : ℂ) := by
    filter_upwards [(memLp_connesConvField ha c).coeFn_toLp,
      (memLp_connesConvField hb d).coeFn_toLp] with x hxa hxb
    rw [show (connesConvKernel ha c : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x
        = connesConvField a c x from hxa,
      show (connesConvKernel hb d : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x
        = connesConvField b d x from hxb,
      toDual_symm_connesConvField, toDual_symm_connesConvField,
      inner_smul_left, inner_smul_right, inner_connesL2Translate]
    simp
    ring
  rw [integral_congr_ae hpt, integral_mul_const, mul_comm]

end

end GaloisForLFunctions.RHTower
