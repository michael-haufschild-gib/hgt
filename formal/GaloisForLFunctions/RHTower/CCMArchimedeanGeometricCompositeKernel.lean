import GaloisForLFunctions.RHTower.CCMArchimedeanGeometricCommutatorKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Distributional composite kernel of the CCM archimedean phase

Connes--Consani Lemma `sch3(iii)` writes the kernel of
`u∞* [P,u∞]` as the λ-composition of the kernels from parts (i) and (ii).  That inner
λ-integral is not generally a Bochner integral (on the diagonal it contains a non-decaying
cosine square).  This module gives the rigorous Schwartz-kernel meaning: the composite kernel is
the continuous operator pairing whose outer integral contains the two convergent kernel actions.
No illegal Fubini swap or value for a nonintegrable Lebesgue integral is used.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- Actual bounded operator corresponding to `(1/2 u∞* đu∞)ᵍ`. -/
def ccmArchimedeanGeometricComposite :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  star ccmArchimedeanGeometricScattering *
    ccmArchimedeanGeometricSharpCommutator

/-- Rigorous distributional pairing of the composite kernel on two dense Schwartz sources.
The ν- and μ-integrals are the convergent kernels from `sch3(i)` and `sch3(ii)`; their
outer `L²` pairing is the canonical order of integration. -/
def ccmArchimedeanGeometricCompositeKernelPairing
    (g h : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ lam : MellinL2.PosReal,
    inner ℂ
      (∫ nu : MellinL2.PosReal,
        ccmArchimedeanGeometricScatteringKernel lam nu *
          ccmMultiplicativeSchwartzSource g nu
            ∂MellinL2.multiplicativeHaar)
      (∫ mu : MellinL2.PosReal,
        (ccmGeometricSharpValue lam - ccmGeometricSharpValue mu) *
          ccmArchimedeanGeometricScatteringKernel lam mu *
            ccmMultiplicativeSchwartzSource h mu
              ∂MellinL2.multiplicativeHaar)
      ∂MellinL2.multiplicativeHaar

/-- Exact operator-to-distributional-kernel identity for Connes--Consani `sch3(iii)`. -/
theorem inner_ccmArchimedeanGeometricComposite_eq_kernelPairing
    (g h : SchwartzMap ℝ ℂ) :
    inner ℂ (ccmMultiplicativeSchwartzSource g)
        (ccmArchimedeanGeometricComposite (ccmMultiplicativeSchwartzSource h)) =
      ccmArchimedeanGeometricCompositeKernelPairing g h := by
  unfold ccmArchimedeanGeometricComposite
  change inner ℂ (ccmMultiplicativeSchwartzSource g)
      ((star ccmArchimedeanGeometricScattering)
        (ccmArchimedeanGeometricSharpCommutator
          (ccmMultiplicativeSchwartzSource h))) = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [MeasureTheory.L2.inner_def]
  unfold ccmArchimedeanGeometricCompositeKernelPairing
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanGeometricScattering_literal_kernel_formula g,
    ccmArchimedeanGeometricSharpCommutator_literal_kernel_formula h]
      with lam hg hh
  rw [hg, hh]

/-- Equivalent compact form using the two already-identified kernel actions. -/
theorem inner_ccmArchimedeanGeometricComposite_eq_kernelActions
    (g h : SchwartzMap ℝ ℂ) :
    inner ℂ (ccmMultiplicativeSchwartzSource g)
        (ccmArchimedeanGeometricComposite (ccmMultiplicativeSchwartzSource h)) =
      ∫ lam : MellinL2.PosReal,
        inner ℂ (ccmArchimedeanGeometricKernelAction g lam)
          (ccmArchimedeanGeometricSharpCommutatorKernelAction h lam)
            ∂MellinL2.multiplicativeHaar := by
  unfold ccmArchimedeanGeometricComposite
  change inner ℂ (ccmMultiplicativeSchwartzSource g)
      ((star ccmArchimedeanGeometricScattering)
        (ccmArchimedeanGeometricSharpCommutator
          (ccmMultiplicativeSchwartzSource h))) = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanGeometricScattering_has_literal_kernel g,
    ccmArchimedeanGeometricSharpCommutator_has_literal_kernel h]
      with lam hg hh
  rw [hg, hh]

/-! ## The published pointwise composition is not a Bochner integral -/

/-- Oscillatory factor on the diagonal `ν=μ=1` after the paper's substitution `y=1/λ`. -/
def ccmArchimedeanGeometricCompositeDiagonalOscillation (y : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * y) ^ 2

theorem ccmArchimedeanGeometricCompositeDiagonalOscillation_periodic :
    Function.Periodic ccmArchimedeanGeometricCompositeDiagonalOscillation 1 := by
  intro y
  unfold ccmArchimedeanGeometricCompositeDiagonalOscillation
  rw [show 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi by ring]
  rw [Real.cos_add_two_pi]

/-- Exact positive mean of the diagonal oscillation over one multiplicative period. -/
theorem integral_ccmArchimedeanGeometricCompositeDiagonalOscillation_zero_one :
    (∫ y in (0 : ℝ)..1, ccmArchimedeanGeometricCompositeDiagonalOscillation y) =
      1 / 2 := by
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => Real.cos x ^ 2)
    (2 * Real.pi)
  change 2 * Real.pi *
      (∫ y in (0 : ℝ)..1,
        ccmArchimedeanGeometricCompositeDiagonalOscillation y) = _ at hscale
  rw [integral_cos_sq] at hscale
  simp only [mul_zero, mul_one, Real.cos_zero, Real.sin_zero] at hscale
  rw [Real.cos_two_pi, Real.sin_two_pi] at hscale
  nlinarith [Real.pi_pos]

/-- Truncated diagonal integrals grow to `+∞`; oscillation does not supply cancellation. -/
theorem ccmArchimedeanGeometricCompositeDiagonalOscillation_integral_tendsto_atTop :
    Tendsto
      (fun t : ℝ => ∫ y in (0 : ℝ)..t,
        ccmArchimedeanGeometricCompositeDiagonalOscillation y)
      atTop atTop := by
  apply ccmArchimedeanGeometricCompositeDiagonalOscillation_periodic
    |>.tendsto_atTop_intervalIntegral_of_pos
  · rw [integral_ccmArchimedeanGeometricCompositeDiagonalOscillation_zero_one]
    norm_num
  · norm_num

theorem ccmArchimedeanGeometricCompositeDiagonalOscillation_tail_integral_tendsto_atTop :
    Tendsto
      (fun t : ℝ => ∫ y in (1 : ℝ)..t,
        ccmArchimedeanGeometricCompositeDiagonalOscillation y)
      atTop atTop := by
  have hcont : Continuous ccmArchimedeanGeometricCompositeDiagonalOscillation := by
    unfold ccmArchimedeanGeometricCompositeDiagonalOscillation
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2
  have hEq :
      (fun t : ℝ => ∫ y in (1 : ℝ)..t,
        ccmArchimedeanGeometricCompositeDiagonalOscillation y) =
        fun t =>
          (∫ y in (0 : ℝ)..t,
            ccmArchimedeanGeometricCompositeDiagonalOscillation y) -
          ∫ y in (0 : ℝ)..1,
            ccmArchimedeanGeometricCompositeDiagonalOscillation y := by
    funext t
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 t)]
    ring
  rw [hEq]
  simpa only [sub_eq_add_neg, add_comm] using
    (tendsto_atTop_add_const_right atTop
      (-(∫ y in (0 : ℝ)..1,
        ccmArchimedeanGeometricCompositeDiagonalOscillation y))
      ccmArchimedeanGeometricCompositeDiagonalOscillation_integral_tendsto_atTop)

/-- The diagonal oscillation is not Lebesgue integrable on the tail. -/
theorem not_integrableOn_ccmArchimedeanGeometricCompositeDiagonalOscillation_Ioi_one :
    ¬ IntegrableOn ccmArchimedeanGeometricCompositeDiagonalOscillation (Ioi (1 : ℝ)) := by
  intro h
  have hfinite := intervalIntegral_tendsto_integral_Ioi
    (f := ccmArchimedeanGeometricCompositeDiagonalOscillation) 1 h tendsto_id
  exact not_tendsto_atTop_of_tendsto_nhds hfinite
    ccmArchimedeanGeometricCompositeDiagonalOscillation_tail_integral_tendsto_atTop

/-- Real-valued version of the paper's sharp multiplier. -/
def ccmGeometricSharpRealValue (x : ℝ) : ℝ :=
  if (1 : ℝ) ≤ x then 1 else 0

/-- Literal `y`-integrand in Connes--Consani `sch3(iii)` at `ν=μ=1`.
The factor `P(1/y)-P(1)` is kept exactly as published. -/
def ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand (y : ℝ) : ℝ :=
  4 * ccmArchimedeanGeometricCompositeDiagonalOscillation y *
    (ccmGeometricSharpRealValue y⁻¹ - ccmGeometricSharpRealValue 1)

/-- On the full tail `y>1`, the literal published diagonal integrand is `-4 cos²(2πy)`. -/
theorem ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand_eq
    {y : ℝ} (hy : 1 < y) :
    ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand y =
      -4 * ccmArchimedeanGeometricCompositeDiagonalOscillation y := by
  have hinv : y⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hy
  simp [ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand,
    ccmGeometricSharpRealValue, not_le.mpr hinv]

/-- The pointwise integral displayed in `sch3(iii)` is not a Bochner/Lebesgue integral:
already its literal diagonal member `ν=μ=1` is nonintegrable.  Hence the valid theorem is the
operator/distributional pairing above, not a pointwise kernel obtained by Lean's totalized
`MeasureTheory.integral`. -/
theorem not_integrableOn_ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand_Ioi_one :
    ¬ IntegrableOn ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand (Ioi (1 : ℝ)) := by
  intro hraw
  apply not_integrableOn_ccmArchimedeanGeometricCompositeDiagonalOscillation_Ioi_one
  have htail := hraw.const_mul (-((4 : ℝ)⁻¹))
  refine IntegrableOn.congr_fun htail ?_ measurableSet_Ioi
  intro y hy
  change -((4 : ℝ)⁻¹) * ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand y = _
  rw [ccmArchimedeanGeometricCompositeRawDiagonalYIntegrand_eq hy]
  ring

end RHTower
