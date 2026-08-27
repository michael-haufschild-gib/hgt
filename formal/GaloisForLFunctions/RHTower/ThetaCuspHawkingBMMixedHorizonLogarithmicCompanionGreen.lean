import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionPhysical

/-!
# Endpoint-sewn Green kernel for the mixed BM logarithmic companion

The resonant regular branch and logarithmic companion form the two endpoint factors of a sourced
Gauss Green kernel. Changing logarithm sheet adds a regular branch to the companion. The
Wronskian denominator is therefore sheet-invariant, while either sewn kernel piece acquires the
same rank-one regular-mode jump. Finite radial source packets inherit an exact rank-one causal
response law with an explicit source projection.

This derives the mixed response-incidence shape from endpoint sewing. It does not yet identify the
radial source projection with the nonlinear Einstein optical reader.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- First jet of the logarithmic companion on a chosen logarithm sheet. -/
def d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
    (N : ℕ) (a b z logSheet : ℂ) : ℂ :=
  d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b z +
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      (d4HypergeometricResonantRegularBranchFirstDerivative N a b z * logSheet +
        d4HypergeometricResonantRegularBranchValue N a b z * z⁻¹)

/-- Sheet change differentiates to the same monodromy coefficient times the regular first jet. -/
theorem d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet_sub
    (N : ℕ) (a b z logPlus logMinus : ℂ)
    (hlog : logPlus - logMinus = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
          N a b z logPlus -
        d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
          N a b z logMinus =
      2 * Real.pi * Complex.I *
        d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          d4HypergeometricResonantRegularBranchFirstDerivative N a b z := by
  unfold d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
  linear_combination
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      d4HypergeometricResonantRegularBranchFirstDerivative N a b z * hlog

/-- Logarithmic-companion function attached to a differentiable logarithm-sheet representative. -/
def d4HypergeometricResonantLogarithmicCompanionOnSheetFunction
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) : ℂ → ℂ :=
  d4HypergeometricResonantCompanionAnalyticValue N a b + fun z =>
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      (d4HypergeometricResonantRegularBranchValue N a b z * logSheet z)

theorem d4HypergeometricResonantLogarithmicCompanionOnSheetFunction_apply
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (z : ℂ) :
    d4HypergeometricResonantLogarithmicCompanionOnSheetFunction
        N a b logSheet z =
      d4HypergeometricResonantLogarithmicCompanionOnSheet
        N a b z (logSheet z) := by
  simp [d4HypergeometricResonantLogarithmicCompanionOnSheetFunction,
    d4HypergeometricResonantLogarithmicCompanionOnSheet]
  ring

/-- A differentiable logarithm-sheet representative gives the declared companion first jet. -/
theorem hasDerivAt_d4HypergeometricResonantLogarithmicCompanionOnSheet
    (N : ℕ) (a b z : ℂ) (logSheet : ℂ → ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1)
    (hlog : HasDerivAt logSheet z⁻¹ z) :
    HasDerivAt (d4HypergeometricResonantLogarithmicCompanionOnSheetFunction
      N a b logSheet)
      (d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
        N a b z (logSheet z)) z := by
  have hH := hasDerivAt_d4HypergeometricResonantCompanionAnalyticValue
    N a b z ha hb hz
  have hU := hasDerivAt_d4HypergeometricResonantRegularBranchValue
    N a b z ha hb hz
  have hscaled := (hU.mul hlog).const_mul
    (d4HypergeometricResonantFrobeniusLogCoefficient N a b)
  simpa only [d4HypergeometricResonantLogarithmicCompanionOnSheetFunction,
    d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet,
    Pi.add_apply, Pi.mul_apply, mul_assoc] using hH.add hscaled

/-- Leading-coefficient times Wronskian denominator of the sewn mixed Green kernel. -/
def d4HypergeometricResonantEndpointGreenDenominatorOnSheet
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t : ℂ) : ℂ :=
  t * (1 - t) *
    (d4HypergeometricResonantRegularBranchValue N a b t *
        d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
          N a b t (logSheet t) -
      d4HypergeometricResonantRegularBranchFirstDerivative N a b t *
        d4HypergeometricResonantLogarithmicCompanionOnSheet
          N a b t (logSheet t))

/-- Adding one deck multiple of the regular branch leaves endpoint Wronskian denominator fixed. -/
theorem d4HypergeometricResonantEndpointGreenDenominatorOnSheet_eq
    (N : ℕ) (a b t : ℂ) (logPlus logMinus : ℂ → ℂ)
    (hlog : logPlus t - logMinus t = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet
        N a b logPlus t =
      d4HypergeometricResonantEndpointGreenDenominatorOnSheet
        N a b logMinus t := by
  have hvalue := d4HypergeometricResonantLogarithmicCompanionOnSheet_sub
    N a b t (logPlus t) (logMinus t) hlog
  have hderiv :=
    d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet_sub
      N a b t (logPlus t) (logMinus t) hlog
  unfold d4HypergeometricResonantEndpointGreenDenominatorOnSheet
  linear_combination
    t * (1 - t) *
      (d4HypergeometricResonantRegularBranchValue N a b t * hderiv -
        d4HypergeometricResonantRegularBranchFirstDerivative N a b t * hvalue)

/-- Right-field endpoint piece: regular source endpoint sewn to companion field endpoint. -/
def d4HypergeometricResonantRightEndpointGreenKernelOnSheet
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t z : ℂ) : ℂ :=
  d4HypergeometricResonantRegularBranchValue N a b t *
      d4HypergeometricResonantLogarithmicCompanionOnSheet
        N a b z (logSheet z) /
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet N a b logSheet t

/-- Left-field endpoint piece: regular field endpoint sewn to companion source endpoint. -/
def d4HypergeometricResonantLeftEndpointGreenKernelOnSheet
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t z : ℂ) : ℂ :=
  d4HypergeometricResonantRegularBranchValue N a b z *
      d4HypergeometricResonantLogarithmicCompanionOnSheet
        N a b t (logSheet t) /
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet N a b logSheet t

@[simp] theorem d4HypergeometricResonantEndpointGreenKernel_diagonal
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t : ℂ) :
    d4HypergeometricResonantRightEndpointGreenKernelOnSheet
        N a b logSheet t t =
      d4HypergeometricResonantLeftEndpointGreenKernelOnSheet
        N a b logSheet t t := by
  rfl

/-- First field jet of right endpoint kernel piece. -/
def d4HypergeometricResonantRightEndpointGreenKernelFirstDerivativeOnSheet
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t z : ℂ) : ℂ :=
  d4HypergeometricResonantRegularBranchValue N a b t *
      d4HypergeometricResonantLogarithmicCompanionFirstDerivativeOnSheet
        N a b z (logSheet z) /
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet N a b logSheet t

/-- First field jet of left endpoint kernel piece. -/
def d4HypergeometricResonantLeftEndpointGreenKernelFirstDerivativeOnSheet
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t z : ℂ) : ℂ :=
  d4HypergeometricResonantRegularBranchFirstDerivative N a b z *
      d4HypergeometricResonantLogarithmicCompanionOnSheet
        N a b t (logSheet t) /
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet N a b logSheet t

/-- Sewn kernel has exact unit leading-coefficient derivative jump on source diagonal. -/
theorem d4HypergeometricResonantEndpointGreenKernel_derivativeJump_diagonal
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (t : ℂ)
    (hD : d4HypergeometricResonantEndpointGreenDenominatorOnSheet
      N a b logSheet t ≠ 0) :
    t * (1 - t) *
        (d4HypergeometricResonantRightEndpointGreenKernelFirstDerivativeOnSheet
            N a b logSheet t t -
          d4HypergeometricResonantLeftEndpointGreenKernelFirstDerivativeOnSheet
            N a b logSheet t t) = 1 := by
  rw [d4HypergeometricResonantRightEndpointGreenKernelFirstDerivativeOnSheet,
    d4HypergeometricResonantLeftEndpointGreenKernelFirstDerivativeOnSheet,
    ← sub_div, ← mul_div_assoc]
  change
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet
          N a b logSheet t /
        d4HypergeometricResonantEndpointGreenDenominatorOnSheet
          N a b logSheet t = 1
  exact div_self hD

/-- Right endpoint Green piece has exact rank-one deck jump. -/
theorem d4HypergeometricResonantRightEndpointGreenKernelOnSheet_sub
    (N : ℕ) (a b t z : ℂ) (logPlus logMinus : ℂ → ℂ)
    (hlogt : logPlus t - logMinus t = 2 * Real.pi * Complex.I)
    (hlogz : logPlus z - logMinus z = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantRightEndpointGreenKernelOnSheet
          N a b logPlus t z -
        d4HypergeometricResonantRightEndpointGreenKernelOnSheet
          N a b logMinus t z =
      (2 * Real.pi * Complex.I *
          d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          d4HypergeometricResonantRegularBranchValue N a b t /
          d4HypergeometricResonantEndpointGreenDenominatorOnSheet
            N a b logMinus t) *
        d4HypergeometricResonantRegularBranchValue N a b z := by
  rw [d4HypergeometricResonantRightEndpointGreenKernelOnSheet,
    d4HypergeometricResonantRightEndpointGreenKernelOnSheet,
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet_eq
      N a b t logPlus logMinus hlogt,
    ← sub_div, ← mul_sub,
    d4HypergeometricResonantLogarithmicCompanionOnSheet_sub
      N a b z (logPlus z) (logMinus z) hlogz]
  ring

/-- Left endpoint Green piece has same exact rank-one deck jump. -/
theorem d4HypergeometricResonantLeftEndpointGreenKernelOnSheet_sub
    (N : ℕ) (a b t z : ℂ) (logPlus logMinus : ℂ → ℂ)
    (hlogt : logPlus t - logMinus t = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantLeftEndpointGreenKernelOnSheet
          N a b logPlus t z -
        d4HypergeometricResonantLeftEndpointGreenKernelOnSheet
          N a b logMinus t z =
      (2 * Real.pi * Complex.I *
          d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          d4HypergeometricResonantRegularBranchValue N a b t /
          d4HypergeometricResonantEndpointGreenDenominatorOnSheet
            N a b logMinus t) *
        d4HypergeometricResonantRegularBranchValue N a b z := by
  rw [d4HypergeometricResonantLeftEndpointGreenKernelOnSheet,
    d4HypergeometricResonantLeftEndpointGreenKernelOnSheet,
    d4HypergeometricResonantEndpointGreenDenominatorOnSheet_eq
      N a b t logPlus logMinus hlogt,
    ← sub_div, ← mul_sub,
    d4HypergeometricResonantLogarithmicCompanionOnSheet_sub
      N a b t (logPlus t) (logMinus t) hlogt]
  ring

/-- Response of a finite radial source packet through right endpoint Green pieces. -/
def d4HypergeometricResonantFiniteRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ S, source i *
    d4HypergeometricResonantRightEndpointGreenKernelOnSheet
      N a b logSheet (point i) z

/-- Explicit left projection of a finite radial source packet. -/
def d4HypergeometricResonantFiniteEndpointSourceProjection
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (N : ℕ) (a b : ℂ) (logSheet : ℂ → ℂ) : ℂ :=
  ∑ i ∈ S, source i *
    d4HypergeometricResonantRegularBranchValue N a b (point i) /
      d4HypergeometricResonantEndpointGreenDenominatorOnSheet
        N a b logSheet (point i)

/-- Every finite radial source packet has exact rank-one endpoint sheet response. -/
theorem d4HypergeometricResonantFiniteRightEndpointGreenResponse_sub
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (N : ℕ) (a b z : ℂ) (logPlus logMinus : ℂ → ℂ)
    (hlog : ∀ w, logPlus w - logMinus w = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantFiniteRightEndpointGreenResponse
          S point source N a b logPlus z -
        d4HypergeometricResonantFiniteRightEndpointGreenResponse
          S point source N a b logMinus z =
      2 * Real.pi * Complex.I *
          d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          d4HypergeometricResonantFiniteEndpointSourceProjection
            S point source N a b logMinus *
        d4HypergeometricResonantRegularBranchValue N a b z := by
  rw [d4HypergeometricResonantFiniteRightEndpointGreenResponse,
    d4HypergeometricResonantFiniteRightEndpointGreenResponse,
    ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub,
    d4HypergeometricResonantRightEndpointGreenKernelOnSheet_sub
      N a b _ z logPlus logMinus (hlog _) (hlog z)]
  rw [d4HypergeometricResonantFiniteEndpointSourceProjection]
  calc
    _ = ∑ i ∈ S,
        (2 * Real.pi * Complex.I *
            d4HypergeometricResonantFrobeniusLogCoefficient N a b) *
          (source i * d4HypergeometricResonantRegularBranchValue
              N a b (point i) /
            d4HypergeometricResonantEndpointGreenDenominatorOnSheet
              N a b logMinus (point i)) *
          d4HypergeometricResonantRegularBranchValue N a b z := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-! ## Actual Xi-fibre finite-source incidence -/

/-- Endpoint Green response of a finite radial packet on an actual Xi mixed-horizon fibre. -/
def d4BMXiMixedHorizonFiniteRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (n k : ℕ) (q : XiZeroCopy) (logSheet : ℂ → ℂ) (z : ℂ) : ℂ :=
  d4HypergeometricResonantFiniteRightEndpointGreenResponse
    S point source
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
    logSheet z

/-- Explicit finite radial source projection selected by actual Xi endpoint sewing. -/
def d4BMXiMixedHorizonFiniteEndpointSourceProjection
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (n k : ℕ) (q : XiZeroCopy) (logSheet : ℂ → ℂ) : ℂ :=
  d4HypergeometricResonantFiniteEndpointSourceProjection
    S point source
    (d4BMMixedHorizonFrobeniusOrder n k)
    (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
    logSheet

/-- Finite mixed radial sources satisfy the exact response-incidence identity required by the
nonlinear causal cut: endpoint sheet difference is source projection times physical monodromy
mode. -/
theorem d4BMXiMixedHorizonFiniteRightEndpointGreenResponse_sub_eq_exactMonodromyMode
    {ι : Type*} (S : Finset ι) (point source : ι → ℂ)
    (n k : ℕ) (q : XiZeroCopy) (logPlus logMinus : ℂ → ℂ) (z : ℂ)
    (hz : ‖z‖ₑ < 1)
    (hlog : ∀ w, logPlus w - logMinus w = 2 * Real.pi * Complex.I) :
    d4BMXiMixedHorizonFiniteRightEndpointGreenResponse
          S point source n k q logPlus z -
        d4BMXiMixedHorizonFiniteRightEndpointGreenResponse
          S point source n k q logMinus z =
      d4BMXiMixedHorizonFiniteEndpointSourceProjection
          S point source n k q logMinus *
        d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  rw [d4BMXiMixedHorizonFiniteRightEndpointGreenResponse,
    d4BMXiMixedHorizonFiniteRightEndpointGreenResponse,
    d4HypergeometricResonantFiniteRightEndpointGreenResponse_sub
      S point source
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMMixedHorizonComplexB n k (d4BMXiMixedHorizonAngularMomentum q))
      z logPlus logMinus hlog,
    d4BMXiMixedHorizonResonantRegularBranchValue_eq n k q z hz]
  rw [d4BMXiMixedHorizonFiniteEndpointSourceProjection,
    d4BMXiMixedHorizonExactMonodromyMode,
    d4BMXiMixedHorizonComplexMonodromyJump,
    d4BMMixedHorizonComplexMonodromyJump]
  ring

end

end RHTower
