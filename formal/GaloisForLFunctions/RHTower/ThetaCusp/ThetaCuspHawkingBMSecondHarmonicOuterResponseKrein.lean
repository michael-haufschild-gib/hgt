import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussSquareRootEndpoint

/-!
# Exact BM outer-response Krein identity

Distinct affine lines in the exact forbidden/normalizable AdS basis produce a normalized rank-one
difference of endpoint Green kernels. Their denominator vanishes exactly on the horizon-regular
projective response line. Finite radial packets inherit the same source-global factorization.

This is the positive replacement exposed by the horizon-monodromy scaling no-go. Physical
retarded/advanced response-line selection remains separate.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Exact AdS outer solution spanning affine response line `S + response * V`. -/
def d4BMPlusPlusAdSOuterResponseSolution
    (n : ℕ) (chi response : ℂ) : ℝ → ℂ := fun z =>
  d4BMPlusPlusAdSForbiddenSolution n chi z +
    response * d4BMPlusPlusAdSNormalizableSolution n chi z

/-- Declared first radial jet of exact affine outer response solution. -/
def d4BMPlusPlusAdSOuterResponseSolutionDerivative
    (n : ℕ) (chi response : ℂ) : ℝ → ℂ := fun z =>
  d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z +
    response * d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z

/-- Conserved normalized Wronskian between horizon-regular and affine outer response solutions. -/
def d4BMPlusPlusAdSOuterResponseGreenDenominator
    (n : ℕ) (chi response : ℂ) (t : ℝ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
    (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
    (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ))
    (d4BMPlusPlusAdSOuterResponseSolution n chi response)
    (d4BMPlusPlusAdSOuterResponseSolutionDerivative n chi response) t

/-- Horizon-regular forbidden/source connection coefficient is nonzero off Frobenius resonance. -/
theorem d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi ≠ 0 := by
  rw [d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_eq n chi hchi,
    d4BMCausalForbiddenBoundaryCoefficient]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply Complex.Gamma_ne_zero
      intro m hm
      rw [d4BMCausalRadialC_plusPlus_eq] at hm
      have him := congrArg Complex.im hm
      norm_num [Complex.mul_im] at him
      exact hchi (by linarith)
    · apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
  · apply mul_ne_zero
    · apply Complex.Gamma_ne_zero
      intro m hm
      apply d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero n chi hchi m
      rw [hm]
      ring
    · apply Complex.Gamma_ne_zero
      intro m hm
      apply d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero n chi hchi m
      rw [hm]
      ring

/-- Ratio of exact normalizable and forbidden coefficients is literal BM projective response. -/
theorem d4BMPlusPlusRegularAdSConnectionCoefficient_ratio_eq_projectiveResponse
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi /
        d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi =
      d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusPlusFrequency n chi) chi := by
  have hGA : Complex.Gamma
      (d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    apply d4BMCausalRadialA_plusPlus_ne_negNat_of_re_ne_zero n chi hchi m
    rw [hm]
    ring
  have hGB : Complex.Gamma
      (d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    apply d4BMCausalRadialB_plusPlus_ne_negNat_of_re_ne_zero n chi hchi m
    rw [hm]
    ring
  have hfactor := d4BMCausalDecayingBoundaryCoefficient_eq_projective_mul_forbidden
    (d4BMCausalPlusPlusFrequency n chi) chi hGA hGB
  have hfactor' :
      d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi =
        d4BMCausalProjectiveBoundaryResponse
            (d4BMCausalPlusPlusFrequency n chi) chi *
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi := by
    rw [d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq n chi hchi,
      d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_eq n chi hchi]
    exact hfactor
  exact (div_eq_iff (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi)).2 hfactor'

/-- Exact Cramer factorization of affine outer-response Green denominator. -/
theorem d4BMPlusPlusAdSOuterResponseGreenDenominator_eq
    (n : ℕ) (chi response : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t =
      (response * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi -
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi) *
        d4BMPlusPlusAdSOuterWronskian n chi t := by
  rcases d4BMPlusPlusRegularAdSConnection_phase n chi hchi ht0 ht1 with
    ⟨hU, hUd⟩
  unfold d4BMPlusPlusAdSOuterResponseGreenDenominator d4BMPlusPlusAdSOuterResponseSolution
    d4BMPlusPlusAdSOuterResponseSolutionDerivative d4BMPlusPlusAdSOuterWronskian
  rw [d4BMPlusPlusNormalizedWronskian,
    d4BMPlusPlusNormalizedWronskian, hU, hUd]
  ring

/-- Outer Wronskian normalization reduces response denominator to one affine factor. -/
theorem d4BMPlusPlusAdSOuterResponseGreenDenominator_eq_neg_half
    (n : ℕ) (chi response : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t =
      -(response * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi -
          d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi) / 2 := by
  rw [d4BMPlusPlusAdSOuterResponseGreenDenominator_eq n chi response hchi ht0 ht1,
    d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi ht0 ht1]
  ring

/-- Response denominator is nonsingular exactly away from BM projective response line. -/
theorem d4BMPlusPlusAdSOuterResponseGreenDenominator_ne_zero_iff
    (n : ℕ) (chi response : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t ≠ 0 ↔
      response ≠ d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusPlusFrequency n chi) chi := by
  rw [d4BMPlusPlusAdSOuterResponseGreenDenominator_eq n chi response hchi ht0 ht1]
  have hW := d4BMPlusPlusAdSOuterWronskian_ne_zero n chi hchi ht0 ht1
  rw [mul_ne_zero_iff_right hW]
  have hA := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  rw [ne_eq, sub_eq_zero,
    ← d4BMPlusPlusRegularAdSConnectionCoefficient_ratio_eq_projectiveResponse n chi hchi]
  exact not_congr (eq_div_iff hA).symm

/-- Right-field endpoint kernel sewn from horizon-regular and affine outer response solutions. -/
def d4BMPlusPlusOuterResponseRightEndpointGreenKernel
    (n : ℕ) (chi response : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusAdSOuterResponseSolution n chi response z /
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t

/-- Left-field endpoint kernel sewn from horizon-regular and affine outer response solutions. -/
def d4BMPlusPlusOuterResponseLeftEndpointGreenKernel
    (n : ℕ) (chi response : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
      d4BMPlusPlusAdSOuterResponseSolution n chi response t /
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t

/-- Exact normalized rank-one Krein difference of two right endpoint response kernels. -/
theorem d4BMPlusPlusOuterResponseRightEndpointGreenKernel_sub
    (n : ℕ) (chi responseA responseB : ℂ) (hchi : chi.re ≠ 0)
    {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hDA : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA t ≠ 0)
    (hDB : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB t ≠ 0) :
    d4BMPlusPlusOuterResponseRightEndpointGreenKernel n chi responseA t z -
        d4BMPlusPlusOuterResponseRightEndpointGreenKernel n chi responseB t z =
      (responseA - responseB) / 2 *
          d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
          d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) /
        (d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA t *
          d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB t) := by
  have hDenA := d4BMPlusPlusAdSOuterResponseGreenDenominator_eq_neg_half
    n chi responseA hchi ht0 ht1
  have hDenB := d4BMPlusPlusAdSOuterResponseGreenDenominator_eq_neg_half
    n chi responseB hchi ht0 ht1
  have hUz := (d4BMPlusPlusRegularAdSConnection_phase n chi hchi hz0 hz1).1
  rw [d4BMPlusPlusOuterResponseRightEndpointGreenKernel, d4BMPlusPlusOuterResponseRightEndpointGreenKernel]
  simp only [d4BMPlusPlusAdSOuterResponseSolution]
  field_simp [hDA, hDB]
  rw [hDenA, hDenB, hUz]
  ring

/-- Exact normalized rank-one Krein difference of two left endpoint response kernels. -/
theorem d4BMPlusPlusOuterResponseLeftEndpointGreenKernel_sub
    (n : ℕ) (chi responseA responseB : ℂ) (hchi : chi.re ≠ 0)
    {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hDA : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA t ≠ 0)
    (hDB : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB t ≠ 0) :
    d4BMPlusPlusOuterResponseLeftEndpointGreenKernel n chi responseA t z -
        d4BMPlusPlusOuterResponseLeftEndpointGreenKernel n chi responseB t z =
      (responseA - responseB) / 2 *
          d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
          d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) /
        (d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA t *
          d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB t) := by
  have hDenA := d4BMPlusPlusAdSOuterResponseGreenDenominator_eq_neg_half
    n chi responseA hchi ht0 ht1
  have hDenB := d4BMPlusPlusAdSOuterResponseGreenDenominator_eq_neg_half
    n chi responseB hchi ht0 ht1
  have hUt := (d4BMPlusPlusRegularAdSConnection_phase n chi hchi ht0 ht1).1
  rw [d4BMPlusPlusOuterResponseLeftEndpointGreenKernel, d4BMPlusPlusOuterResponseLeftEndpointGreenKernel]
  simp only [d4BMPlusPlusAdSOuterResponseSolution]
  field_simp [hDA, hDB]
  rw [hDenA, hDenB, hUt]
  ring

/-- First field jet of right affine outer-response endpoint kernel. -/
def d4BMPlusPlusOuterResponseRightEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi response : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusAdSOuterResponseSolutionDerivative n chi response z /
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t

/-- First field jet of left affine outer-response endpoint kernel. -/
def d4BMPlusPlusOuterResponseLeftEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi response : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
      d4BMPlusPlusAdSOuterResponseSolution n chi response t /
    d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t

/-- Sewn outer-response kernel has exact unit normalized derivative jump on source diagonal. -/
theorem d4BMPlusPlusOuterResponseEndpointGreenKernel_derivativeJump_diagonal
    (n : ℕ) (chi response : ℂ) (t : ℝ)
    (hD : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t ≠ 0) :
    d4BMPlusPlusIntegratingFactor n chi t *
        (d4BMPlusPlusOuterResponseRightEndpointGreenKernelFirstDerivative n chi response t t -
          d4BMPlusPlusOuterResponseLeftEndpointGreenKernelFirstDerivative n chi response t t) = 1 := by
  rw [d4BMPlusPlusOuterResponseRightEndpointGreenKernelFirstDerivative,
    d4BMPlusPlusOuterResponseLeftEndpointGreenKernelFirstDerivative, ← sub_div, ← mul_div_assoc]
  change d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t /
      d4BMPlusPlusAdSOuterResponseGreenDenominator n chi response t = 1
  exact div_self hD

/-- Finite radial packet propagated through right affine outer-response endpoint kernel. -/
def d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi response : ℂ) (z : ℝ) : ℂ :=
  ∑ i ∈ S, source i * d4BMPlusPlusOuterResponseRightEndpointGreenKernel
    n chi response (point i) z

/-- Explicit source projection multiplying rank-one difference between two response lines. -/
def d4BMPlusPlusFiniteOuterResponseSourceProjection
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi responseA responseB : ℂ) : ℂ :=
  ∑ i ∈ S, source i *
    ((responseA - responseB) / 2 *
        d4BMPlusPlusRegularHypergeometricSolution n chi (point i : ℂ) /
      (d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA (point i) *
        d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB (point i)))

/-- Every finite radial packet obeys exact source-global outer-response Krein identity. -/
theorem d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse_sub
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi responseA responseB : ℂ) (hchi : chi.re ≠ 0) (z : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1)
    (hA : responseA ≠ d4BMCausalProjectiveBoundaryResponse
      (d4BMCausalPlusPlusFrequency n chi) chi)
    (hB : responseB ≠ d4BMCausalProjectiveBoundaryResponse
      (d4BMCausalPlusPlusFrequency n chi) chi) :
    d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse S point source n chi responseA z -
        d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse S point source n chi responseB z =
      d4BMPlusPlusFiniteOuterResponseSourceProjection S point source n chi responseA responseB *
        d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) := by
  rw [d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse,
    d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [d4BMPlusPlusFiniteOuterResponseSourceProjection]
  calc
    _ = ∑ i ∈ S,
        (source i *
          ((responseA - responseB) / 2 *
              d4BMPlusPlusRegularHypergeometricSolution n chi (point i : ℂ) /
            (d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA (point i) *
              d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB (point i)))) *
          d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := hpoint i hi
      have hDA : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseA (point i) ≠ 0 :=
        (d4BMPlusPlusAdSOuterResponseGreenDenominator_ne_zero_iff
          n chi responseA hchi hi'.1 hi'.2).2 hA
      have hDB : d4BMPlusPlusAdSOuterResponseGreenDenominator n chi responseB (point i) ≠ 0 :=
        (d4BMPlusPlusAdSOuterResponseGreenDenominator_ne_zero_iff
          n chi responseB hchi hi'.1 hi'.2).2 hB
      rw [d4BMPlusPlusOuterResponseRightEndpointGreenKernel_sub n chi responseA responseB hchi
        (t := point i) (z := z) hi'.1 hi'.2 hz0 hz1 hDA hDB]
      ring
    _ = _ := by rw [← Finset.sum_mul]

/-! ## Actual Xi-fibre outer-response cut -/

/-- Every Xi-fibre affine response denominator is nonsingular precisely off its BM response. -/
theorem d4BMXiPlusPlusAdSOuterResponseGreenDenominator_ne_zero_iff
    (n : ℕ) (q : XiZeroCopy) (response : ℂ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusAdSOuterResponseGreenDenominator n
          (d4BMXiMixedHorizonAngularMomentum q) response t ≠ 0 ↔
      response ≠ d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
        (d4BMXiMixedHorizonAngularMomentum q) :=
  d4BMPlusPlusAdSOuterResponseGreenDenominator_ne_zero_iff
    n (d4BMXiMixedHorizonAngularMomentum q) response
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) ht0 ht1

/-- Every finite Xi-fibre radial source has exact rank-one response-line cut. -/
theorem d4BMXiPlusPlusFiniteOuterResponseRightEndpointGreenResponse_sub
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (q : XiZeroCopy) (responseA responseB : ℂ) (z : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1)
    (hA : responseA ≠ d4BMCausalProjectiveBoundaryResponse
      (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMXiMixedHorizonAngularMomentum q))
    (hB : responseB ≠ d4BMCausalProjectiveBoundaryResponse
      (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
      (d4BMXiMixedHorizonAngularMomentum q)) :
    d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse
          S point source n (d4BMXiMixedHorizonAngularMomentum q) responseA z -
        d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse
          S point source n (d4BMXiMixedHorizonAngularMomentum q) responseB z =
      d4BMPlusPlusFiniteOuterResponseSourceProjection
          S point source n (d4BMXiMixedHorizonAngularMomentum q) responseA responseB *
        d4BMPlusPlusRegularHypergeometricSolution n
          (d4BMXiMixedHorizonAngularMomentum q) (z : ℂ) :=
  d4BMPlusPlusFiniteOuterResponseRightEndpointGreenResponse_sub
    S point source n (d4BMXiMixedHorizonAngularMomentum q) responseA responseB
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) z hz0 hz1 hpoint hA hB

end

end RHTower
