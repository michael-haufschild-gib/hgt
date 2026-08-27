import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicComplementaryGaussConnectionCoefficient

/-!
# Canonical BM horizon-basis Green Krein identity

Exact regular and complementary horizon solutions are each sewn to physical normalizable AdS
branch. Gauss nonvanishing removes both denominator premises. Their Green-kernel difference is
rank one with exact complementary Frobenius exponent coefficient; finite radial packets inherit a
source-global factorization on every Xi fibre.

Regular/complementary horizon basis is canonical but its physical retarded/advanced incidence
remains separate.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Normalized Wronskian denominator sewing regular horizon line to normalizable AdS line. -/
def d4BMPlusPlusRegularAdSNormalizableGreenDenominator
    (n : ℕ) (chi : ℂ) (t : ℝ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
    (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
    (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ))
    (d4BMPlusPlusAdSNormalizableSolution n chi)
    (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi) t

/-- Normalized Wronskian denominator sewing complementary horizon line to normalizable AdS line. -/
def d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator
    (n : ℕ) (chi : ℂ) (t : ℝ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
    (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
    (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi)
    (d4BMPlusPlusAdSNormalizableSolution n chi)
    (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi) t

/-- Regular/normalizable denominator is regular forbidden coefficient times outer Wronskian. -/
theorem d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t =
      d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
        d4BMPlusPlusAdSOuterWronskian n chi t := by
  have hU := (d4BMPlusPlusRegularAdSConnection_phase n chi hchi ht0 ht1)
  rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator,
    d4BMPlusPlusAdSOuterWronskian,
    d4BMPlusPlusNormalizedWronskian,
    d4BMPlusPlusNormalizedWronskian, hU.1, hU.2]
  ring

/-- Complementary/normalizable denominator is complementary source coefficient times outer Wronskian. -/
theorem d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t =
      d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi *
        d4BMPlusPlusAdSOuterWronskian n chi t := by
  have hC := (d4BMPlusPlusComplementaryAdSConnection_phase n chi hchi ht0 ht1)
  rw [d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator,
    d4BMPlusPlusAdSOuterWronskian,
    d4BMPlusPlusNormalizedWronskian,
    d4BMPlusPlusNormalizedWronskian, hC.1, hC.2]
  ring

/-- Exact regular/normalizable denominator normalization. -/
theorem d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t =
      -d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi / 2 := by
  rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq n chi hchi ht0 ht1,
    d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi ht0 ht1]
  ring

/-- Exact complementary/normalizable denominator normalization. -/
theorem d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq_neg_half
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t =
      -d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi / 2 := by
  rw [d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq n chi hchi ht0 ht1,
    d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi ht0 ht1]
  ring

/-- Regular/normalizable Green denominator is premise-free nonzero on radial interior. -/
theorem d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t ≠ 0 := by
  rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1]
  exact div_ne_zero
    (neg_ne_zero.mpr
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi))
    (by norm_num)

/-- Complementary/normalizable Green denominator is premise-free nonzero on radial interior. -/
theorem d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t ≠ 0 := by
  rw [d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1]
  exact div_ne_zero
    (neg_ne_zero.mpr
      (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero n chi hchi))
    (by norm_num)

/-- Right endpoint kernel for regular horizon and normalizable AdS conditions. -/
def d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusAdSNormalizableSolution n chi z /
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t

/-- Right endpoint kernel for complementary horizon and normalizable AdS conditions. -/
def d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryHypergeometricSolution n chi t *
      d4BMPlusPlusAdSNormalizableSolution n chi z /
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t

/-- Left endpoint kernel for regular horizon and normalizable AdS conditions. -/
def d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
      d4BMPlusPlusAdSNormalizableSolution n chi t /
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t

/-- Left endpoint kernel for complementary horizon and normalizable AdS conditions. -/
def d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryHypergeometricSolution n chi z *
      d4BMPlusPlusAdSNormalizableSolution n chi t /
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t

/-- Exact rank-one right-kernel difference between canonical horizon basis lines. -/
theorem d4BMPlusPlusHorizonBasisRightEndpointGreenKernel_sub
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel n chi t z -
        d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernel n chi t z =
      -d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi t *
          d4BMPlusPlusAdSNormalizableSolution n chi z /
        (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t) := by
  have hDR := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  have hDC := d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  have hDReq := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1
  have hDCeq := d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1
  have hU := (d4BMPlusPlusRegularAdSConnection_phase n chi hchi ht0 ht1).1
  have hC := (d4BMPlusPlusComplementaryAdSConnection_phase n chi hchi ht0 ht1).1
  have hdet := d4BMPlusPlusAdSConnectionDet_eq n chi hchi
  have hnum :
      d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t -
        d4BMPlusPlusComplementaryHypergeometricSolution n chi t *
          d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t =
        -d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi t := by
    rw [hDReq, hDCeq, hU, hC]
    linear_combination
      (d4BMPlusPlusAdSNormalizableSolution n chi t / 2) * hdet
  rw [d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel, d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernel]
  calc
    _ = (d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
            d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t -
          d4BMPlusPlusComplementaryHypergeometricSolution n chi t *
            d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t) *
          d4BMPlusPlusAdSNormalizableSolution n chi z /
        (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t) := by
      field_simp [hDR, hDC]
    _ = _ := by rw [hnum]

/-- Exact rank-one left-kernel difference between canonical horizon basis lines. -/
theorem d4BMPlusPlusHorizonBasisLeftEndpointGreenKernel_sub
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernel n chi t z -
        d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernel n chi t z =
      -d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi t *
          d4BMPlusPlusAdSNormalizableSolution n chi z /
        (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t) := by
  have hDR := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  have hDC := d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  have hDReq := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1
  have hDCeq := d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht0 ht1
  have hU := (d4BMPlusPlusRegularAdSConnection_phase n chi hchi hz0 hz1).1
  have hC := (d4BMPlusPlusComplementaryAdSConnection_phase n chi hchi hz0 hz1).1
  have hdet := d4BMPlusPlusAdSConnectionDet_eq n chi hchi
  have hnum :
      d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t -
        d4BMPlusPlusComplementaryHypergeometricSolution n chi z *
          d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t =
        -d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi z := by
    rw [hDReq, hDCeq, hU, hC]
    linear_combination
      (d4BMPlusPlusAdSNormalizableSolution n chi z / 2) * hdet
  rw [d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernel, d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernel]
  calc
    _ = (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
            d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t -
          d4BMPlusPlusComplementaryHypergeometricSolution n chi z *
            d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t) *
          d4BMPlusPlusAdSNormalizableSolution n chi t /
        (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t *
          d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t) := by
      field_simp [hDR, hDC]
    _ = _ := by rw [hnum]; ring

/-- First field jet of regular/normalizable right endpoint kernel. -/
def d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z /
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t

/-- First field jet of regular/normalizable left endpoint kernel. -/
def d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
      d4BMPlusPlusAdSNormalizableSolution n chi t /
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t

/-- First field jet of complementary/normalizable right endpoint kernel. -/
def d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryHypergeometricSolution n chi t *
      d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z /
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t

/-- First field jet of complementary/normalizable left endpoint kernel. -/
def d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernelFirstDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z *
      d4BMPlusPlusAdSNormalizableSolution n chi t /
    d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t

/-- Regular/normalizable sewn kernel has exact unit normalized diagonal derivative jump. -/
theorem d4BMPlusPlusRegularAdSNormalizableGreenKernel_derivativeJump_diagonal
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusIntegratingFactor n chi t *
        (d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernelFirstDerivative n chi t t -
          d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernelFirstDerivative n chi t t) = 1 := by
  have hD := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  rw [d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernelFirstDerivative,
    d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernelFirstDerivative, ← sub_div, ← mul_div_assoc]
  change d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t /
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t = 1
  exact div_self hD

/-- Complementary/normalizable sewn kernel has exact unit normalized diagonal derivative jump. -/
theorem d4BMPlusPlusComplementaryAdSNormalizableGreenKernel_derivativeJump_diagonal
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusIntegratingFactor n chi t *
        (d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernelFirstDerivative n chi t t -
          d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernelFirstDerivative n chi t t) = 1 := by
  have hD := d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_ne_zero n chi hchi ht0 ht1
  rw [d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernelFirstDerivative,
    d4BMPlusPlusComplementaryAdSNormalizableLeftEndpointGreenKernelFirstDerivative, ← sub_div, ← mul_div_assoc]
  change d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t /
      d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi t = 1
  exact div_self hD

/-- Finite source packet propagated through regular/normalizable right kernel. -/
def d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  ∑ i ∈ S, source i * d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel n chi (point i) z

/-- Finite source packet propagated through complementary/normalizable right kernel. -/
def d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  ∑ i ∈ S, source i * d4BMPlusPlusComplementaryAdSNormalizableRightEndpointGreenKernel n chi (point i) z

/-- Explicit finite-source projection for canonical horizon-basis Green difference. -/
def d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) : ℂ :=
  ∑ i ∈ S, source i *
    (-d4BMPlusPlusComplementaryFrobeniusExponent n chi *
        d4BMPlusPlusAdSNormalizableSolution n chi (point i) /
      (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (point i) *
        d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi (point i)))

/-- Finite packets obey exact source-global canonical horizon-basis Green identity. -/
theorem d4BMPlusPlusFiniteHorizonBasisRightEndpointGreenResponse_sub
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (z : ℝ)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse S point source n chi z -
        d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse S point source n chi z =
      d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection S point source n chi *
        d4BMPlusPlusAdSNormalizableSolution n chi z := by
  rw [d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse,
    d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection]
  calc
    _ = ∑ i ∈ S,
        (source i *
          (-d4BMPlusPlusComplementaryFrobeniusExponent n chi *
              d4BMPlusPlusAdSNormalizableSolution n chi (point i) /
            (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (point i) *
              d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator n chi (point i)))) *
          d4BMPlusPlusAdSNormalizableSolution n chi z := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := hpoint i hi
      rw [d4BMPlusPlusHorizonBasisRightEndpointGreenKernel_sub n chi hchi hi'.1 hi'.2]
      ring
    _ = _ := by rw [← Finset.sum_mul]

/-- Actual Xi fibres inherit exact source-global canonical horizon-basis Green identity. -/
theorem d4BMXiPlusPlusFiniteHorizonBasisRightEndpointGreenResponse_sub
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (q : XiZeroCopy) (z : ℝ)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteRegularAdSNormalizableRightEndpointGreenResponse S point source n
          (d4BMXiMixedHorizonAngularMomentum q) z -
        d4BMPlusPlusFiniteComplementaryAdSNormalizableRightEndpointGreenResponse S point source n
          (d4BMXiMixedHorizonAngularMomentum q) z =
      d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection S point source n
          (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMPlusPlusAdSNormalizableSolution n
          (d4BMXiMixedHorizonAngularMomentum q) z :=
  d4BMPlusPlusFiniteHorizonBasisRightEndpointGreenResponse_sub S point source n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) z hpoint

end

end RHTower
