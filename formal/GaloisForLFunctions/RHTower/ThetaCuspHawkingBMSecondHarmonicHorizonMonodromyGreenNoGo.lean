import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicHorizonWronskianMonodromy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicExactWronskianConservation

/-!
# Projective no-go for `++` horizon monodromy Green cuts

Multiplying exact complementary `++` solution by a nonzero horizon-sheet multiplier multiplies
its normalized Wronskian by same scalar. Both endpoint-selected Green pieces are consequently
unchanged. In particular, distinct clockwise and counterclockwise Frobenius multipliers produce
same Green operator, despite their nonzero mode-level monodromy difference.

Therefore a Birmingham--Mokhtari Peierls cut cannot be obtained by renormalizing one horizon
solution line. Retarded and advanced propagators must select distinct projective outer-boundary
response lines.

`[NO-GO] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Complementary `++` solution on a multiplicatively rescaled horizon sheet. -/
def d4BMPlusPlusScaledComplementarySolution
    (n : ℕ) (chi mu : ℂ) (z : ℝ) : ℂ :=
  mu * d4BMPlusPlusComplementaryHypergeometricSolution n chi z

/-- First jet of multiplicatively rescaled complementary solution. -/
def d4BMPlusPlusScaledComplementarySolutionDerivative
    (n : ℕ) (chi mu : ℂ) (z : ℝ) : ℂ :=
  mu * d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z

/-- Normalized regular/scaled-complementary Wronskian. -/
def d4BMPlusPlusScaledRegularComplementaryWronskian
    (n : ℕ) (chi mu : ℂ) (t : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingFactor n chi t *
    (d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
        d4BMPlusPlusScaledComplementarySolutionDerivative n chi mu t -
      d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ) *
        d4BMPlusPlusScaledComplementarySolution n chi mu t)

/-- Scaling complementary line scales normalized Wronskian by same factor. -/
theorem d4BMPlusPlusScaledRegularComplementaryWronskian_eq
    (n : ℕ) (chi mu : ℂ) (t : ℝ) :
    d4BMPlusPlusScaledRegularComplementaryWronskian n chi mu t =
      mu * d4BMPlusPlusRegularComplementaryWronskian n chi t := by
  simp [d4BMPlusPlusScaledRegularComplementaryWronskian,
    d4BMPlusPlusScaledComplementarySolution,
    d4BMPlusPlusScaledComplementarySolutionDerivative,
    d4BMPlusPlusRegularComplementaryWronskian]
  ring

/-- Right endpoint piece built from one scaled complementary line. -/
def d4BMPlusPlusScaledRightEndpointGreenKernel
    (n : ℕ) (chi mu : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusScaledComplementarySolution n chi mu z /
    d4BMPlusPlusScaledRegularComplementaryWronskian n chi mu t

/-- Left endpoint piece built from one scaled complementary line. -/
def d4BMPlusPlusScaledLeftEndpointGreenKernel
    (n : ℕ) (chi mu : ℂ) (t z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
      d4BMPlusPlusScaledComplementarySolution n chi mu t /
    d4BMPlusPlusScaledRegularComplementaryWronskian n chi mu t

/-- Right endpoint Green piece depends only on projective complementary solution line. -/
theorem d4BMPlusPlusScaledRightEndpointGreenKernel_eq_one
    (n : ℕ) (chi mu : ℂ) (t z : ℝ) (hmu : mu ≠ 0)
    (hW : d4BMPlusPlusRegularComplementaryWronskian n chi t ≠ 0) :
    d4BMPlusPlusScaledRightEndpointGreenKernel n chi mu t z =
      d4BMPlusPlusScaledRightEndpointGreenKernel n chi 1 t z := by
  rw [d4BMPlusPlusScaledRightEndpointGreenKernel,
    d4BMPlusPlusScaledRightEndpointGreenKernel,
    d4BMPlusPlusScaledComplementarySolution,
    d4BMPlusPlusScaledComplementarySolution,
    d4BMPlusPlusScaledRegularComplementaryWronskian_eq,
    d4BMPlusPlusScaledRegularComplementaryWronskian_eq]
  field_simp [hmu, hW]

/-- Left endpoint Green piece also depends only on projective complementary solution line. -/
theorem d4BMPlusPlusScaledLeftEndpointGreenKernel_eq_one
    (n : ℕ) (chi mu : ℂ) (t z : ℝ) (hmu : mu ≠ 0)
    (hW : d4BMPlusPlusRegularComplementaryWronskian n chi t ≠ 0) :
    d4BMPlusPlusScaledLeftEndpointGreenKernel n chi mu t z =
      d4BMPlusPlusScaledLeftEndpointGreenKernel n chi 1 t z := by
  rw [d4BMPlusPlusScaledLeftEndpointGreenKernel,
    d4BMPlusPlusScaledLeftEndpointGreenKernel,
    d4BMPlusPlusScaledComplementarySolution,
    d4BMPlusPlusScaledComplementarySolution,
    d4BMPlusPlusScaledRegularComplementaryWronskian_eq,
    d4BMPlusPlusScaledRegularComplementaryWronskian_eq]
  field_simp [hmu, hW]

/-- Clockwise and counterclockwise horizon continuations give identical right Green piece. -/
theorem d4BMPlusPlusCounterclockwiseRightEndpointGreenKernel_eq_clockwise
    (n : ℕ) (chi : ℂ) {t : ℝ} (z : ℝ)
    (hchi : chi.re ≠ 0) (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusScaledRightEndpointGreenKernel n chi
        (d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi) t z =
      d4BMPlusPlusScaledRightEndpointGreenKernel n chi
        (d4BMPlusPlusClockwiseFrobeniusMultiplier n chi) t z := by
  have hW := d4BMPlusPlusRegularComplementaryWronskian_ne_zero
    n chi hchi ht0 ht1
  have hccw : d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi ≠ 0 := by
    unfold d4BMPlusPlusCounterclockwiseFrobeniusMultiplier
    exact Complex.exp_ne_zero _
  have hcw : d4BMPlusPlusClockwiseFrobeniusMultiplier n chi ≠ 0 := by
    unfold d4BMPlusPlusClockwiseFrobeniusMultiplier
    exact Complex.exp_ne_zero _
  rw [d4BMPlusPlusScaledRightEndpointGreenKernel_eq_one n chi _ t z
      hccw hW,
    d4BMPlusPlusScaledRightEndpointGreenKernel_eq_one n chi _ t z
      hcw hW]

/-- Clockwise and counterclockwise horizon continuations give identical left Green piece. -/
theorem d4BMPlusPlusCounterclockwiseLeftEndpointGreenKernel_eq_clockwise
    (n : ℕ) (chi : ℂ) {t : ℝ} (z : ℝ)
    (hchi : chi.re ≠ 0) (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusScaledLeftEndpointGreenKernel n chi
        (d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi) t z =
      d4BMPlusPlusScaledLeftEndpointGreenKernel n chi
        (d4BMPlusPlusClockwiseFrobeniusMultiplier n chi) t z := by
  have hW := d4BMPlusPlusRegularComplementaryWronskian_ne_zero
    n chi hchi ht0 ht1
  have hccw : d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi ≠ 0 := by
    unfold d4BMPlusPlusCounterclockwiseFrobeniusMultiplier
    exact Complex.exp_ne_zero _
  have hcw : d4BMPlusPlusClockwiseFrobeniusMultiplier n chi ≠ 0 := by
    unfold d4BMPlusPlusClockwiseFrobeniusMultiplier
    exact Complex.exp_ne_zero _
  rw [d4BMPlusPlusScaledLeftEndpointGreenKernel_eq_one n chi _ t z
      hccw hW,
    d4BMPlusPlusScaledLeftEndpointGreenKernel_eq_one n chi _ t z
      hcw hW]

/-- Finite source response through rescaled right endpoint pieces. -/
def d4BMPlusPlusScaledFiniteRightEndpointGreenResponse
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi mu : ℂ) (z : ℝ) : ℂ :=
  ∑ i ∈ S, source i *
    d4BMPlusPlusScaledRightEndpointGreenKernel n chi mu (point i) z

/-- Every finite radial packet has zero clockwise-minus-counterclockwise Green response. -/
theorem d4BMPlusPlusScaledFiniteRightEndpointGreenResponse_counterclockwise_eq_clockwise
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (z : ℝ) (hchi : chi.re ≠ 0)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusScaledFiniteRightEndpointGreenResponse S point source n chi
        (d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi) z =
      d4BMPlusPlusScaledFiniteRightEndpointGreenResponse S point source n chi
        (d4BMPlusPlusClockwiseFrobeniusMultiplier n chi) z := by
  unfold d4BMPlusPlusScaledFiniteRightEndpointGreenResponse
  apply Finset.sum_congr rfl
  intro i hi
  rw [d4BMPlusPlusCounterclockwiseRightEndpointGreenKernel_eq_clockwise
    n chi z hchi (hpoint i hi).1 (hpoint i hi).2]

end

end RHTower
