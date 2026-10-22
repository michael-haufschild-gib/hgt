import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicExactHorizonBasis

/-!
# Exact local BM second-harmonic Cauchy/Peierls kernel

The exact regular/complementary basis produces a two-point Cauchy kernel wherever its normalized
Wronskian is nonzero. The kernel solves the homogeneous BM equation in its field variable, vanishes
on the diagonal, and has exact unit integrating-factor derivative jump. These statements derive a
local fundamental kernel without assuming retarded/advanced endpoint incidence.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Two-point Cauchy kernel from exact complementary and regular BM solutions. -/
def d4BMPlusPlusExactCauchyKernel
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  (d4BMPlusPlusComplementaryHypergeometricSolution n chi z *
        d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) -
      d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
        d4BMPlusPlusComplementaryHypergeometricSolution n chi t) /
    d4BMPlusPlusRegularComplementaryWronskian n chi t

/-- Exact first field-variable derivative of the Cauchy kernel. -/
def d4BMPlusPlusExactCauchyKernelDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z *
        d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) -
      d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
        d4BMPlusPlusComplementaryHypergeometricSolution n chi t) /
    d4BMPlusPlusRegularComplementaryWronskian n chi t

/-- Exact second field-variable derivative of the Cauchy kernel. -/
def d4BMPlusPlusExactCauchyKernelSecondDerivative
    (n : ℕ) (chi : ℂ) (t z : ℝ) : ℂ :=
  (d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi z *
        d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) -
      d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ) *
        d4BMPlusPlusComplementaryHypergeometricSolution n chi t) /
    d4BMPlusPlusRegularComplementaryWronskian n chi t

/-- The first Cauchy-kernel jet is its actual real derivative on the radial interior. -/
theorem hasDerivAt_d4BMPlusPlusExactCauchyKernel
    (n : ℕ) (chi : ℂ) (t : ℝ) {z : ℝ}
    (hchi : chi.re ≠ 0) (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusExactCauchyKernel n chi t)
      (d4BMPlusPlusExactCauchyKernelDerivative n chi t z) z := by
  have hC := hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolution
    n chi hchi hz0 hz1
  have hR :=
    (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution
      n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have h :=
    ((hC.mul_const
      (d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))).sub
      (hR.mul_const
        (d4BMPlusPlusComplementaryHypergeometricSolution n chi t))).div_const
      (d4BMPlusPlusRegularComplementaryWronskian n chi t)
  simpa [d4BMPlusPlusExactCauchyKernel,
    d4BMPlusPlusExactCauchyKernelDerivative] using! h

/-- The second Cauchy-kernel jet differentiates the first on the radial interior. -/
theorem hasDerivAt_d4BMPlusPlusExactCauchyKernelDerivative
    (n : ℕ) (chi : ℂ) (t : ℝ) {z : ℝ}
    (hchi : chi.re ≠ 0) (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusExactCauchyKernelDerivative n chi t)
      (d4BMPlusPlusExactCauchyKernelSecondDerivative n chi t z) z := by
  have hC := hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolutionDerivative
    n chi hchi hz0 hz1
  have hR :=
    (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative
      n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have h :=
    ((hC.mul_const
      (d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))).sub
      (hR.mul_const
        (d4BMPlusPlusComplementaryHypergeometricSolution n chi t))).div_const
      (d4BMPlusPlusRegularComplementaryWronskian n chi t)
  simpa [d4BMPlusPlusExactCauchyKernelDerivative,
    d4BMPlusPlusExactCauchyKernelSecondDerivative] using! h

/-- Real restriction of the regular solution solves the exact BM jet. -/
theorem d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ))
      (d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ)) = 0 := by
  have h := d4BMPlusPlusRegularHypergeometricSolution_jet_eq_zero
    n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)
  rw [d4BMPlusPlusHypergeometricJet]
  push_cast
  exact h

/-- Cauchy kernel solves the homogeneous BM equation in its field variable. -/
theorem d4BMPlusPlusExactCauchyKernel_jet_eq_zero
    (n : ℕ) (chi : ℂ) (t : ℝ) {z : ℝ}
    (hchi : chi.re ≠ 0) (hz0 : 0 < z) (hz1 : z < 1)
    (hW : d4BMPlusPlusRegularComplementaryWronskian n chi t ≠ 0) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusExactCauchyKernel n chi t z)
      (d4BMPlusPlusExactCauchyKernelDerivative n chi t z)
      (d4BMPlusPlusExactCauchyKernelSecondDerivative n chi t z) = 0 := by
  have hC := d4BMPlusPlusComplementaryHypergeometricSolution_jet_eq_zero
    n chi hchi hz0 hz1
  have hR := d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero
    n chi hchi hz0 hz1
  rw [d4BMPlusPlusHypergeometricJet] at hC hR
  push_cast at hC hR
  rw [d4BMPlusPlusHypergeometricJet,
    d4BMPlusPlusExactCauchyKernel,
    d4BMPlusPlusExactCauchyKernelDerivative,
    d4BMPlusPlusExactCauchyKernelSecondDerivative]
  push_cast
  field_simp [hW]
  linear_combination
    d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) * hC -
      d4BMPlusPlusComplementaryHypergeometricSolution n chi t * hR

/-- Cauchy kernel vanishes on the source diagonal. -/
@[simp]
theorem d4BMPlusPlusExactCauchyKernel_diagonal
    (n : ℕ) (chi : ℂ) (t : ℝ) :
    d4BMPlusPlusExactCauchyKernel n chi t t = 0 := by
  rw [d4BMPlusPlusExactCauchyKernel]
  ring

/-- Exact unit integrating-factor derivative normalization on the source diagonal. -/
theorem d4BMPlusPlusExactCauchyKernel_weightedDerivative_diagonal
    (n : ℕ) (chi : ℂ) (t : ℝ)
    (hW : d4BMPlusPlusRegularComplementaryWronskian n chi t ≠ 0) :
    d4BMPlusPlusIntegratingFactor n chi t *
        d4BMPlusPlusExactCauchyKernelDerivative n chi t t = 1 := by
  rw [d4BMPlusPlusExactCauchyKernelDerivative]
  field_simp [hW]
  rw [d4BMPlusPlusRegularComplementaryWronskian]
  ring

/-- Every Xi fibre has exact unit local Cauchy normalization wherever its basis is nondegenerate. -/
theorem d4BMXiPlusPlusExactCauchyKernel_weightedDerivative_diagonal
    (n : ℕ) (q : XiZeroCopy) (t : ℝ)
    (hW : d4BMPlusPlusRegularComplementaryWronskian n
      (d4BMXiMixedHorizonAngularMomentum q) t ≠ 0) :
    d4BMPlusPlusIntegratingFactor n (d4BMXiMixedHorizonAngularMomentum q) t *
        d4BMPlusPlusExactCauchyKernelDerivative n
          (d4BMXiMixedHorizonAngularMomentum q) t t = 1 :=
  d4BMPlusPlusExactCauchyKernel_weightedDerivative_diagonal n _ t hW

end

end RHTower
