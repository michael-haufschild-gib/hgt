import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicExactCauchyKernel

/-!
# Exact BM second-harmonic Wronskian conservation

The exact regular and complementary BM solutions obey the same divergence-form radial equation.
Their normalized Wronskian therefore has zero derivative throughout the radial interior. Connectedness
and the exact horizon limit identify its global value with the complementary Frobenius exponent.
Thus no interior conjugate point obstructs the exact Cauchy kernel on any nonresonant Xi fibre.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Normalized Wronskian of two candidate BM solution jets. -/
def d4BMPlusPlusNormalizedWronskian
    (n : ℕ) (chi : ℂ) (y dy v dv : ℝ → ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingFactor n chi z * (y z * dv z - dy z * v z)

/-- Any two actual solution jets of the same BM equation have zero normalized-Wronskian
derivative. This is Abel's identity in the corpus BM integrating-factor normalization. -/
theorem hasDerivAt_d4BMPlusPlusNormalizedWronskian_of_solutionJets
    (n : ℕ) (chi : ℂ) (y dy ddy v dv ddv : ℝ → ℂ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hy : HasDerivAt y (dy z) z) (hdy : HasDerivAt dy (ddy z) z)
    (hv : HasDerivAt v (dv z) z) (hdv : HasDerivAt dv (ddv z) z)
    (hyjet : d4BMPlusPlusHypergeometricJet n chi z
      (y z) (dy z) (ddy z) = 0)
    (hvjet : d4BMPlusPlusHypergeometricJet n chi z
      (v z) (dv z) (ddv z) = 0) :
    HasDerivAt (d4BMPlusPlusNormalizedWronskian n chi y dy v dv) 0 z := by
  let p := d4BMPlusPlusIntegratingFactor n chi
  let pd := fun x : ℝ =>
    d4BMPlusPlusIntegratingWeight n chi x *
      d4BMPlusPlusHypergeometricDrift n chi x
  let qpot := fun x : ℝ =>
    d4BMPlusPlusIntegratingWeight n chi x *
      d4BMPlusPlusHypergeometricPotential n chi
  have hp : HasDerivAt p (pd z) z :=
    hasDerivAt_d4BMPlusPlusIntegratingFactor n chi hz0 hz1
  have hydiv : pd z * dy z + p z * ddy z - qpot z * y z = 0 := by
    calc
      pd z * dy z + p z * ddy z - qpot z * y z =
          d4BMPlusPlusIntegratingWeight n chi z *
            d4BMPlusPlusHypergeometricJet n chi z (y z) (dy z) (ddy z) := by
              simpa [p, pd, qpot] using
                (d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
                  n chi hz0 hz1 (y z) (dy z) (ddy z)).symm
      _ = 0 := by rw [hyjet, mul_zero]
  have hvdiv : pd z * dv z + p z * ddv z - qpot z * v z = 0 := by
    calc
      pd z * dv z + p z * ddv z - qpot z * v z =
          d4BMPlusPlusIntegratingWeight n chi z *
            d4BMPlusPlusHypergeometricJet n chi z (v z) (dv z) (ddv z) := by
              simpa [p, pd, qpot] using
                (d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
                  n chi hz0 hz1 (v z) (dv z) (ddv z)).symm
      _ = 0 := by rw [hvjet, mul_zero]
  have hzero :
      pd z * (y z * dv z - dy z * v z) +
          p z * ((dy z * dv z + y z * ddv z) -
            (ddy z * v z + dy z * dv z)) = 0 := by
    linear_combination y z * hvdiv - v z * hydiv
  have hW := hp.mul ((hy.mul hdv).sub (hdy.mul hv))
  have hW0 := hW.congr_deriv hzero
  simpa [d4BMPlusPlusNormalizedWronskian, p, pd] using! hW0

/-- The exact normalized regular/complementary Wronskian has zero radial derivative. -/
theorem hasDerivAt_d4BMPlusPlusRegularComplementaryWronskian
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusRegularComplementaryWronskian n chi) 0 z := by
  let R := fun x : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ)
  let Rd := fun x : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)
  let Rdd := fun x : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ)
  let C := d4BMPlusPlusComplementaryHypergeometricSolution n chi
  let Cd := d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi
  let Cdd := d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi
  let p := d4BMPlusPlusIntegratingFactor n chi
  let pd := fun x : ℝ =>
    d4BMPlusPlusIntegratingWeight n chi x *
      d4BMPlusPlusHypergeometricDrift n chi x
  let v := fun x : ℝ =>
    d4BMPlusPlusIntegratingWeight n chi x *
      d4BMPlusPlusHypergeometricPotential n chi
  have hp : HasDerivAt p (pd z) z :=
    hasDerivAt_d4BMPlusPlusIntegratingFactor n chi hz0 hz1
  have hR : HasDerivAt R (Rd z) z := by
    simpa [R, Rd] using!
      (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution
        n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have hRd : HasDerivAt Rd (Rdd z) z := by
    simpa [Rd, Rdd] using!
      (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative
        n chi (z : ℂ) hchi (enorm_ofReal_lt_one hz0 hz1)).comp_ofReal
  have hC : HasDerivAt C (Cd z) z := by
    simpa [C, Cd] using!
      hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolution
        n chi hchi hz0 hz1
  have hCd : HasDerivAt Cd (Cdd z) z := by
    simpa [Cd, Cdd] using!
      hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolutionDerivative
        n chi hchi hz0 hz1
  have hRjet :
      d4BMPlusPlusHypergeometricJet n chi z (R z) (Rd z) (Rdd z) = 0 := by
    simpa [R, Rd, Rdd] using
      d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero
        n chi hchi hz0 hz1
  have hCjet :
      d4BMPlusPlusHypergeometricJet n chi z (C z) (Cd z) (Cdd z) = 0 := by
    simpa [C, Cd, Cdd] using
      d4BMPlusPlusComplementaryHypergeometricSolution_jet_eq_zero
        n chi hchi hz0 hz1
  have hRdiv : pd z * Rd z + p z * Rdd z - v z * R z = 0 := by
    calc
      pd z * Rd z + p z * Rdd z - v z * R z =
          d4BMPlusPlusIntegratingWeight n chi z *
            d4BMPlusPlusHypergeometricJet n chi z (R z) (Rd z) (Rdd z) := by
              simpa [p, pd, v] using
                (d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
                  n chi hz0 hz1 (R z) (Rd z) (Rdd z)).symm
      _ = 0 := by rw [hRjet, mul_zero]
  have hCdiv : pd z * Cd z + p z * Cdd z - v z * C z = 0 := by
    calc
      pd z * Cd z + p z * Cdd z - v z * C z =
          d4BMPlusPlusIntegratingWeight n chi z *
            d4BMPlusPlusHypergeometricJet n chi z (C z) (Cd z) (Cdd z) := by
              simpa [p, pd, v] using
                (d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
                  n chi hz0 hz1 (C z) (Cd z) (Cdd z)).symm
      _ = 0 := by rw [hCjet, mul_zero]
  have hzero :
      pd z * (R z * Cd z - Rd z * C z) +
          p z * ((Rd z * Cd z + R z * Cdd z) -
            (Rdd z * C z + Rd z * Cd z)) = 0 := by
    linear_combination R z * hCdiv - C z * hRdiv
  have hW := hp.mul ((hR.mul hCd).sub (hRd.mul hC))
  have hW0 := hW.congr_deriv hzero
  simpa [d4BMPlusPlusRegularComplementaryWronskian, R, Rd, Rdd, C, Cd, Cdd,
    p, pd] using! hW0

/-- The normalized Wronskian is constant on the connected radial interior. -/
theorem d4BMPlusPlusRegularComplementaryWronskian_eq_of_mem_Ioo
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusRegularComplementaryWronskian n chi x =
      d4BMPlusPlusRegularComplementaryWronskian n chi y := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusRegularComplementaryWronskian
      n chi hchi hz.1 hz.2).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusRegularComplementaryWronskian
      n chi hchi hz.1 hz.2).deriv
  · exact hx
  · exact hy

/-- Horizon normalization fixes the exact Wronskian globally on `0 < z < 1`. -/
theorem d4BMPlusPlusRegularComplementaryWronskian_eq_exponent
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularComplementaryWronskian n chi z =
      d4BMPlusPlusComplementaryFrobeniusExponent n chi := by
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := by
    have h : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      d4BMPlusPlusRegularComplementaryWronskian n chi =ᶠ[𝓝[>] (0 : ℝ)]
        fun _ => d4BMPlusPlusRegularComplementaryWronskian n chi z := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 ht1
    exact d4BMPlusPlusRegularComplementaryWronskian_eq_of_mem_Ioo
      n chi hchi ⟨ht0, ht1⟩ ⟨hz0, hz1⟩
  have hconst : Tendsto (d4BMPlusPlusRegularComplementaryWronskian n chi)
      (𝓝[>] (0 : ℝ))
      (𝓝 (d4BMPlusPlusRegularComplementaryWronskian n chi z)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hconst
    (tendsto_d4BMPlusPlusRegularComplementaryWronskian_zero n chi hchi)

/-- No interior conjugate point occurs for the exact nonresonant horizon basis. -/
theorem d4BMPlusPlusRegularComplementaryWronskian_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularComplementaryWronskian n chi z ≠ 0 := by
  rw [d4BMPlusPlusRegularComplementaryWronskian_eq_exponent n chi hchi hz0 hz1]
  exact d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n chi hchi

/-- Every Xi fibre has a globally nondegenerate exact basis on the radial interior. -/
theorem d4BMXiPlusPlusRegularComplementaryWronskian_ne_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularComplementaryWronskian n
      (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 :=
  d4BMPlusPlusRegularComplementaryWronskian_ne_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1

/-- Exact Cauchy kernel solves the BM equation at every interior source radius. -/
theorem d4BMPlusPlusExactCauchyKernel_jet_eq_zero_global
    (n : ℕ) (chi : ℂ) {t z : ℝ} (hchi : chi.re ≠ 0)
    (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusExactCauchyKernel n chi t z)
      (d4BMPlusPlusExactCauchyKernelDerivative n chi t z)
      (d4BMPlusPlusExactCauchyKernelSecondDerivative n chi t z) = 0 :=
  d4BMPlusPlusExactCauchyKernel_jet_eq_zero n chi t hchi hz0 hz1
    (d4BMPlusPlusRegularComplementaryWronskian_ne_zero n chi hchi ht0 ht1)

/-- Exact Cauchy kernel has unit diagonal jump at every interior source radius. -/
theorem d4BMPlusPlusExactCauchyKernel_weightedDerivative_diagonal_global
    (n : ℕ) (chi : ℂ) {t : ℝ} (hchi : chi.re ≠ 0)
    (ht0 : 0 < t) (ht1 : t < 1) :
    d4BMPlusPlusIntegratingFactor n chi t *
        d4BMPlusPlusExactCauchyKernelDerivative n chi t t = 1 :=
  d4BMPlusPlusExactCauchyKernel_weightedDerivative_diagonal n chi t
    (d4BMPlusPlusRegularComplementaryWronskian_ne_zero n chi hchi ht0 ht1)

end

end RHTower
