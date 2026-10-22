import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicRegularSolution

/-!
# Exact BM second-harmonic horizon basis

The horizon-regular and complementary full solutions have an exact integrating-factor Wronskian.
Frobenius exponent balance reduces it to analytic factors and proves its horizon limit is
`lambda = 4n+3+2i chi`, nonzero whenever `chi.re != 0`. Thus every Xi fibre has a genuine
nondegenerate local solution basis; retarded/advanced endpoint incidence remains separate data.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact cancellation of integrating and complementary Frobenius powers. -/
theorem d4BMPlusPlusIntegratingFactor_mul_leadingComplementaryBranch_eq
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz : 0 < z) :
    d4BMPlusPlusIntegratingFactor n chi z *
        d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z =
      (z : ℂ) * (Real.sqrt (1 - z) : ℂ) := by
  rw [d4BMPlusPlusIntegratingFactor,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch]
  have hsum :
      d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
          (Real.log z : ℂ) +
        d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          (Real.log z : ℂ) = (Real.log z : ℂ) := by
    rw [d4BMPlusPlusComplementaryFrobeniusExponent]
    ring
  have hexp :
      Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        Complex.exp
          (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
            (Real.log z : ℂ)) = (z : ℂ) := by
    rw [← Complex.exp_add, hsum, ← Complex.ofReal_exp, Real.exp_log hz]
  calc
    Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        (Real.sqrt (1 - z) : ℂ) *
          Complex.exp
            (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
              (Real.log z : ℂ)) =
      (Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        Complex.exp
          (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
            (Real.log z : ℂ))) *
        (Real.sqrt (1 - z) : ℂ) := by ring
    _ = _ := by rw [hexp]

/-- Full integrating-factor Wronskian of regular and complementary exact solutions. -/
def d4BMPlusPlusRegularComplementaryWronskian
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingFactor n chi z *
    (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
        d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z -
      d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
        d4BMPlusPlusComplementaryHypergeometricSolution n chi z)

/-- Exact full Wronskian expansion in regular hypergeometric factors. -/
theorem d4BMPlusPlusRegularComplementaryWronskian_eq
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz : 0 < z) :
    d4BMPlusPlusRegularComplementaryWronskian n chi z =
      d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) *
          d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          (Real.sqrt (1 - z) : ℂ) +
        (z : ℂ) * (Real.sqrt (1 - z) : ℂ) *
          (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) -
            d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)) := by
  have hW := d4BMPlusPlusLeadingFrobeniusWronskian_eq n chi hz
  have hP := d4BMPlusPlusIntegratingFactor_mul_leadingComplementaryBranch_eq n chi hz
  rw [d4BMPlusPlusLeadingFrobeniusWronskian] at hW
  rw [d4BMPlusPlusRegularComplementaryWronskian,
    d4BMPlusPlusComplementaryHypergeometricSolutionDerivative,
    d4BMPlusPlusComplementaryHypergeometricSolution]
  calc
    _ =
      d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) *
          (d4BMPlusPlusIntegratingFactor n chi z *
            d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z) +
        (d4BMPlusPlusIntegratingFactor n chi z *
          d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z) *
          (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) -
            d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)) := by ring
    _ = _ := by
      rw [hW, hP]
      ring

/-- The exact full regular/complementary Wronskian tends to the nonresonant exponent. -/
theorem tendsto_d4BMPlusPlusRegularComplementaryWronskian_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto (d4BMPlusPlusRegularComplementaryWronskian n chi)
      (𝓝[>] 0)
      (𝓝 (d4BMPlusPlusComplementaryFrobeniusExponent n chi)) := by
  let g := fun z : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ) *
          d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          (Real.sqrt (1 - z) : ℂ) +
        (z : ℂ) * (Real.sqrt (1 - z) : ℂ) *
          (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ) -
            d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
              d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ))
  have hRComplex :
      ContinuousAt (d4BMPlusPlusRegularHypergeometricSolution n chi) 0 :=
    (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution
      n chi 0 hchi (by simp)).continuousAt
  have hRdComplex :
      ContinuousAt (d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi) 0 :=
    (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative
      n chi 0 hchi (by simp)).continuousAt
  have hFComplex :
      ContinuousAt (d4BMPlusPlusComplementaryHypergeometricFactor n chi) 0 :=
    continuousAt_d4BMPlusPlusComplementaryHypergeometricFactor_zero n chi hchi
  have hFdComplex :
      ContinuousAt (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi) 0 :=
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFirstDerivative
      n chi 0 hchi (by simp)).continuousAt
  have hR : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)) 0 :=
    by simpa only [Function.comp_def] using
      hRComplex.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hRd : ContinuousAt
      (fun z : ℝ =>
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ)) 0 :=
    by simpa only [Function.comp_def] using
      hRdComplex.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hF : ContinuousAt
      (fun z : ℝ =>
        d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ)) 0 :=
    by simpa only [Function.comp_def] using
      hFComplex.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hFd : ContinuousAt
      (fun z : ℝ =>
        d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi (z : ℂ)) 0 :=
    by simpa only [Function.comp_def] using
      hFdComplex.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hg : ContinuousAt g 0 := by
    dsimp only [g]
    fun_prop
  have ht : Tendsto g (𝓝 0)
      (𝓝 (d4BMPlusPlusComplementaryFrobeniusExponent n chi)) := by
    simpa [g] using hg.tendsto
  have heq :
      d4BMPlusPlusRegularComplementaryWronskian n chi =ᶠ[𝓝[Set.Ioi 0] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact d4BMPlusPlusRegularComplementaryWronskian_eq n chi hz
  exact (ht.mono_left inf_le_left).congr' heq.symm

/-- The full horizon basis normalization is nonzero for nonzero angular real part. -/
theorem d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryFrobeniusExponent n chi ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMPlusPlusComplementaryFrobeniusExponent_eq] at him
  norm_num [Complex.mul_im] at him
  exact hchi (by linarith)

/-- Every Xi fibre has a nonzero exact regular/complementary horizon Wronskian limit. -/
theorem d4BMXiPlusPlusRegularComplementaryWronskian_limit_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMPlusPlusComplementaryFrobeniusExponent n
        (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 :=
  d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- The exact regular/complementary basis is nondegenerate on a punctured horizon neighborhood. -/
theorem eventually_d4BMPlusPlusRegularComplementaryWronskian_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∀ᶠ z in 𝓝[>] (0 : ℝ),
      d4BMPlusPlusRegularComplementaryWronskian n chi z ≠ 0 := by
  have ht := tendsto_d4BMPlusPlusRegularComplementaryWronskian_zero n chi hchi
  exact ht.eventually (eventually_ne_nhds
    (d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n chi hchi))

/-- Every Xi fibre has a nondegenerate exact local horizon basis. -/
theorem eventually_d4BMXiPlusPlusRegularComplementaryWronskian_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    ∀ᶠ z in 𝓝[>] (0 : ℝ),
      d4BMPlusPlusRegularComplementaryWronskian n
        (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 :=
  eventually_d4BMPlusPlusRegularComplementaryWronskian_ne_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

end

end RHTower
