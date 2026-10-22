import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicExactAdSNormalizableSolution

/-!
# Exact BM second-harmonic AdS outer basis

The constant and square-root AdS Frobenius branches have normalized Wronskian `-1/2`. Exact
endpoint expansion proves this limit; Abel conservation propagates it through `0<z<1`. Thus the
actual outer source/normalizable basis is globally nondegenerate on every nonresonant Xi fibre.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- On `z<1`, the exponential half-log branch is the positive real square root. -/
theorem d4BMPlusPlusAdSLeadingNormalizableBranch_eq_sqrt
    {z : ℝ} (hz1 : z < 1) :
    d4BMPlusPlusAdSLeadingNormalizableBranch z =
      (Real.sqrt (1 - z) : ℂ) := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  rw [d4BMPlusPlusAdSLeadingNormalizableBranch]
  calc
    Complex.exp ((1 / 2 : ℂ) * (Real.log (1 - z) : ℂ)) =
        ((Real.exp (Real.log (1 - z) / 2) : ℝ) : ℂ) := by
          rw [show
            (1 / 2 : ℂ) * (Real.log (1 - z) : ℂ) =
              ((Real.log (1 - z) / 2 : ℝ) : ℂ) by
                push_cast
                ring]
          rw [← Complex.ofReal_exp]
    _ = (Real.sqrt (1 - z) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hw0]
      congr 2
      ring

/-- Integrating-factor Wronskian of the exact constant and normalizable AdS branches. -/
def d4BMPlusPlusAdSOuterWronskian
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
    (d4BMPlusPlusAdSForbiddenSolution n chi)
    (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi)
    (d4BMPlusPlusAdSNormalizableSolution n chi)
    (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi) z

/-- Exact endpoint-friendly expansion of the outer normalized Wronskian. -/
theorem d4BMPlusPlusAdSOuterWronskian_eq
    (n : ℕ) (chi : ℂ) {z : ℝ} (_hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusAdSOuterWronskian n chi z =
      Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        (-(1 / 2 : ℂ) *
              d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
                ((1 - z : ℝ) : ℂ) *
              d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
                ((1 - z : ℝ) : ℂ) +
          ((1 - z : ℝ) : ℂ) *
            (d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
                  ((1 - z : ℝ) : ℂ) *
                d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
                  ((1 - z : ℝ) : ℂ) -
              d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
                  ((1 - z : ℝ) : ℂ) *
                d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
                  ((1 - z : ℝ) : ℂ))) := by
  have hw0 : 0 < 1 - z := sub_pos.mpr hz1
  have hw : 1 - z ≠ 0 := ne_of_gt hw0
  have hwC : ((1 - z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  have hsqrtSq : (Real.sqrt (1 - z) : ℂ) ^ 2 = ((1 - z : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hw0.le
  rw [d4BMPlusPlusAdSOuterWronskian,
    d4BMPlusPlusNormalizedWronskian,
    d4BMPlusPlusAdSForbiddenSolution,
    d4BMPlusPlusAdSForbiddenSolutionDerivative,
    d4BMPlusPlusAdSNormalizableSolution,
    d4BMPlusPlusAdSNormalizableSolutionDerivative,
    d4BMPlusPlusIntegratingFactor,
    d4BMPlusPlusAdSLeadingNormalizableBranchDerivative,
    d4BMPlusPlusAdSLeadingNormalizableBranch_eq_sqrt hz1]
  field_simp [hwC]
  rw [hsqrtSq]
  ring

/-- Outer normalized Wronskian has zero derivative throughout the radial interior. -/
theorem hasDerivAt_d4BMPlusPlusAdSOuterWronskian
    (n : ℕ) (chi : ℂ) {z : ℝ} (hchi : chi.re ≠ 0)
    (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSOuterWronskian n chi) 0 z := by
  simpa [d4BMPlusPlusAdSOuterWronskian] using!
    hasDerivAt_d4BMPlusPlusNormalizedWronskian_of_solutionJets n chi
      (d4BMPlusPlusAdSForbiddenSolution n chi)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi)
      (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi)
      (d4BMPlusPlusAdSNormalizableSolution n chi)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi)
      (d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi)
      hz0 hz1
      (hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hz0 hz1)
      (hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative n chi hchi hz0 hz1)
      (hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hz0 hz1)
      (hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi hz0 hz1)
      (d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n chi hchi hz0 hz1)
      (d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hz0 hz1)

/-- Exact outer Wronskian normalization at the AdS endpoint. -/
theorem tendsto_d4BMPlusPlusAdSOuterWronskian_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto (d4BMPlusPlusAdSOuterWronskian n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 (-(1 / 2 : ℂ))) := by
  let g := fun z : ℝ =>
    Complex.exp
        (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
          (Real.log z : ℂ)) *
      (-(1 / 2 : ℂ) *
            d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
              ((1 - z : ℝ) : ℂ) *
            d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
              ((1 - z : ℝ) : ℂ) +
        ((1 - z : ℝ) : ℂ) *
          (d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
                ((1 - z : ℝ) : ℂ) *
              d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
                ((1 - z : ℝ) : ℂ) -
            d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
                ((1 - z : ℝ) : ℂ) *
              d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
                ((1 - z : ℝ) : ℂ)))
  have hS0 := (hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFactor
    n chi 0 hchi (by simp)).continuousAt
  have hSd0 := (hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative
    n chi 0 hchi (by simp)).continuousAt
  have hV0 := (hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    n chi 0 hchi (by simp)).continuousAt
  have hVd0 := (hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative
    n chi 0 hchi (by simp)).continuousAt
  have hw : ContinuousAt (fun z : ℝ => ((1 - z : ℝ) : ℂ)) 1 := by fun_prop
  have hS : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hS0.comp_of_eq hw (by norm_num)
  have hSd : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hSd0.comp_of_eq hw (by norm_num)
  have hV : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hV0.comp_of_eq hw (by norm_num)
  have hVd : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSNormalizableHypergeometricFirstDerivative n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hVd0.comp_of_eq hw (by norm_num)
  have hlogC : ContinuousAt (fun z : ℝ => (Real.log z : ℂ)) 1 := by
    have hlogR := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.comp hlogR
  have hE : ContinuousAt
      (fun z : ℝ => Complex.exp
        (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
          (Real.log z : ℂ))) 1 := by
    have harg : ContinuousAt
        (fun z : ℝ =>
          d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) 1 := continuousAt_const.mul hlogC
    simpa only [Function.comp_def] using
      Complex.continuous_exp.continuousAt.comp harg
  have hg : ContinuousAt g 1 := by
    dsimp only [g]
    fun_prop
  have ht : Tendsto g (𝓝 (1 : ℝ)) (𝓝 (-(1 / 2 : ℂ))) := by
    simpa [g] using hg.tendsto
  have hpos : ∀ᶠ z in 𝓝[<] (1 : ℝ), 0 < z := by
    have h : ∀ᶠ z in 𝓝 (1 : ℝ), 0 < z := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      d4BMPlusPlusAdSOuterWronskian n chi =ᶠ[𝓝[<] (1 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin, hpos] with z hz1 hz0
    exact d4BMPlusPlusAdSOuterWronskian_eq n chi hz0 hz1
  exact (ht.mono_left inf_le_left).congr' heq.symm

/-- Outer normalized Wronskian is constant on the connected radial interior. -/
theorem d4BMPlusPlusAdSOuterWronskian_eq_of_mem_Ioo
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusAdSOuterWronskian n chi x =
      d4BMPlusPlusAdSOuterWronskian n chi y := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusAdSOuterWronskian
      n chi hchi hz.1 hz.2).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusAdSOuterWronskian
      n chi hchi hz.1 hz.2).deriv
  · exact hx
  · exact hy

/-- Endpoint normalization fixes the outer Wronskian globally to `-1/2`. -/
theorem d4BMPlusPlusAdSOuterWronskian_eq_neg_half
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusAdSOuterWronskian n chi z = -(1 / 2 : ℂ) := by
  have hpos : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t := by
    have h : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      d4BMPlusPlusAdSOuterWronskian n chi =ᶠ[𝓝[<] (1 : ℝ)]
        fun _ => d4BMPlusPlusAdSOuterWronskian n chi z := by
    filter_upwards [self_mem_nhdsWithin, hpos] with t ht1 ht0
    exact d4BMPlusPlusAdSOuterWronskian_eq_of_mem_Ioo
      n chi hchi ⟨ht0, ht1⟩ ⟨hz0, hz1⟩
  have hconst : Tendsto (d4BMPlusPlusAdSOuterWronskian n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 (d4BMPlusPlusAdSOuterWronskian n chi z)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hconst
    (tendsto_d4BMPlusPlusAdSOuterWronskian_one n chi hchi)

/-- Exact outer source/normalizable basis is nondegenerate everywhere in the radial interior. -/
theorem d4BMPlusPlusAdSOuterWronskian_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusAdSOuterWronskian n chi z ≠ 0 := by
  rw [d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi hz0 hz1]
  norm_num

/-- Every Xi fibre has a globally nondegenerate exact AdS outer basis. -/
theorem d4BMXiPlusPlusAdSOuterWronskian_ne_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusAdSOuterWronskian n
      (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 :=
  d4BMPlusPlusAdSOuterWronskian_ne_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1

end

end RHTower
