import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicOuterPolarizedReciprocity

/-!
# Complementary BM Gauss connection coefficient

Global Gauss summation and dominated Abel convergence identify forbidden/source AdS coefficient of
exact complementary horizon solution. Its Gamma quotient is nonzero whenever `chi.re != 0`, so
complementary projective response is finite. Exact connection determinant then proves regular and
complementary horizon lines have distinct projective AdS responses.

This closes projective-chart and denominator infrastructure. Retarded/advanced Einstein incidence
of two canonical horizon lines remains separate.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal


/-- Explicit Gamma quotient for forbidden AdS coefficient of complementary horizon solution. -/
def d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  Complex.Gamma (d4BMPlusPlusComplementaryHypergeometricC n chi) *
      Complex.Gamma (1 / 2 : ℂ) /
    (Complex.Gamma
        (d4BMPlusPlusComplementaryHypergeometricC n chi -
          d4BMPlusPlusComplementaryHypergeometricA n chi) *
      Complex.Gamma
        (d4BMPlusPlusComplementaryHypergeometricC n chi -
          d4BMPlusPlusComplementaryHypergeometricB n chi))

/-- Complementary Frobenius transform preserves positive Gauss gap `1/2`. -/
theorem d4BMPlusPlusComplementaryHypergeometric_gaussGap
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryHypergeometricC n chi -
        d4BMPlusPlusComplementaryHypergeometricA n chi -
        d4BMPlusPlusComplementaryHypergeometricB n chi = 1 / 2 := by
  rw [d4BMPlusPlusComplementaryHypergeometricA,
    d4BMPlusPlusComplementaryHypergeometricB,
    d4BMPlusPlusComplementaryHypergeometricC]
  have h := d4BMPlusPlusHypergeometric_gaussGap n chi
  linear_combination h

/-- Complementary Gauss parameters and endpoint complements avoid nonpositive integers. -/
theorem d4BMPlusPlusComplementaryGaussParameters_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (∀ j : ℕ, (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricA n chi) ∧
    (∀ j : ℕ, (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricB n chi) ∧
    (∀ j : ℕ, (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricC n chi) ∧
    (∀ j : ℕ, (j : ℂ) ≠
      -(d4BMPlusPlusComplementaryHypergeometricC n chi -
        d4BMPlusPlusComplementaryHypergeometricA n chi)) ∧
    (∀ j : ℕ, (j : ℂ) ≠
      -(d4BMPlusPlusComplementaryHypergeometricC n chi -
        d4BMPlusPlusComplementaryHypergeometricB n chi)) := by
  constructor
  · exact fun j =>
      (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
        n chi hchi j).1
  constructor
  · exact fun j =>
      (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
        n chi hchi j).2.1
  constructor
  · exact fun j =>
      (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
        n chi hchi j).2.2
  constructor
  · intro j hj
    have him := congrArg Complex.im hj
    rw [Complex.natCast_im, Complex.neg_im, Complex.sub_im,
      d4BMPlusPlusComplementaryHypergeometricC_im,
      d4BMPlusPlusComplementaryHypergeometricA_im] at him
    norm_num at him
    exact hchi (by linarith)
  · intro j hj
    have him := congrArg Complex.im hj
    rw [Complex.natCast_im, Complex.neg_im, Complex.sub_im,
      d4BMPlusPlusComplementaryHypergeometricC_im,
      d4BMPlusPlusComplementaryHypergeometricB_im] at him
    norm_num at him
    exact hchi (by linarith)

/-- Gauss sum of complementary coefficient series is explicit forbidden boundary coefficient. -/
theorem tsum_d4BMPlusPlusComplementaryHypergeometricCoefficient_eq_forbiddenBoundaryCoefficient
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ∑' j : ℕ, ordinaryHypergeometricCoefficient
        (d4BMPlusPlusComplementaryHypergeometricA n chi)
        (d4BMPlusPlusComplementaryHypergeometricB n chi)
        (d4BMPlusPlusComplementaryHypergeometricC n chi) j =
      d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient n chi := by
  let a := d4BMPlusPlusComplementaryHypergeometricA n chi
  let b := d4BMPlusPlusComplementaryHypergeometricB n chi
  let c := d4BMPlusPlusComplementaryHypergeometricC n chi
  rcases d4BMPlusPlusComplementaryGaussParameters_ne_negNat n chi hchi with
    ⟨ha, hb, hc, hca, hcb⟩
  have hgapEq : c - a - b = 1 / 2 := d4BMPlusPlusComplementaryHypergeometric_gaussGap n chi
  have hgap : 0 < (c - a - b).re := by rw [hgapEq]; norm_num
  have hgauss := gaussSummation a b c ha hb hc hca hcb hgap
  rw [GaussSummationFormula] at hgauss
  rw [hgauss, hgapEq]
  rfl

/-- Explicit complementary forbidden boundary Gamma quotient never vanishes off resonance. -/
theorem d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient n chi ≠ 0 := by
  rcases d4BMPlusPlusComplementaryGaussParameters_ne_negNat n chi hchi with
    ⟨_ha, _hb, hc, hca, hcb⟩
  rw [d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact Gamma_ne_zero_of_avoidsNegNat _ hc
    · apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
  · exact mul_ne_zero
      (Gamma_ne_zero_of_avoidsNegNat _ hca)
      (Gamma_ne_zero_of_avoidsNegNat _ hcb)

/-- Complementary Gauss factor has exact one-sided Abel boundary value. -/
theorem tendsto_d4BMPlusPlusComplementaryHypergeometricFactor_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun z : ℝ => d4BMPlusPlusComplementaryHypergeometricFactor n chi (z : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient n chi)) := by
  let a := d4BMPlusPlusComplementaryHypergeometricA n chi
  let b := d4BMPlusPlusComplementaryHypergeometricB n chi
  let c := d4BMPlusPlusComplementaryHypergeometricC n chi
  rcases d4BMPlusPlusComplementaryGaussParameters_ne_negNat n chi hchi with
    ⟨ha, hb, hc, _hca, _hcb⟩
  have hgapEq : c - a - b = 1 / 2 := d4BMPlusPlusComplementaryHypergeometric_gaussGap n chi
  have hgap : 0 < (c - a - b).re := by rw [hgapEq]; norm_num
  have h := tendsto_tsum_ordinaryHypergeometricCoefficient_mul_pow_one
    a b c ha hb hc hgap
  rw [tsum_d4BMPlusPlusComplementaryHypergeometricCoefficient_eq_forbiddenBoundaryCoefficient n chi hchi] at h
  simpa [d4BMPlusPlusComplementaryHypergeometricFactor,
    ordinaryHypergeometric, ordinaryHypergeometric_sum_eq,
    ordinaryHypergeometricCoefficient, smul_eq_mul, a, b, c] using h

/-- Full complementary solution has same exact one-sided forbidden boundary value. -/
theorem tendsto_d4BMPlusPlusComplementaryHypergeometricSolution_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
      (𝓝[<] (1 : ℝ))
      (𝓝 (d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient n chi)) := by
  have hlogR := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hlogC : ContinuousAt (fun z : ℝ => (Real.log z : ℂ)) 1 := by
    simpa only [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.comp hlogR
  have harg : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusComplementaryFrobeniusExponent n chi *
        (Real.log z : ℂ)) 1 := continuousAt_const.mul hlogC
  have hleadCont : ContinuousAt
      (d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi) 1 := by
    simpa only [d4BMPlusPlusLeadingComplementaryFrobeniusBranch,
      Function.comp_def] using!
        Complex.continuous_exp.continuousAt.comp harg
  have hlead : Tendsto
      (d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h := hleadCont.tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
    simpa [d4BMPlusPlusLeadingComplementaryFrobeniusBranch] using h
  have hfactor := tendsto_d4BMPlusPlusComplementaryHypergeometricFactor_one n chi hchi
  have hprod := hlead.mul hfactor
  simpa [d4BMPlusPlusComplementaryHypergeometricSolution] using! hprod

/-- Wronskian/Cramer complementary source coefficient equals explicit Gamma quotient. -/
theorem d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi =
      d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient n chi := by
  let CF := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi
  let CN := d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi
  have hC := tendsto_d4BMPlusPlusComplementaryHypergeometricSolution_one n chi hchi
  have hS := tendsto_d4BMPlusPlusAdSForbiddenSolution_one n chi hchi
  have hV := tendsto_d4BMPlusPlusAdSNormalizableSolution_one n chi hchi
  have hpos : ∀ᶠ z in 𝓝[<] (1 : ℝ), 0 < z := by
    have h : ∀ᶠ z in 𝓝 (1 : ℝ), 0 < z := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      d4BMPlusPlusComplementaryHypergeometricSolution n chi =ᶠ[𝓝[<] (1 : ℝ)]
      fun z : ℝ => CF * d4BMPlusPlusAdSForbiddenSolution n chi z +
        CN * d4BMPlusPlusAdSNormalizableSolution n chi z := by
    filter_upwards [self_mem_nhdsWithin, hpos] with z hz1 hz0
    exact (d4BMPlusPlusComplementaryAdSConnection_phase n chi hchi hz0 hz1).1
  have hCFconst : Tendsto (fun _ : ℝ => CF) (𝓝[<] (1 : ℝ)) (𝓝 CF) :=
    tendsto_const_nhds
  have hCNconst : Tendsto (fun _ : ℝ => CN) (𝓝[<] (1 : ℝ)) (𝓝 CN) :=
    tendsto_const_nhds
  have hright := (hCFconst.mul hS).add (hCNconst.mul hV)
  have hright' : Tendsto
      (fun z : ℝ => CF * d4BMPlusPlusAdSForbiddenSolution n chi z +
        CN * d4BMPlusPlusAdSNormalizableSolution n chi z)
      (𝓝[<] (1 : ℝ)) (𝓝 CF) := by
    simpa [CF, CN] using hright
  have hleft : Tendsto
      (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 CF) := hright'.congr' heq.symm
  exact tendsto_nhds_unique hleft hC

/-- Exact complementary horizon line lies in finite AdS source chart. -/
theorem d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi ≠ 0 := by
  rw [d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_eq n chi hchi]
  exact d4BMPlusPlusComplementaryForbiddenBoundaryCoefficient_ne_zero n chi hchi

/-- Finite projective AdS response of complementary horizon solution. -/
def d4BMPlusPlusComplementaryProjectiveBoundaryResponse
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi /
    d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi

/-- Exact response separation is normalized horizon-to-AdS connection determinant. -/
theorem d4BMPlusPlusComplementaryProjectiveResponse_sub_regular_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryProjectiveBoundaryResponse n chi -
        d4BMCausalProjectiveBoundaryResponse
          (d4BMCausalPlusPlusFrequency n chi) chi =
      (-2 * d4BMPlusPlusComplementaryFrobeniusExponent n chi) /
        (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi) := by
  have hA := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  have hAc := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  rw [d4BMPlusPlusComplementaryProjectiveBoundaryResponse,
    ← d4BMPlusPlusRegularAdSConnectionCoefficient_ratio_eq_projectiveResponse
      n chi hchi]
  have hdet := d4BMPlusPlusAdSConnectionDet_eq n chi hchi
  field_simp [hA, hAc]
  linear_combination hdet

/-- Regular and complementary horizon lines select distinct finite AdS responses. -/
theorem d4BMPlusPlusComplementaryProjectiveResponse_ne_regular
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusComplementaryProjectiveBoundaryResponse n chi ≠
      d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalPlusPlusFrequency n chi) chi := by
  intro h
  have hsub := d4BMPlusPlusComplementaryProjectiveResponse_sub_regular_eq n chi hchi
  rw [h, sub_self] at hsub
  have hA := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  have hAc := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  have hden := mul_ne_zero hA hAc
  have hnum : -2 * d4BMPlusPlusComplementaryFrobeniusExponent n chi ≠ 0 :=
    mul_ne_zero (by norm_num)
      (d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n chi hchi)
  exact (div_ne_zero hnum hden) hsub.symm

end

end RHTower
