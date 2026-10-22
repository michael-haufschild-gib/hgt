import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicExactConnectionMatrix

/-!
# Gauss identification of exact BM connection data

Absolute convergence gives a one-sided Abel limit for the regular hypergeometric series.  The exact
AdS basis tends to `(1, 0)` at the boundary, so uniqueness of limits identifies the Wronskian-defined
forbidden/source coefficient with the explicit Birmingham--Mokhtari Gamma coefficient.
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory

namespace RHTower
noncomputable section

theorem tendsto_tsum_ordinaryHypergeometricCoefficient_mul_pow_one
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : 0 < (c - a - b).re) :
    Tendsto
      (fun z : ℝ => ∑' j : ℕ,
        ordinaryHypergeometricCoefficient a b c j * (z : ℂ) ^ j)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j)) := by
  have hsum := summable_ordinaryHypergeometricCoefficient_of_re_gap_pos
    a b c ha hb hc hgap
  refine tendsto_tsum_of_dominated_convergence hsum.norm (fun j => ?_) ?_
  · have hcont : ContinuousAt
        (fun z : ℝ => ordinaryHypergeometricCoefficient a b c j * (z : ℂ) ^ j) 1 := by
      fun_prop
    have ht := hcont.tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
    simpa using ht
  · have hpos : ∀ᶠ z in 𝓝[<] (1 : ℝ), 0 < z := by
      have h : ∀ᶠ z in 𝓝 (1 : ℝ), 0 < z := Ioi_mem_nhds (by norm_num)
      exact h.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hpos] with z hz1 hz0 j
    rw [norm_mul, norm_pow]
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      norm_num [abs_of_pos hz0]
      exact le_of_lt hz1
    calc
      ‖ordinaryHypergeometricCoefficient a b c j‖ * ‖(z : ℂ)‖ ^ j ≤
          ‖ordinaryHypergeometricCoefficient a b c j‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hzle) (norm_nonneg _)
      _ = ‖ordinaryHypergeometricCoefficient a b c j‖ := mul_one _

theorem tendsto_d4BMPlusPlusRegularHypergeometricSolution_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (d4BMCausalForbiddenBoundaryCoefficient
        (d4BMCausalPlusPlusFrequency n chi) chi)) := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  have hp (j : ℕ) := d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j
  have ha : ∀ j : ℕ, (j : ℂ) ≠ -a := fun j => (hp j).1
  have hb : ∀ j : ℕ, (j : ℂ) ≠ -b := fun j => (hp j).2.1
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := fun j => (hp j).2.2
  have hgapEq : c - a - b = 1 / 2 :=
    d4BMPlusPlusHypergeometric_gaussGap n chi
  have hgap : 0 < (c - a - b).re := by
    rw [hgapEq]
    norm_num
  have h := tendsto_tsum_ordinaryHypergeometricCoefficient_mul_pow_one
    a b c ha hb hc hgap
  rw [tsum_d4BMPlusPlusRegularHypergeometricCoefficient_eq_forbiddenBoundaryCoefficient
    n chi hchi] at h
  simpa [d4BMPlusPlusRegularHypergeometricSolution,
    d4BMPlusPlusRegularHypergeometricSeries,
    ordinaryHypergeometric_sum_eq, smul_eq_mul] using h

theorem tendsto_d4BMPlusPlusAdSForbiddenSolution_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto (d4BMPlusPlusAdSForbiddenSolution n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hS0 := (hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFactor
    n chi 0 hchi (by simp)).continuousAt
  have hw : ContinuousAt (fun z : ℝ => ((1 - z : ℝ) : ℂ)) 1 := by fun_prop
  have hS : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hS0.comp_of_eq hw (by norm_num)
  have ht := hS.tendsto.mono_left
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
  change Tendsto
    (fun z : ℝ => d4BMPlusPlusAdSForbiddenHypergeometricFactor n chi
      ((1 - z : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ))
  simpa only [sub_self, Complex.ofReal_zero,
    d4BMPlusPlusAdSForbiddenHypergeometricFactor_zero] using ht

theorem tendsto_d4BMPlusPlusAdSNormalizableSolution_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto (d4BMPlusPlusAdSNormalizableSolution n chi)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hV0 := (hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    n chi 0 hchi (by simp)).continuousAt
  have hw : ContinuousAt (fun z : ℝ => ((1 - z : ℝ) : ℂ)) 1 := by fun_prop
  have hV : ContinuousAt
      (fun z : ℝ => d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
        ((1 - z : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hV0.comp_of_eq hw (by norm_num)
  have htV := hV.tendsto.mono_left
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
  have hsqrt : ContinuousAt (fun z : ℝ => (Real.sqrt (1 - z) : ℂ)) 1 := by
    fun_prop
  have htsqrt := hsqrt.tendsto.mono_left
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
  have htsqrt0 : Tendsto (fun z : ℝ => (Real.sqrt (1 - z) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using htsqrt
  have hlead : Tendsto d4BMPlusPlusAdSLeadingNormalizableBranch
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    apply htsqrt0.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (d4BMPlusPlusAdSLeadingNormalizableBranch_eq_sqrt hz).symm
  have hprod := hlead.mul htV
  change Tendsto
    (fun z : ℝ => d4BMPlusPlusAdSLeadingNormalizableBranch z *
      d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
        ((1 - z : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ))
  simpa only [zero_mul] using hprod

theorem d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi =
      d4BMCausalForbiddenBoundaryCoefficient
        (d4BMCausalPlusPlusFrequency n chi) chi := by
  let CF := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi
  let CN := d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi
  have hR := tendsto_d4BMPlusPlusRegularHypergeometricSolution_one n chi hchi
  have hF := tendsto_d4BMPlusPlusAdSForbiddenSolution_one n chi hchi
  have hN := tendsto_d4BMPlusPlusAdSNormalizableSolution_one n chi hchi
  have hpos : ∀ᶠ z in 𝓝[<] (1 : ℝ), 0 < z := by
    have h : ∀ᶠ z in 𝓝 (1 : ℝ), 0 < z := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)) =ᶠ[
        𝓝[<] (1 : ℝ)]
      (fun z : ℝ => CF * d4BMPlusPlusAdSForbiddenSolution n chi z +
        CN * d4BMPlusPlusAdSNormalizableSolution n chi z) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with z hz1 hz0
    exact (d4BMPlusPlusRegularAdSConnection_phase n chi hchi hz0 hz1).1
  have hCF : Tendsto
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 CF) := by
    have hCFconst : Tendsto (fun _ : ℝ => CF) (𝓝[<] (1 : ℝ)) (𝓝 CF) :=
      tendsto_const_nhds
    have hCNconst : Tendsto (fun _ : ℝ => CN) (𝓝[<] (1 : ℝ)) (𝓝 CN) :=
      tendsto_const_nhds
    have hright := (hCFconst.mul hF).add (hCNconst.mul hN)
    have hright' : Tendsto
        (fun z : ℝ => CF * d4BMPlusPlusAdSForbiddenSolution n chi z +
          CN * d4BMPlusPlusAdSNormalizableSolution n chi z)
        (𝓝[<] (1 : ℝ)) (𝓝 CF) := by
      simpa [CF, CN] using hright
    exact hright'.congr' heq.symm
  exact tendsto_nhds_unique hCF hR

end
end RHTower

