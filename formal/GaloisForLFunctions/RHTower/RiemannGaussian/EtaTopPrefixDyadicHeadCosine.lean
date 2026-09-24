import GaloisForLFunctions.RHTower.RiemannGaussian.EtaTopPrefixDyadicLeadingFlux
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyLeadingFluxKernelFactorization

/-!
# The multiplicity-one dyadic eta obstruction is a Fourier-cosine sign

The new-head kernel has one cosine phase and one horizontal-tilt bracket.
Its exact integral is the isolated leading current.  At a hypothetical
right-half zero of multiplicity one, the proved positive dyadic leading-current
law therefore forces the corresponding weighted cosine correlation negative
on every sufficiently late dyadic block.  Any source-side nonnegative-block
law for that literal correlation would exclude such a zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Literal weighted Fourier-cosine correlation between the translated new
eta head and its successor finite prefix. -/
def pairedEtaTopPrefixFiniteHeadCosineCorrelation
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  ∫ z : ℝ × ℝ,
    Real.cos (rho.1.im *
      (z.2 - (pairedEtaLogTailCutoff (N + 1) + z.1))) *
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho
      (pairedEtaLogTailCutoff (N + 1) + z.1 + z.2)
    ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod
      (pairedEtaFiniteLogMeasure (N + 2)))

/-- At multiplicity one, the isolated leading current is negative twice the
literal weighted head--prefix cosine correlation. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_neg_two_headCosineCorrelation_of_multiplicity_one
    (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      -2 * pairedEtaTopPrefixFiniteHeadCosineCorrelation rho N := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_head_cosine_bracket_of_multiplicity_one
    rho hm N]
  unfold pairedEtaTopPrefixFiniteHeadCosineCorrelation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  ring

/-- Exact dyadic form of the multiplicity-one head-cosine identity. -/
theorem rgEtaDyadicLeadingFluxBlock_eq_neg_two_headCosineBlock_of_multiplicity_one
    (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    (∑ j ∈ Finset.range N,
        pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j)) =
      -2 * (∑ j ∈ Finset.range N,
        pairedEtaTopPrefixFiniteHeadCosineCorrelation rho (N + j)) := by
  calc
    _ = ∑ j ∈ Finset.range N,
          -2 * pairedEtaTopPrefixFiniteHeadCosineCorrelation rho (N + j) :=
        Finset.sum_congr rfl (fun j _ =>
          topPrefixFiniteEnergyLeadingFlux_eq_neg_two_headCosineCorrelation_of_multiplicity_one
            rho hm (N + j))
    _ = _ := (Finset.mul_sum (Finset.range N)
      (fun j => pairedEtaTopPrefixFiniteHeadCosineCorrelation rho (N + j)) (-2)).symm

/-- A hypothetical right-half zero of multiplicity one gives the exact
negative sharp scaled limit for its literal dyadic Fourier correlation. -/
theorem tendsto_scaled_rgEtaDyadicHeadCosineBlock_of_half_lt_re_and_multiplicity_one
    (rho : NontrivialZetaZero)
    (hhalf : 1 / 2 < rho.1.re)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) *
        (∑ j ∈ Finset.range N,
          pairedEtaTopPrefixFiniteHeadCosineCorrelation rho (N + j)))
      atTop
      (nhds ((-1 / 2 : ℝ) *
        ((1 - (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho)) *
          (rgEtaSharpConstant rho) ^ 2))) := by
  have hflux := tendsto_scaled_rgEtaDyadicLeadingFluxBlock_of_half_lt_re rho hhalf
  have hhalfFlux := hflux.const_mul (-1 / 2 : ℝ)
  apply hhalfFlux.congr'
  filter_upwards with N
  rw [rgEtaDyadicLeadingFluxBlock_eq_neg_two_headCosineBlock_of_multiplicity_one
    rho hm N]
  ring

/-- A hypothetical right-half zero of multiplicity one forces the actual
weighted head--prefix cosine correlation to have negative dyadic blocks. -/
theorem eventually_neg_rgEtaDyadicHeadCosineBlock_of_half_lt_re_and_multiplicity_one
    (rho : NontrivialZetaZero)
    (hhalf : 1 / 2 < rho.1.re)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    ∀ᶠ N : ℕ in atTop,
      ∑ j ∈ Finset.range N,
        pairedEtaTopPrefixFiniteHeadCosineCorrelation rho (N + j) < 0 := by
  have hpos := eventually_pos_rgEtaDyadicLeadingFluxBlock_of_half_lt_re rho hhalf
  filter_upwards [hpos] with N hN
  have hsum :=
    rgEtaDyadicLeadingFluxBlock_eq_neg_two_headCosineBlock_of_multiplicity_one
      rho hm N
  nlinarith

end

end RiemannGaussian
