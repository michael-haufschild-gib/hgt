import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianDigammaGauss
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianExplicitFormula

/-!
# Gaussian explicit-formula layer: discharged premises

Several lemmas of the Gaussian explicit-formula layer were stated under a named analytic input
that later modules proved outright:

* `ZetaZeroGaussianOrdinateSummable` — from the quadratic growth of `riemannXi`
  (`zetaZeroGaussianOrdinateSummable`);
* `RiemannXiQuadraticGrowth` — `riemannXi_quadraticGrowth`;
* `QuarterLineDigammaGaussDifferenceFormula` — Gauss's digamma integral
  (`quarterLineDigammaGaussDifferenceFormula`), which also yields `GaussianDigammaScrewTransform`;
* `GaussianArithmeticExplicitFormulaIdentified` — the log-derivative contour bound
  (`gaussianArithmeticExplicitFormulaIdentified`);
* `ZetaGaussianZeroDivisorSeparation` — `zetaGaussianZeroDivisorSeparation_proved`.

Each theorem below is the hypothesis-free form of a lemma whose only non-typing premise was one of
these inputs.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory MeromorphicOn Set Metric
open scoped Topology

/-! ## Zero-ordinate summability -/

/-- The heat-integrand `L¹` norms over all zero occurrences are summable. -/
theorem summable_integral_norm_zetaGaussian_heat_unconditional
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    Summable (fun occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      ∫ s : ℝ,
        ‖(Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
          zetaGaussianZeroSummand
            analyticZetaZeroMultiplicity a s occurrence‖) :=
  summable_integral_norm_zetaGaussian_heat zetaZeroGaussianOrdinateSummable hε hεa t

/-- Heat convolution commutes with the complete translated zero sum. -/
theorem tsum_zetaGaussianZeroSummand_heat_convolution_unconditional
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    (∑' occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence) =
      (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
            (∑' occurrence :
              NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
              zetaGaussianZeroSummand
                analyticZetaZeroMultiplicity a s occurrence) :=
  tsum_zetaGaussianZeroSummand_heat_convolution zetaZeroGaussianOrdinateSummable hε hεa t

/-- Every translated entire Gaussian is absolutely summable over the zero occurrences. -/
theorem summable_zetaGaussianZeroSummand_unconditional
    (ε t : ℝ) (hε : 0 < ε) :
    Summable (zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε t) :=
  summable_zetaGaussianZeroSummand_of_ordinateSummable zetaZeroGaussianOrdinateSummable ε t hε

/-- The occurrence enumeration represents the canonical symmetric Gaussian zero sum. -/
theorem representsCanonicalZetaSymmetricGaussianZeroSum_unconditional :
    RepresentsZetaSymmetricGaussianZeroSum analyticZetaZeroMultiplicity
      canonicalZetaSymmetricGaussianZeroSum :=
  representsCanonicalZetaSymmetricGaussianZeroSum zetaZeroGaussianOrdinateSummable

/-! ## Quadratic growth of `riemannXi` -/

/-- One uniform constant bounds the `riemannXi` divisor in every closed ball quadratically. -/
theorem exists_riemannXi_divisor_closedBall_quadratic_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * (2 * r + 1) ^ (2 : ℕ) / Real.log 2 :=
  riemannXi_quadraticGrowth.exists_divisor_bound

/-! ## Gauss's digamma integral -/

/-- The Gaussian–Gauss joint kernel is integrable on the positive quadrant. -/
theorem integrable_gaussianDigammaGaussJointIntegrand_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (gaussianDigammaGaussJointIntegrand ε t)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ)))) :=
  integrable_gaussianDigammaGaussJointIntegrand quarterLineDigammaGaussDifferenceFormula hε t

/-- Fubini exchange for the Gaussian–Gauss joint kernel. -/
theorem integral_gaussianDigammaGauss_swap_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        ∫ u in Set.Ioi (0 : ℝ),
          gaussianSuzukiDigammaOscillationIntegrand r u) =
      ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          ∫ r in Set.Ioi (0 : ℝ),
            symmetricGaussian ε t r *
              (1 - Real.cos (r * u)) :=
  integral_gaussianDigammaGauss_swap quarterLineDigammaGaussDifferenceFormula hε t

/-- Gaussian average of the archimedean density increment, in Gauss-integral form. -/
theorem integral_symmetricGaussian_mul_archimedeanDensityDifference_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        (riemannArchimedeanDensity r -
          riemannArchimedeanDensity 0)) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          (Real.sqrt (Real.pi / ε) *
            (1 - Real.exp (-u ^ 2 / (4 * ε)) *
              Real.cos (t * u))) :=
  integral_symmetricGaussian_mul_archimedeanDensityDifference
    quarterLineDigammaGaussDifferenceFormula hε t

/-- The outer Gauss integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_gaussianDigammaGaussOuter_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => gaussianSuzukiDigammaDensity u *
        (Real.sqrt (Real.pi / ε) *
          (1 - Real.exp (-u ^ 2 / (4 * ε)) *
            Real.cos (t * u))))
      (Set.Ioi (0 : ℝ)) :=
  integrableOn_gaussianDigammaGaussOuter quarterLineDigammaGaussDifferenceFormula hε t

/-- The complete digamma gain is the Gaussian energy of the quarter-line density. -/
theorem gaussianDigammaGain_eq_gaussianSuzukiDigammaEnergy_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianDigammaGain ε t =
      2 / Real.sqrt (Real.pi * ε) *
        ∫ u in Set.Ioi (0 : ℝ),
          gaussianSuzukiDigammaDensity u *
            Real.exp (-u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u)) :=
  gaussianDigammaGain_eq_gaussianSuzukiDigammaEnergy quarterLineDigammaGaussDifferenceFormula hε t

/-! ## Digamma screw transform -/

/-- Endpoint, forward prime-energy discrepancy and missing curvature recombine to the arithmetic
Gaussian value. -/
theorem gaussianArithmeticExplicitFormula_eq_endpoint_add_forwardDiscrepancy_add_missing_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianForwardPrimeEnergyDiscrepancy ε t +
          gaussianSuzukiMissingCurvatureEnergy ε t :=
  gaussianArithmeticExplicitFormula_eq_endpoint_add_forwardDiscrepancy_add_missing
    gaussianDigammaScrewTransform hε t

/-- The improper Chebyshev-error integrals converge to the arithmetic Gaussian value. -/
theorem tendsto_gaussianArithmeticExplicitFormula_from_chebyshevError_add_missing_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        gaussianArithmeticExplicitFormula ε 0 +
          gaussianSuzukiMissingCurvatureEnergy ε t +
          2 / Real.sqrt (Real.pi * ε) *
            ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
              gaussianPrimeAbelKernelDerivative ε t x *
                (x - Chebyshev.psi x))
      atTop (𝓝 (gaussianArithmeticExplicitFormula ε t)) :=
  tendsto_gaussianArithmeticExplicitFormula_from_chebyshevError_add_missing
    gaussianDigammaScrewTransform hε t

/-- Cofinal Suzuki energy budgets are cofinal arithmetic Gaussian positivity. -/
theorem gaussianSuzukiEnergyGoodWidthsUnbounded_iff_arithmetic_unconditional :
    GaussianSuzukiEnergyGoodWidthsUnbounded ↔
      GaussianArithmeticGoodWidthsUnbounded :=
  gaussianSuzukiEnergyGoodWidthsUnbounded_iff_arithmetic gaussianDigammaScrewTransform

/-! ## Explicit-formula identification -/

/-- The arithmetic Gaussian expression obeys the exact heat propagation law. -/
theorem gaussianArithmeticExplicitFormula_heat_convolution_unconditional
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      heatConvolution a (heatParameter a ε)
        (gaussianArithmeticExplicitFormula a) t :=
  gaussianArithmeticExplicitFormula_heat_convolution gaussianArithmeticExplicitFormulaIdentified
    hε hεa t

/-- Positivity at cofinally many widths is positivity at every width. -/
theorem gaussianArithmeticGoodWidthsUnbounded_iff_nonnegative_unconditional :
    GaussianArithmeticGoodWidthsUnbounded ↔
      ZetaSymmetricGaussianZeroSumNonnegative
        gaussianArithmeticExplicitFormula :=
  gaussianArithmeticGoodWidthsUnbounded_iff_nonnegative gaussianArithmeticExplicitFormulaIdentified

/-! ## Zero-divisor separation -/

/-- Coherent-kernel separation holds: a positive semidefinite coherent Gram kernel of a represented
zero sum forces every nontrivial zero onto the critical line. -/
theorem zetaGaussianCoherentKernelSeparation_proved :
    ZetaGaussianCoherentKernelSeparation :=
  zetaGaussianCoherentKernelSeparation_of_zeroDivisorSeparation
    zetaGaussianZeroDivisorSeparation_proved

end

end RiemannGaussian
