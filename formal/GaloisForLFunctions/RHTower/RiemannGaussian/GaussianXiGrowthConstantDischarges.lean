import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireBoundaryLowerBound
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRadialAnnulus
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRadialBoundary
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRadialHeatLimit
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiInverseSquareSummability
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiQuantitativeContour
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianZetaCounting
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaLowerNearLinear
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaLowerSubquadratic
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiWeilVertical
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiWeilVerticalLimit
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiSubquadraticGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogLinearGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiGrowth

/-!
# Uniform growth constants of `ξ` in the RiemannGaussian estimates

Many estimates of the Gaussian/Suzuki layer take a growth constant `A ≥ 1` and the bound
`‖ξ(z)‖ ≤ exp(A·g(‖z‖+1))` as hypotheses, for the three growth profiles proved in the corpus:

* quadratic, `g(r) = r²` — `riemannXi_quadraticGrowth`;
* subquadratic, `g(r) = r^{3/2}` — `riemannXi_threeHalvesGrowth`;
* log-linear, `g = xiLogLinearScale` — `riemannXi_logLinearGrowth`.

Each theorem below is the corresponding estimate with one constant `A` valid uniformly in all
remaining parameters, the growth hypothesis discharged by the matching growth law.
-/

open Filter MeasureTheory MeromorphicOn Metric Set
open scoped Topology ENNReal Interval

noncomputable section

namespace RiemannGaussian

/-- Uniform-constant form of
`norm_riemannXiCanonicalResidual_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_norm_riemannXiCanonicalResidual_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ closedBall 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalResidual n z‖ ≤ Real.exp (A * (xiCanonicalRadius n + 1) ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalResidual_le_of_growth (A := A)
        (_hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`riemannXiCanonicalLog_re_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_riemannXiCanonicalLog_re_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      (riemannXiCanonicalLog n z).re ≤ A * (xiCanonicalRadius n + 1) ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z hz => riemannXiCanonicalLog_re_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`norm_riemannXiCanonicalLog_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_norm_riemannXiCanonicalLog_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalLog n z‖ ≤ 2 * (A * (xiCanonicalRadius n + 1) ^ 2) * ‖z‖ / (xiCanonicalRadius n - ‖z‖) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalLog_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`norm_logDeriv_riemannXiCanonicalResidual_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_norm_logDeriv_riemannXiCanonicalResidual_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ xiCanonicalRadius n / 4 →
      ‖logDeriv (riemannXiCanonicalResidual n) z‖ ≤ (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) / (xiCanonicalRadius n / 4) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z hz => norm_logDeriv_riemannXiCanonicalResidual_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`sum_divisor_riemannXi_ball_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_sum_divisor_riemannXi_ball_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      ((∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤ A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => sum_divisor_riemannXi_ball_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`norm_canonicalLogDerivSum_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_norm_canonicalLogDerivSum_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ) (δ : ℝ), 0 < δ → ‖z‖ ≤ xiCanonicalRadius n / 4 → ∀ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 → δ ≤ ‖z - i‖ →
      ‖∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i • logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) z‖ ≤ (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) * (2 / xiCanonicalRadius n + 1 / δ) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z δ hδ hz hsep => norm_canonicalLogDerivSum_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (δ := δ)
        (hδ := hδ)
        (hz := hz)
        (hsep := hsep)⟩

/-- Uniform-constant form of
`norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (y : ℝ), -1 ≤ y → y ≤ 1 →
      ‖logDeriv riemannXi (completedSpectralCoordinate ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I))‖ ≤ (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) / (xiCanonicalRadius n / 4) + (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) * (2 / xiCanonicalRadius n + 1 / spectralBoundarySeparation n) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n y hylo hyhi => norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (y := y)
        (hylo := hylo)
        (hyhi := hyhi)⟩

/-- Uniform-constant form of
`explicit_logDeriv_bound_le_exponential`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_explicit_logDeriv_bound_le_exponential :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) / (xiCanonicalRadius n / 4) + (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) * (2 / xiCanonicalRadius n + 1 / spectralBoundarySeparation n) ≤ (392 * A + 729 * (A / Real.log 2) * (13 + 75 * (A / Real.log 2))) * Real.exp (4 * quantitativeSpectralBoundaryTruncation n) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => explicit_logDeriv_bound_le_exponential (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`spectralZetaZeroWindow_card_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_spectralZetaZeroWindow_card_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T : ℝ), 0 ≤ T →
      ((spectralZetaZeroWindow T).card : ℝ) ≤ A * (2 * (T + 1) + 1) ^ (2 : ℕ) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun T hT => spectralZetaZeroWindow_card_le_of_growth (A := A)
        (T := T)
        (hA := hA)
        (hT := hT)
        (hbound := hbound)⟩

/-- Uniform-constant form of
`finiteUpperHeatInRadialAnnulus_le_quadraticMaxGaussian_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_finiteUpperHeatInRadialAnnulus_le_quadraticMaxGaussian :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℝ[X]) (r : ℝ) (R : ℝ) (z : ℂ) (tau : ℝ), 0 < R → 0 < tau → r ≤ R → realPolynomialRootCountInBall P 0 r = riemannXiSpectralRadialDivisorCount r → realPolynomialRootCountInBall P 0 R = riemannXiSpectralRadialDivisorCount R →
      finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInRadialAnnulus P r R) tau ≤ (K * (2 * (R + 1) + 1) ^ (2 : ℕ) / Real.log 2) * (tau⁻¹ * Real.exp (-((max (r - ‖z‖) 0) ^ (2 : ℕ) * tau))) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun P r R z tau hR htau hrR hinner houter => finiteUpperHeatInRadialAnnulus_le_quadraticMaxGaussian_of_growth (P := P)
        (K := K)
        (r := r)
        (R := R)
        (z := z)
        (tau := tau)
        (hK := hK)
        (hR := hR)
        (hbound := hbound)
        (htau := htau)
        (hrR := hrR)
        (hinner := hinner)
        (houter := houter)⟩

/-- Uniform-constant form of
`finiteUpperHeatInSelectedRadialAnnulus_le_majorant`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_finiteUpperHeatInSelectedRadialAnnulus_le_majorant :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℝ[X]) (m : ℕ) (n : ℕ), m < n → realPolynomialRootCountInBall P 0 (quantitativeSpectralRadialBoundary n) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary n) → ∀ k : ℕ, k + 1 ≤ n → realPolynomialRootCountInBall P 0 (quantitativeSpectralRadialBoundary k) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary k) → ∀ (z : ℂ) (tau : ℝ), 0 < tau →
      finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInRadialAnnulus P (quantitativeSpectralRadialBoundary m) (quantitativeSpectralRadialBoundary (m + 1))) tau ≤ selectedRadialHeatShellMajorant K z tau m := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun P m n hmn hcurrent hearlier z tau htau => finiteUpperHeatInSelectedRadialAnnulus_le_majorant (P := P)
        (K := K)
        (hK := hK)
        (hbound := hbound)
        (m := m)
        (n := n)
        (hmn := hmn)
        (hcurrent := hcurrent)
        (hearlier := hearlier)
        (z := z)
        (tau := tau)
        (htau := htau)⟩

/-- Uniform-constant form of
`summable_spectralRadialAnnularHeat_and_tendsto_polynomialShellSum`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_summable_spectralRadialAnnularHeat_and_tendsto_polynomialShellSum :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ → ℝ[X]), TendstoLocallyUniformlyOn (fun n w ↦ ((B n).map Complex.ofRealHom).eval w) riemannXiSpectral atTop Set.univ → ∀ n : ℕ, realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary n) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary n) → ∀ (n m : ℕ), m + 1 ≤ n → realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary m) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary m) → ∀ (z : ℂ), 0 < z.im → ∀ (tau : ℝ), 0 < tau →
      Summable (fun m : ℕ ↦ riemannXiUpperHyperbolicHeatRadialAnnulus z tau (quantitativeSpectralRadialBoundary m) (quantitativeSpectralRadialBoundary (m + 1))) ∧ Tendsto (fun n ↦ ∑ m ∈ Finset.range n, finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInRadialAnnulus (B n) (quantitativeSpectralRadialBoundary m) (quantitativeSpectralRadialBoundary (m + 1))) tau) atTop (nhds (∑' m : ℕ, riemannXiUpperHyperbolicHeatRadialAnnulus z tau (quantitativeSpectralRadialBoundary m) (quantitativeSpectralRadialBoundary (m + 1)))) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun B hlimit hcurrent hearlier z hz tau htau => summable_spectralRadialAnnularHeat_and_tendsto_polynomialShellSum (B := B)
        (hlimit := hlimit)
        (K := K)
        (hK := hK)
        (hbound := hbound)
        (hcurrent := hcurrent)
        (hearlier := hearlier)
        (z := z)
        (hz := hz)
        (tau := tau)
        (htau := htau)⟩

/-- Uniform-constant form of
`tendsto_finiteUpperHeatInsideSelectedRadialBall`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_tendsto_finiteUpperHeatInsideSelectedRadialBall :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ → ℝ[X]), TendstoLocallyUniformlyOn (fun n w ↦ ((B n).map Complex.ofRealHom).eval w) riemannXiSpectral atTop Set.univ → ∀ n : ℕ, realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary n) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary n) → ∀ (n m : ℕ), m + 1 ≤ n → realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary m) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary m) → ∀ (z : ℂ), 0 < z.im → ∀ (tau : ℝ), 0 < tau →
      Tendsto (fun n ↦ finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInsideBall (B n) (quantitativeSpectralRadialBoundary n)) tau) atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun B hlimit hcurrent hearlier z hz tau htau => tendsto_finiteUpperHeatInsideSelectedRadialBall (B := B)
        (hlimit := hlimit)
        (K := K)
        (hK := hK)
        (hbound := hbound)
        (hcurrent := hcurrent)
        (hearlier := hearlier)
        (z := z)
        (hz := hz)
        (tau := tau)
        (htau := htau)⟩

/-- Uniform-constant form of
`tendsto_realPolynomialUpperHeatSum_of_radialCounts`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_tendsto_realPolynomialUpperHeatSum_of_radialCounts :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ → ℝ[X]), TendstoLocallyUniformlyOn (fun n w ↦ ((B n).map Complex.ofRealHom).eval w) riemannXiSpectral atTop Set.univ → ∀ n : ℕ, realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary n) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary n) → ∀ (n m : ℕ), m + 1 ≤ n → realPolynomialRootCountInBall (B n) 0 (quantitativeSpectralRadialBoundary m) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary m) → ∀ (z : ℂ), 0 < z.im → ∀ (tau : ℝ), 0 < tau → Tendsto (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset (B n) (realPolynomialUpperRootMultisetInsideBall (B n) (quantitativeSpectralRadialBoundary n)) z tau) atTop (nhds 0) →
      Tendsto (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) z tau) atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun B hlimit hcurrent hearlier z hz tau htau htail => tendsto_realPolynomialUpperHeatSum_of_radialCounts (B := B)
        (hlimit := hlimit)
        (K := K)
        (hK := hK)
        (hbound := hbound)
        (hcurrent := hcurrent)
        (hearlier := hearlier)
        (z := z)
        (hz := hz)
        (tau := tau)
        (htau := htau)
        (htail := htail)⟩

/-- Uniform-constant form of
`one_div_spectralRadialBoundarySeparation_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_one_div_spectralRadialBoundarySeparation_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      1 / spectralRadialBoundarySeparation n ≤ 3 * (A * (2 * ((n : ℝ) + 2) + 1) ^ (2 : ℕ) / Real.log 2 + 4) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => one_div_spectralRadialBoundarySeparation_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`exp_neg_xiQuantitativeRadialBoundaryLowerExponent_le_norm_riemannXiSpectral`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_exp_neg_xiQuantitativeRadialBoundaryLowerExponent_le_norm_riemannXiSpectral :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (w : ℂ), ‖w‖ = quantitativeSpectralRadialBoundary n →
      Real.exp (-xiQuantitativeRadialBoundaryLowerExponent A n) ≤ ‖riemannXiSpectral w‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n w hw => exp_neg_xiQuantitativeRadialBoundaryLowerExponent_le_norm_riemannXiSpectral (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (w := w)
        (hw := hw)⟩

/-- Uniform-constant form of
`radialCanonicalInnerQuarterBound_le_exponential`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_radialCanonicalInnerQuarterBound_le_exponential :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      (2 * (A * (xiCanonicalRadius n + 1) ^ (2 : ℕ))) / (xiCanonicalRadius n / 4) + (A * (2 * xiCanonicalRadius n + 1) ^ (2 : ℕ) / Real.log 2) * (2 / xiCanonicalRadius n + 1 / spectralRadialBoundarySeparation n) ≤ (392 * A + 729 * (A / Real.log 2) * (13 + 75 * (A / Real.log 2))) * Real.exp (4 * quantitativeSpectralRadialBoundary n) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => radialCanonicalInnerQuarterBound_le_exponential (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`xiQuantitativeRadialBoundaryLowerExponent_le_exponential`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_xiQuantitativeRadialBoundaryLowerExponent_le_exponential :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      xiQuantitativeRadialBoundaryLowerExponent A n ≤ 26 * (392 * A + 729 * (A / Real.log 2) * (13 + 75 * (A / Real.log 2))) * Real.exp (5 * quantitativeSpectralRadialBoundary n) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => xiQuantitativeRadialBoundaryLowerExponent_le_exponential (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`norm_riemannXiCanonicalResidual_le_of_threeHalves_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_norm_riemannXiCanonicalResidual_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ closedBall 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalResidual n z‖ ≤ Real.exp (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalResidual_le_of_threeHalves_growth (A := A)
        (_hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`riemannXiCanonicalLog_re_le_of_threeHalves_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_riemannXiCanonicalLog_re_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      (riemannXiCanonicalLog n z).re ≤ A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n z hz => riemannXiCanonicalLog_re_le_of_threeHalves_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`norm_riemannXiCanonicalLog_le_of_threeHalves_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_norm_riemannXiCanonicalLog_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalLog n z‖ ≤ 2 * (A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ)) * ‖z‖ / (xiCanonicalRadius n - ‖z‖) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalLog_le_of_threeHalves_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`exp_neg_xiCanonicalThreeHalvesLowerExponent_le_norm_riemannXi`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_exp_neg_xiCanonicalThreeHalvesLowerExponent_le_norm_riemannXi :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ) (delta : ℝ), 0 < delta → ‖z‖ ≤ xiCanonicalRadius n / 4 → riemannXi z ≠ 0 → ∀ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 → delta ≤ ‖z - i‖ →
      Real.exp (- ( 2 * A * (xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) + (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2) * Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤ ‖riemannXi z‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n z delta hdelta hz hxi hsep => exp_neg_xiCanonicalThreeHalvesLowerExponent_le_norm_riemannXi (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (delta := delta)
        (hdelta := hdelta)
        (hz := hz)
        (hxi := hxi)
        (hsep := hsep)⟩

/-- Uniform-constant form of
`exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (y : ℝ), -1 ≤ y → y ≤ 1 →
      Real.exp (-xiQuantitativeBoundaryThreeHalvesLowerExponent A n) ≤ ‖riemannXiSpectral ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n y hylo hyhi => exp_neg_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_norm_riemannXiSpectral (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (y := y)
        (hylo := hylo)
        (hyhi := hyhi)⟩

/-- Uniform-constant form of
`xiQuantitativeBoundaryThreeHalvesLowerExponent_le_polynomialLog`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_xiQuantitativeBoundaryThreeHalvesLowerExponent_le_polynomialLog :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      xiQuantitativeBoundaryThreeHalvesLowerExponent A n ≤ xiQuantitativeBoundaryThreeHalvesPolynomialLogMajorant A n := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => xiQuantitativeBoundaryThreeHalvesLowerExponent_le_polynomialLog (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero :
    ∃ A : ℝ, 1 ≤ A ∧ Tendsto (fun n : ℕ ↦ xiQuantitativeBoundaryThreeHalvesLowerExponent A n / (quantitativeSpectralBoundaryTruncation n + 1) ^ 2) atTop (nhds 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, tendsto_xiQuantitativeBoundaryThreeHalvesLowerExponent_div_sq_zero (A := A)
        (hA := hA)
        (hbound := hbound)⟩

/-- Uniform-constant form of
`criticalZeta_log_negativePart_le_threeHalvesLowerExponent`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_criticalZeta_log_negativePart_le_threeHalvesLowerExponent :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      max 0 (-Real.log ‖riemannZeta (staticContourCriticalEndpoint (quantitativeSpectralBoundaryTruncation n))‖) ≤ xiQuantitativeBoundaryThreeHalvesLowerExponent A n + 2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) + Real.log staticContourCriticalGammaRUpperMass := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => criticalZeta_log_negativePart_le_threeHalvesLowerExponent (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tendsto_criticalZeta_threeHalvesNegativeMajorant_div_sq_zero`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_tendsto_criticalZeta_threeHalvesNegativeMajorant_div_sq_zero :
    ∃ A : ℝ, 1 ≤ A ∧ Tendsto (fun n : ℕ ↦ (xiQuantitativeBoundaryThreeHalvesLowerExponent A n + 2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) + Real.log staticContourCriticalGammaRUpperMass) / (quantitativeSpectralBoundaryTruncation n + 1) ^ 2) atTop (nhds 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, tendsto_criticalZeta_threeHalvesNegativeMajorant_div_sq_zero (A := A)
        (hA := hA)
        (hbound := hbound)⟩

/-- Uniform-constant form of
`suzukiXiWeilVerticalExplicitMajorant_le_rpow`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_suzukiXiWeilVerticalExplicitMajorant_le_rpow :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (t : ℝ) (n : ℕ), 1 ≤ n →
      suzukiXiWeilVerticalExplicitMajorant A B t n ≤ suzukiXiWeilVerticalAsymptoticConstant A B t * ((n : ℝ) + 1) ^ (-(5 / 16 : ℝ)) := by
  obtain ⟨A, hA, hThreeHalves⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun B hB t n hn => suzukiXiWeilVerticalExplicitMajorant_le_rpow (A := A)
        (B := B)
        (hA := hA)
        (hThreeHalves := hThreeHalves)
        (hB := hB)
        (t := t)
        (n := n)
        (hn := hn)⟩

/-- Uniform-constant form of
`tendsto_suzukiXiWeilVerticalExplicitMajorant_zero`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_tendsto_suzukiXiWeilVerticalExplicitMajorant_zero :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (B : ℝ), 1 ≤ B → ∀ (t : ℝ),
      Tendsto (fun n : ℕ ↦ suzukiXiWeilVerticalExplicitMajorant A B t n) atTop (nhds 0) := by
  obtain ⟨A, hA, hThreeHalves⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun B hB t => tendsto_suzukiXiWeilVerticalExplicitMajorant_zero (A := A)
        (B := B)
        (hA := hA)
        (hThreeHalves := hThreeHalves)
        (hB := hB)
        (t := t)⟩

/-- Uniform-constant form of
`spectralZetaZeroWindow_card_le_threeHalves_of_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_spectralZetaZeroWindow_card_le_threeHalves :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T : ℝ), 0 ≤ T →
      ((spectralZetaZeroWindow T).card : ℝ) ≤ A * (2 * (T + 1) + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun T hT => spectralZetaZeroWindow_card_le_threeHalves_of_growth (A := A)
        (T := T)
        (hA := hA)
        (hT := hT)
        (hbound := hbound)⟩

/-- Uniform-constant form of
`sum_divisor_riemannXi_ball_le_threeHalves_of_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_sum_divisor_riemannXi_ball_le_threeHalves :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      ((∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤ A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => sum_divisor_riemannXi_ball_le_threeHalves_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`intervalIntegral_norm_canonicalLogDerivSum_quantitative_le_of_growth`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_intervalIntegral_norm_canonicalLogDerivSum_quantitative_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      (∫ y : ℝ in (-1 : ℝ)..1, ‖∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i • logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) (completedSpectralCoordinate ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I))‖) ≤ (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2) * (4 / xiCanonicalRadius n + 2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => intervalIntegral_norm_canonicalLogDerivSum_quantitative_le_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`intervalIntegral_norm_logDeriv_riemannXiCanonicalResidual_quantitative_le_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_intervalIntegral_norm_logDeriv_riemannXiCanonicalResidual_quantitative_le :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (n : ℕ),
      (∫ y : ℝ in (-1 : ℝ)..1, ‖logDeriv (riemannXiCanonicalResidual n) (completedSpectralCoordinate ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I))‖) ≤ 2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) / (xiCanonicalRadius n / 4)) := by
  obtain ⟨B, hB, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨B, hB, fun n => intervalIntegral_norm_logDeriv_riemannXiCanonicalResidual_quantitative_le_of_growth (B := B)
        (hB := hB)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tsum_zetaZeroNormDyadicShell_multiplicity_le`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_tsum_zetaZeroNormDyadicShell_multiplicity_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      ∑' rho : {rho : NontrivialZetaZero | zetaZeroNormDyadicIndex rho = n}, (analyticZetaZeroMultiplicity rho.1 : ℝ) ≤ A * (2 * (2 : ℝ) ^ n + 1) ^ (3 / 2 : ℝ) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => tsum_zetaZeroNormDyadicShell_multiplicity_le (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tsum_zetaZeroNormDyadicShell_inverseSquare_le`;
the growth constant comes from `riemannXi_threeHalvesGrowth`. -/
theorem exists_tsum_zetaZeroNormDyadicShell_inverseSquare_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      ∑' rho : {rho : NontrivialZetaZero | zetaZeroNormDyadicIndex rho = n}, (analyticZetaZeroMultiplicity rho.1 : ℝ) / (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤ riemannXiInverseSquareDyadicMajorant A n := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  exact ⟨A, hA, fun n => tsum_zetaZeroNormDyadicShell_inverseSquare_le (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`spectralZetaZeroWindow_card_le_logLinear_of_growth`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_spectralZetaZeroWindow_card_le_logLinear :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T : ℝ), 0 ≤ T →
      ((spectralZetaZeroWindow T).card : ℝ) ≤ A * xiLogLinearScale (2 * (T + 1) + 1) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun T hT => spectralZetaZeroWindow_card_le_logLinear_of_growth (A := A)
        (T := T)
        (hA := hA)
        (hT := hT)
        (hbound := hbound)⟩

/-- Uniform-constant form of
`sum_divisor_riemannXi_ball_le_logLinear_of_growth`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_sum_divisor_riemannXi_ball_le_logLinear :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      ((∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤ A * xiLogLinearScale (2 * xiCanonicalRadius n + 1) / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n => sum_divisor_riemannXi_ball_le_logLinear_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`norm_riemannXiCanonicalResidual_le_of_logLinear_growth`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_norm_riemannXiCanonicalResidual_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ closedBall 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalResidual n z‖ ≤ Real.exp (A * xiLogLinearScale (xiCanonicalRadius n + 1)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalResidual_le_of_logLinear_growth (A := A)
        (_hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`riemannXiCanonicalLog_re_le_of_logLinear_growth`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_riemannXiCanonicalLog_re_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      (riemannXiCanonicalLog n z).re ≤ A * xiLogLinearScale (xiCanonicalRadius n + 1) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n z hz => riemannXiCanonicalLog_re_le_of_logLinear_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`norm_riemannXiCanonicalLog_le_of_logLinear_growth`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_norm_riemannXiCanonicalLog_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), z ∈ ball 0 (xiCanonicalRadius n) →
      ‖riemannXiCanonicalLog n z‖ ≤ 2 * (A * xiLogLinearScale (xiCanonicalRadius n + 1)) * ‖z‖ / (xiCanonicalRadius n - ‖z‖) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n z hz => norm_riemannXiCanonicalLog_le_of_logLinear_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (hz := hz)⟩

/-- Uniform-constant form of
`exp_neg_xiCanonicalLogLinearLowerExponent_le_norm_riemannXi`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_exp_neg_xiCanonicalLogLinearLowerExponent_le_norm_riemannXi :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ) (delta : ℝ), 0 < delta → ‖z‖ ≤ xiCanonicalRadius n / 4 → riemannXi z ≠ 0 → ∀ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 → delta ≤ ‖z - i‖ →
      Real.exp (- ( 2 * A * xiLogLinearScale (xiCanonicalRadius n + 1) + (A * xiLogLinearScale (2 * xiCanonicalRadius n + 1) / Real.log 2) * Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤ ‖riemannXi z‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n z delta hdelta hz hxi hsep => exp_neg_xiCanonicalLogLinearLowerExponent_le_norm_riemannXi (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (delta := delta)
        (hdelta := hdelta)
        (hz := hz)
        (hxi := hxi)
        (hsep := hsep)⟩

/-- Uniform-constant form of
`exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (y : ℝ), -1 ≤ y → y ≤ 1 →
      Real.exp (-xiQuantitativeBoundaryLogLinearLowerExponent A n) ≤ ‖riemannXiSpectral ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n y hylo hyhi => exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (y := y)
        (hylo := hylo)
        (hyhi := hyhi)⟩

/-- Uniform-constant form of
`xiQuantitativeBoundaryLogLinearLowerExponent_le_polynomialLog`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_xiQuantitativeBoundaryLogLinearLowerExponent_le_polynomialLog :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      xiQuantitativeBoundaryLogLinearLowerExponent A n ≤ xiQuantitativeBoundaryLogLinearPolynomialLogMajorant A n := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n => xiQuantitativeBoundaryLogLinearLowerExponent_le_polynomialLog (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ ↦ xiQuantitativeBoundaryLogLinearLowerExponent A n / (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon)) atTop (nhds 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun epsilon hepsilon => tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero (A := A)
        (hA := hA)
        (hbound := hbound)
        (epsilon := epsilon)
        (hepsilon := hepsilon)⟩

/-- Uniform-constant form of
`criticalZeta_log_negativePart_le_logLinearLowerExponent`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_criticalZeta_log_negativePart_le_logLinearLowerExponent :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      max 0 (-Real.log ‖riemannZeta (staticContourCriticalEndpoint (quantitativeSpectralBoundaryTruncation n))‖) ≤ xiQuantitativeBoundaryLogLinearLowerExponent A n + 2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) + Real.log staticContourCriticalGammaRUpperMass := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun n => criticalZeta_log_negativePart_le_logLinearLowerExponent (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`tendsto_criticalZeta_logLinearNegativeMajorant_div_one_add_rpow_zero`;
the growth constant comes from `riemannXi_logLinearGrowth`. -/
theorem exists_tendsto_criticalZeta_logLinearNegativeMajorant_div_one_add_rpow_zero :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ ↦ (xiQuantitativeBoundaryLogLinearLowerExponent A n + 2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) + Real.log staticContourCriticalGammaRUpperMass) / (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon)) atTop (nhds 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_logLinearGrowth
  exact ⟨A, hA, fun epsilon hepsilon => tendsto_criticalZeta_logLinearNegativeMajorant_div_one_add_rpow_zero (A := A)
        (hA := hA)
        (hbound := hbound)
        (epsilon := epsilon)
        (hepsilon := hepsilon)⟩

/-- Uniform-constant form of
`exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ) (delta : ℝ), 0 < delta → ‖z‖ ≤ xiCanonicalRadius n / 4 → riemannXi z ≠ 0 → ∀ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 → delta ≤ ‖z - i‖ →
      Real.exp (- ( 2 * A * (xiCanonicalRadius n + 1) ^ (2 : ℕ) + (A * (2 * xiCanonicalRadius n + 1) ^ (2 : ℕ) / Real.log 2) * Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤ ‖riemannXi z‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z delta hdelta hz hxi hsep => exp_neg_xiCanonicalLowerExponent_le_norm_riemannXi (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (z := z)
        (delta := delta)
        (hdelta := hdelta)
        (hz := hz)
        (hxi := hxi)
        (hsep := hsep)⟩

/-- Uniform-constant form of
`exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (y : ℝ), -1 ≤ y → y ≤ 1 →
      Real.exp (-xiQuantitativeBoundaryLowerExponent A n) ≤ ‖riemannXiSpectral ((quantitativeSpectralBoundaryTruncation n : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n y hylo hyhi => exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (y := y)
        (hylo := hylo)
        (hyhi := hyhi)⟩

/-- Uniform-constant form of
`xiQuantitativeBoundaryLowerExponent_le_exponential`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_xiQuantitativeBoundaryLowerExponent_le_exponential :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ),
      xiQuantitativeBoundaryLowerExponent A n ≤ 26 * (392 * A + 729 * (A / Real.log 2) * (13 + 75 * (A / Real.log 2))) * Real.exp (5 * quantitativeSpectralBoundaryTruncation n) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n => xiQuantitativeBoundaryLowerExponent_le_exponential (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral_horizontal`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral_horizontal :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (x : ℝ) (y : ℝ), |x| ≤ quantitativeSpectralBoundaryTruncation n → |y| = 1 →
      Real.exp (-xiQuantitativeBoundaryLowerExponent A n) ≤ ‖riemannXiSpectral ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n x y hx hy => exp_neg_xiQuantitativeBoundaryLowerExponent_le_norm_riemannXiSpectral_horizontal (A := A)
        (hA := hA)
        (hbound := hbound)
        (n := n)
        (x := x)
        (y := y)
        (hx := hx)
        (hy := hy)⟩

/-- Uniform-constant form of
`tsum_zetaZeroOrdinateShell_le`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_tsum_zetaZeroOrdinateShell_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (c : ℝ), 0 < c → ∀ (n : ℕ),
      ∑' ρ : {ρ : NontrivialZetaZero | zetaZeroOrdinateShellIndex ρ = n}, (analyticZetaZeroMultiplicity ρ.1 : ℝ) * Real.exp (-c * (zetaSpectralCoordinate ρ.1.1).re ^ (2 : ℕ)) ≤ (A * (2 * ((n : ℝ) + 2) + 1) ^ (2 : ℕ) / Real.log 2) * Real.exp (-c * (n : ℝ) ^ (2 : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun c hc n => tsum_zetaZeroOrdinateShell_le (A := A)
        (c := c)
        (hA := hA)
        (hc := hc)
        (hbound := hbound)
        (n := n)⟩

/-- Uniform-constant form of
`summable_distinct_zetaZeroGaussianOrdinate_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_summable_distinct_zetaZeroGaussianOrdinate :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (c : ℝ), 0 < c →
      Summable fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ) * Real.exp (-c * (zetaSpectralCoordinate ρ.1).re ^ (2 : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun c hc => summable_distinct_zetaZeroGaussianOrdinate_of_growth (A := A)
        (hA := hA)
        (hbound := hbound)
        (c := c)
        (hc := hc)⟩

/-- Uniform-constant form of
`finiteUpperHeatInRadialAnnulus_le_quadraticGaussian_of_growth`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_finiteUpperHeatInRadialAnnulus_le_quadraticGaussian :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℝ[X]) (r : ℝ) (R : ℝ) (z : ℂ) (tau : ℝ), 0 < R → 0 < tau → ‖z‖ ≤ r → r ≤ R → realPolynomialRootCountInBall P 0 r = riemannXiSpectralRadialDivisorCount r → realPolynomialRootCountInBall P 0 R = riemannXiSpectralRadialDivisorCount R →
      finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInRadialAnnulus P r R) tau ≤ (K * (2 * (R + 1) + 1) ^ (2 : ℕ) / Real.log 2) * (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ (2 : ℕ) * tau))) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun P r R z tau hR htau hrz hrR hinner houter => finiteUpperHeatInRadialAnnulus_le_quadraticGaussian_of_growth (P := P)
        (K := K)
        (r := r)
        (R := R)
        (z := z)
        (tau := tau)
        (hK := hK)
        (hR := hR)
        (hbound := hbound)
        (htau := htau)
        (hrz := hrz)
        (hrR := hrR)
        (hinner := hinner)
        (houter := houter)⟩

/-- Uniform-constant form of
`finiteUpperHeatInEarlierScheduledRadialAnnulus_le_quadraticGaussian`;
the growth constant comes from `riemannXi_quadraticGrowth`. -/
theorem exists_finiteUpperHeatInEarlierScheduledRadialAnnulus_le_quadraticGaussian :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℝ[X]) (m : ℕ) (n : ℕ), m + 2 ≤ n → ∀ k : ℕ, k + 1 ≤ n → realPolynomialRootCountInBall P 0 (quantitativeSpectralRadialBoundary k) = riemannXiSpectralRadialDivisorCount (quantitativeSpectralRadialBoundary k) → ∀ (z : ℂ) (tau : ℝ), 0 < tau → ‖z‖ ≤ quantitativeSpectralRadialBoundary m →
      finiteUpperHyperbolicHeatSum z (realPolynomialUpperRootMultisetInRadialAnnulus P (quantitativeSpectralRadialBoundary m) (quantitativeSpectralRadialBoundary (m + 1))) tau ≤ (K * (2 * (quantitativeSpectralRadialBoundary (m + 1) + 1) + 1) ^ (2 : ℕ) / Real.log 2) * (tau⁻¹ * Real.exp (-((quantitativeSpectralRadialBoundary m - ‖z‖) ^ (2 : ℕ) * tau))) := by
  obtain ⟨K, hK, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨K, hK, fun P m n hmn hcounts z tau htau hrz => finiteUpperHeatInEarlierScheduledRadialAnnulus_le_quadraticGaussian (P := P)
        (K := K)
        (hK := hK)
        (hbound := hbound)
        (m := m)
        (n := n)
        (hmn := hmn)
        (hcounts := hcounts)
        (z := z)
        (tau := tau)
        (htau := htau)
        (hrz := hrz)⟩

/-! ## Two growth constants at once -/

/-- Vertical `L¹` bound for the negative log-derivative of `ξ` on the quantitative boundary, with
the subquadratic constant `A` from `riemannXi_threeHalvesGrowth` and the quadratic constant `B`
from `riemannXi_quadraticGrowth`. -/
theorem exists_intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_le :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ ∀ n : ℕ,
      (∫ y : ℝ in (-1 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖) ≤
        2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4)) +
          (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
              Real.log 2) *
            (4 / xiCanonicalRadius n +
              2 * Real.log (1 + 3 / spectralBoundarySeparation n)) := by
  obtain ⟨A, hA, hThreeHalves⟩ := riemannXi_threeHalvesGrowth
  obtain ⟨B, hB, hQuadratic⟩ := riemannXi_quadraticGrowth
  exact ⟨A, B, hA, hB, fun n =>
    intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_le_of_growth
      hA hThreeHalves hB hQuadratic n⟩

/-- Quantitative bound on the vertical Suzuki–Weil boundary integral at every truncation, with the
two growth constants of `ξ` supplied by the subquadratic and quadratic growth laws. -/
theorem exists_norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ ∀ (t : ℝ) (z : ℂ) (n : ℕ),
      2 * |z.re| ≤ quantitativeSpectralBoundaryTruncation n →
      ‖suzukiXiWeilVerticalBoundaryIntegral t z
          (quantitativeSpectralBoundaryTruncation n)‖ ≤
        2 * ((2 * (Real.exp |t| + 1) /
            quantitativeSpectralBoundaryTruncation n ^ 2) *
          (2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
              (xiCanonicalRadius n / 4)) +
            (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
                Real.log 2) *
              (4 / xiCanonicalRadius n +
                2 * Real.log
                  (1 + 3 / spectralBoundarySeparation n)))) := by
  obtain ⟨A, hA, hThreeHalves⟩ := riemannXi_threeHalvesGrowth
  obtain ⟨B, hB, hQuadratic⟩ := riemannXi_quadraticGrowth
  exact ⟨A, B, hA, hB, fun t z n hzT =>
    norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le_of_growth
      hA hThreeHalves hB hQuadratic t z n hzT⟩

end RiemannGaussian
