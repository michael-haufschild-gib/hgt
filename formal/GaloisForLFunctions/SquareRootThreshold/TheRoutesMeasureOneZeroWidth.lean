import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.RegularizedLogZetaAbscissa
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.PaperWoldDirectedCovarianceWidthSpectrum
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.XiThermalProjectiveMomentSpectrum
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum
import GaloisForLFunctions.RHTower.CCM.CCMSourceDivisorEnergySpectrum
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.XiSpectralApertureConservationUniversalityLaw
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.BiScaleUncertainty.PacketOneSidedGrowthLaw
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.RHTower.XiLogDerivReStripBound
import GaloisForLFunctions.RHTower.ZetaRecurrenceAtEveryPointModuloItsZeros

/-!
# The prime-side and zero-side routes measure one zero width

The walls dictionary reads the zero width `zetaZeroWidth = sup |Re ρ − ½|` in the languages of the
walls: Chebyshev deficit, mean-square band, window ceiling, lag family, ground-energy floor, heat
time and Jensen integral. This module extends the dictionary to the routes of the frontier map
whose graded receivers the corpus already owns, so that each route's "quantitative progress" is
the same number:

* **PBM** (regularized prime and `log ζ` abscissa): `zetaZeroWidth ≤ σ` iff the series
  `Σ ((Λ(n) − 1)/log n) n^{−s}` converges at every real `s > ½ + σ`, iff the regularized prime
  zeta series does (`zetaZeroWidth_le_iff_logZetaRegCoeff_converges`,
  `zetaZeroWidth_le_iff_primeRegCoeff_converges`); the `Λ − 1` series itself
  (`zetaZeroWidth_le_iff_vonMangoldtMinusOne_converges`).
* **WL** (packets and the universal spline probe): one-sided packet growth at exponent `σ` for
  every test, and the spline-weighted prime inequality at exponent `1 + σ`
  (`zetaZeroWidth_le_iff_forall_packet_upper`, `zetaZeroWidth_le_iff_spline_prime_sum_le`).
* **TT** (theta tail, Wold covariance): finite natural Wold energy at every radius `t < ½ − σ`,
  and the raw directed covariance bounded above at every such radius
  (`zetaZeroWidth_le_iff_forall_woldNatResidualSquareEnergy`,
  `zetaZeroWidth_le_iff_forall_directedCovariance_bddAbove`).
* **HCF** (Gaussian heat Hankel): the complete Gaussian Hedenmalm Hankel tail cone above `σ`
  (`zetaZeroWidth_le_iff_hedenmalmGaussianHankelTailCone`).
* **SZ** (Suzuki): zero-freeness right of the shifted critical line
  (`zetaZeroWidth_le_iff_suzukiZetaZeroFreeRightOf`).
* **TH** (thermal moments): the thermal projective moments grow at most like `σ^m`
  (`zetaZeroWidth_le_iff_forall_thermalProjectiveMoment_le`).
* **RW / HF** (CCM source tomography): analyticity of the critical Mellin defect and of the
  inverse-tilted dyadic source above `½ + σ` (`zetaZeroWidth_le_iff_criticalMellinDefectAnalyticAbove`,
  `zetaZeroWidth_le_iff_inverseTiltedDyadicSourceAnalyticAbove`).
* **FU / MC** (sharp dyadic prime windows): a dyadic weighted prime-window power bound at
  exponent `σ` (`zetaZeroWidth_le_iff_exists_dyadicWeightedPrimeWindowPowerUpper`).
* **PA** (Poisson trace): vertical type of the canonical Poisson trace at most `σ`
  (`zetaZeroWidth_le_iff_xiPoissonTraceVerticalTypeAtMost`).
* **Projective reflection radius**: the horizontal support radius of the Xi divisor is the width
  (`zetaZeroWidth_le_iff_xiProjectiveReflectionRadius_le`).
* **LA / TT / SZ / TH** (shifted and heat-flowed `Ξ`): every cosine shift `cos(hD)Ξ` with
  `h > zetaZeroWidth` is in the Laguerre–Pólya class
  (`laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt`); the unconditional `h ≥ ½` and the RH case
  `h > 0` are the two ends of the strip.

Every statement is a composition of the width dictionary with a receiver the corpus proves for the
half-plane bound `XiZeroHalfPlaneBound σ`; none supplies a bound on the width.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.Zeta23 _root_.RHTower _root_.RHTower.Sieve
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge GaloisForLFunctions.HTGeometry

/-! ### 1. Prime-side routes -/

/-- **PBM.** The width is the abscissa of the regularized `log ζ` series. -/
theorem zetaZeroWidth_le_iff_logZetaRegCoeff_converges {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ConvergesRightOf logZetaRegCoeff (1 / 2 + σ) :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges hσ)

/-- **PBM.** The width is the abscissa of the regularized prime zeta series. -/
theorem zetaZeroWidth_le_iff_primeRegCoeff_converges {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ConvergesRightOf primeRegCoeff (1 / 2 + σ) :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_primeRegCoeff_converges hσ)

/-- **WL.** The width is the abscissa of convergence of `Σ (Λ(n) − 1) n^{−s}`. -/
theorem zetaZeroWidth_le_iff_vonMangoldtMinusOne_converges {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ s : ℝ, 1 / 2 + σ < s → ∃ L : ℂ, Tendsto (fun N =>
      ∑ n ∈ Finset.range N,
        ((vonMangoldtMinusOne n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(s : ℂ))) atTop (𝓝 L) :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges hσ)

/-- **WL.** The width is the universal one-sided packet growth exponent. -/
theorem zetaZeroWidth_le_iff_forall_packet_upper {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K * Real.exp (σ * τ) :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_forall_packet_upper hσ)

/-- **WL.** The width as one spline-weighted prime inequality. -/
theorem zetaZeroWidth_le_iff_spline_prime_sum_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
      splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + σ) * τ) :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_spline_prime_sum_le hσ)

/-- **FU / MC.** The width is the exponent of the sharp dyadic weighted prime-window bound. -/
theorem zetaZeroWidth_le_iff_exists_dyadicWeightedPrimeWindowPowerUpper {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∃ N : ℕ, DyadicWeightedPrimeWindowPowerUpper σ N :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_exists_dyadicWeightedPrimeWindowPowerUpper hσ)

/-! ### 2. Theta, heat and Suzuki routes -/

/-- **TT.** The natural Wold energy is finite at every radius `t < ½ − σ` iff the width is `≤ σ`. -/
theorem zetaZeroWidth_le_iff_forall_woldNatResidualSquareEnergy {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - σ → WoldNatResidualSquareEnergy t :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ0).trans
    (xiZeroHalfPlaneBound_iff_forall_woldNatResidualSquareEnergy hσ0 hσ)

/-- **TT.** Route TT's raw signed covariance is bounded above at every radius `t < ½ − σ` iff
the width is `≤ σ`. -/
theorem zetaZeroWidth_le_iff_forall_directedCovariance_bddAbove {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - σ → ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N ≤ C :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ0).trans
    (xiZeroHalfPlaneBound_iff_forall_directedCovariance_bddAbove hσ0 hσ)

/-- **HCF.** At every Gaussian temperature the complete Hedenmalm Hankel tail cone above `σ` is
the width bound `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_iff_hedenmalmGaussianHankelTailCone {τ σ : ℝ} (hτ : 0 < τ)
    (hσ : 0 ≤ σ) : zetaZeroWidth ≤ σ ↔ HedenmalmGaussianHankelTailCone τ σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound hτ hσ).symm

/-- **SZ.** Zero-freeness right of Suzuki's shifted critical line is the width bound. -/
theorem zetaZeroWidth_le_iff_suzukiZetaZeroFreeRightOf {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ SuzukiZetaZeroFreeRightOf σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound hσ).symm

/-- **TH.** The thermal projective moments grow at most like `σ^m` iff the width is `≤ σ`. -/
theorem zetaZeroWidth_le_iff_forall_thermalProjectiveMoment_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ m : ℕ, xiThermalProjectiveMoment m ≤
      normalizedPrimeArchMoment 0 * σ ^ m :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le

/-- The horizontal support radius of the Xi divisor is the width. -/
theorem zetaZeroWidth_le_iff_xiProjectiveReflectionRadius_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ xiProjectiveReflectionRadius ≤ σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le hσ)

/-- **The width is the projective reflection radius of the Xi divisor.** -/
theorem zetaZeroWidth_eq_xiProjectiveReflectionRadius :
    zetaZeroWidth = xiProjectiveReflectionRadius :=
  le_antisymm
    ((zetaZeroWidth_le_iff_xiProjectiveReflectionRadius_le
      xiProjectiveReflectionRadius_nonneg).mpr le_rfl)
    ((zetaZeroWidth_le_iff_xiProjectiveReflectionRadius_le zetaZeroWidth_nonneg).mp le_rfl)

/-! ### 3. Operator-side and source-side routes -/

/-- **RW / HF.** The critical Mellin defect is holomorphic above `½ + σ` iff the width is `≤ σ`. -/
theorem zetaZeroWidth_le_iff_criticalMellinDefectAnalyticAbove {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ CriticalMellinDefectAnalyticAbove σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove hσ)

/-- **RW / HF.** The inverse-tilted dyadic prime source is holomorphic above `½ + σ` iff the
width is `≤ σ`. -/
theorem zetaZeroWidth_le_iff_inverseTiltedDyadicSourceAnalyticAbove {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ InverseTiltedDyadicSourceAnalyticAbove σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove hσ)

/-- **PA.** The vertical type of the canonical Poisson trace is at most `σ` iff the width is
`≤ σ`. -/
theorem zetaZeroWidth_le_iff_xiPoissonTraceVerticalTypeAtMost {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ XiPoissonTraceVerticalTypeAtMost σ :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiPoissonTraceVerticalTypeAtMost_iff_xiZeroHalfPlaneBound hσ).symm

/-! ### 3b. Zero-side routes: Lagarias' criterion and the local Bagchi criterion at width `σ` -/

/-- **LA / XN / WD.** Lagarias' criterion at width `σ`: once `zetaZeroWidth ≤ σ`, the logarithmic
derivative of `ξ` has nonnegative real part at every `s` with `Re s > ½ + σ` and `ξ(s) ≠ 0`. -/
theorem re_logDeriv_xi_nonneg_of_zetaZeroWidth_le {σ : ℝ} (hσ : zetaZeroWidth ≤ σ) {s : ℂ}
    (hs : 1 / 2 + σ < s.re) (hxi : xi s ≠ 0) : 0 ≤ (logDeriv xi s).re := by
  have hs' : 1 / 2 < s.re := by linarith [zetaZeroWidth_nonneg]
  refine re_logDeriv_xi_nonneg_of_strip_bound hs' hxi fun q => ?_
  have h := abs_re_sub_half_le_zetaZeroWidth
    (RHTower.CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q)
  have h1 : |(q.1 : ℂ).re - 1 / 2| < s.re - 1 / 2 := by linarith
  have h2 : 0 ≤ |(q.1 : ℂ).re - 1 / 2| := abs_nonneg _
  calc ((q.1 : ℂ).re - 1 / 2) ^ 2 = |(q.1 : ℂ).re - 1 / 2| ^ 2 := (sq_abs _).symm
    _ < (s.re - 1 / 2) ^ 2 := by nlinarith

/-- **BAG.** `zetaZeroWidth ≤ σ` iff every point of the strip right of `½ + σ` carries a closed
disc on which `ζ` is strongly recurrent: the local Bagchi criterion at width `σ`. -/
theorem zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ z : ℂ, 1 / 2 + σ < z.re → z.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r) := by
  rw [zetaZeroWidth_le_iff_re_le hσ]
  constructor
  · intro h z hz1 hz2
    rw [exists_zetaDiscStronglyRecurrentOn_iff_ne_zero (by linarith) hz2]
    intro hzero
    have hmem : z ∈ zetaZeroConfig.carrier :=
      show IsNontrivialZero z from ⟨hzero, by linarith, hz2⟩
    linarith [h z hmem]
  · intro h ρ hρ
    by_contra hlt
    have hlt' : 1 / 2 + σ < ρ.re := not_le.mp hlt
    exact (exists_zetaDiscStronglyRecurrentOn_iff_ne_zero (by linarith) hρ.2.2).mp
      (h ρ hlt' hρ.2.2) hρ.1

/-! ### 4. Shifted `Ξ`: the cosine shifts past the width are Laguerre–Pólya -/

/-- Every centred spectral point lies above `−h` once the shift `h` exceeds the width. -/
theorem neg_lt_im_xiSpectralPoint_of_zetaZeroWidth_lt {h : ℝ} (hh : zetaZeroWidth < h)
    (q : XiZeroCopy) : -h < (xiSpectralPoint q).im := by
  rw [xiSpectralPoint_im_eq]
  have hw := (zetaZeroWidth_le_iff_re_le zetaZeroWidth_nonneg).mp le_rfl (q.1 : ℂ)
    (RHTower.CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q)
  linarith

/-- **LA / TT / SZ / TH.** `cos(hD)Ξ` is Laguerre–Pólya for every shift `h > zetaZeroWidth`: the
shift and heat constructions of the theta routes are real-rooted exactly beyond the strip. -/
theorem laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt {h : ℝ} (hh : zetaZeroWidth < h) :
    LaguerrePolya (fun z => (XiC (z + h * Complex.I) + XiC (z - h * Complex.I)) / 2) :=
  laguerrePolya_cosineShiftXi_of_im_gt fun q => neg_lt_im_xiSpectralPoint_of_zetaZeroWidth_lt hh q

/-! ### 5. One number -/

/-- **The routes measure one zero width.** For `0 ≤ σ < ½`, the PBM abscissa law, the TT Wold
energy law, the SZ zero-free region, the TH thermal moment law, the HF/RW source tomography and
the FU/MC dyadic window law are the single statement `zetaZeroWidth ≤ σ`. -/
theorem theRoutesMeasureOneZeroWidth {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    (zetaZeroWidth ≤ σ ↔ ConvergesRightOf logZetaRegCoeff (1 / 2 + σ)) ∧
    (zetaZeroWidth ≤ σ ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - σ → WoldNatResidualSquareEnergy t) ∧
    (zetaZeroWidth ≤ σ ↔ SuzukiZetaZeroFreeRightOf σ) ∧
    (zetaZeroWidth ≤ σ ↔ ∀ m : ℕ, xiThermalProjectiveMoment m ≤
      normalizedPrimeArchMoment 0 * σ ^ m) ∧
    (zetaZeroWidth ≤ σ ↔ CriticalMellinDefectAnalyticAbove σ) ∧
    (zetaZeroWidth ≤ σ ↔ ∃ N : ℕ, DyadicWeightedPrimeWindowPowerUpper σ N) ∧
    (zetaZeroWidth ≤ σ ↔ xiProjectiveReflectionRadius ≤ σ) :=
  ⟨zetaZeroWidth_le_iff_logZetaRegCoeff_converges hσ0,
    zetaZeroWidth_le_iff_forall_woldNatResidualSquareEnergy hσ0 hσ,
    zetaZeroWidth_le_iff_suzukiZetaZeroFreeRightOf hσ0,
    zetaZeroWidth_le_iff_forall_thermalProjectiveMoment_le hσ0,
    zetaZeroWidth_le_iff_criticalMellinDefectAnalyticAbove hσ0,
    zetaZeroWidth_le_iff_exists_dyadicWeightedPrimeWindowPowerUpper hσ0,
    zetaZeroWidth_le_iff_xiProjectiveReflectionRadius_le hσ0⟩

end GaloisForLFunctions.SquareRootThreshold

end
