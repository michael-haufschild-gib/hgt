import GaloisForLFunctions.RHTower.HedenmalmStokesCurvatureNormalizedFluxBudget
import GaloisForLFunctions.RHTower.HedenmalmCentralBandGaussianHankel

/-!
# Central-band propagation of the curvature-normalized Stokes budget

P-G144 isolates the curvature-normalized completed-flux budget as the exact remaining Route P
condition.  The endpoint-quartet source geometry already supplies more transverse propagation than
the positive real ray: every exact quartet-admissible frequency band has the raw completed-flux
sign at every positive aperture.

This module transports that sign to the curvature-normalized budget and proves an exact
localization theorem.  On the concrete source-produced band `|Im s| <= 218 / 25`, the budget is
unconditional.  Consequently its RH-equivalent content is precisely the two high-frequency tails
`218 / 25 < |Im s|`.

No RH premise, zero computation, or added axiom enters the central-band theorem.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The curvature-normalized right-strip budget restricted to frequencies outside a symmetric
central band. -/
def HedenmalmCurvatureNormalizedRightTailBudget (R : ℝ) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → R < |s.im| → riemannZeta s ≠ 0 →
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re

/-- Every exact endpoint-quartet band carries the raw completed-flux dissipativity sign throughout
all positive apertures. -/
theorem seamFluxCochain_re_nonpos_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ R) :
    (seamFluxCochain s).re ≤ 0 := by
  let a : ℝ := s.re - 1 / 2
  let b : ℝ := s.im
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  let zplus : ℂ := (b : ℂ) + (a : ℂ) * I
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hzplusIm : 0 < zplus.im := by
    simp only [zplus, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_add, zero_mul, mul_one]
    simpa using ha
  have hzplusRe : |zplus.re| ≤ R := by
    simpa only [zplus, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, b] using hfreq
  have hXiPlus : XiC zplus ≠ 0 :=
    XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand
      R hband zplus hzplusIm hzplusRe
  have hconj : (starRingEnd ℂ) zplus = z := by
    apply Complex.ext <;>
      simp [z, zplus, mul_re, mul_im]
  have hXi : XiC z ≠ 0 := by
    simpa only [hconj] using XiC_ne_zero_conj hXiPlus
  have htrace :=
    xiRelativeResolventTrace_im_nonneg_lower_exactOffLineQuartetBand
      R hband ha hfreq
  have hcoord : (1 / 2 : ℂ) + z * I = s := by
    apply Complex.ext <;>
      simp [z, a, b, mul_re, mul_im]
  rw [xiRelativeResolventTrace_eq_completedFlux hXi, hcoord] at htrace
  simp only [mul_im, neg_re, neg_im, I_re, I_im, zero_mul, neg_zero] at htrace
  linarith

/-- **Unconditional transverse propagation.**  Every exact endpoint-quartet band satisfies the
P-G144 curvature allowance pointwise throughout the positive-aperture half-plane. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_budget_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ R) :
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re := by
  have hraw := seamFluxCochain_re_nonpos_of_exactOffLineQuartetBand
    R hband hhalf hfreq
  have him := deriv_seamFluxCochain_one_half_im_eq_zero
  rw [hedenmalmCurvatureNormalizedSeamFlux,
    hedenmalmCurvatureNormalizedFlux]
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im]
  rw [him, mul_zero, sub_zero]
  norm_num
  linarith

/-- Concrete source-produced curvature budget on the full rational central band. -/
theorem hedenmalmCurvatureNormalizedSeamFlux_budget_twoHundredEighteen_twentyFifths
    {s : ℂ} (hhalf : 1 / 2 < s.re) (hfreq : |s.im| ≤ 218 / 25) :
    (hedenmalmCurvatureNormalizedSeamFlux s).re ≤
      -(s.re - 1 / 2) * (deriv seamFluxCochain (1 / 2)).re := by
  exact hedenmalmCurvatureNormalizedSeamFlux_budget_of_exactOffLineQuartetBand
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths
    hhalf hfreq

/-- **Exact central-band/tail gluing law.**  Once an exact endpoint-quartet band is available, the
global P-G144 right-strip budget is equivalent to its restriction to the two exterior frequency
tails. -/
theorem hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    HedenmalmCurvatureNormalizedRightTailBudget R ↔
      HedenmalmCurvatureNormalizedRightBudget := by
  constructor
  · intro htail s hhalf hone hzeta
    by_cases hhigh : R < |s.im|
    · exact htail s hhalf hone hhigh hzeta
    · exact hedenmalmCurvatureNormalizedSeamFlux_budget_of_exactOffLineQuartetBand
        R hband hhalf (le_of_not_gt hhigh)
  · intro hglobal s hhalf hone _hhigh hzeta
    exact hglobal s hhalf hone hzeta

/-- On the sharpened source-produced central band, only the two high-frequency tails retain any
RH-bearing content. -/
theorem hedenmalmCurvatureNormalizedRightTailBudget_twoHundredEighteen_twentyFifths_iff_rh :
    HedenmalmCurvatureNormalizedRightTailBudget (218 / 25) ↔
      RiemannHypothesis := by
  rw [hedenmalmCurvatureNormalizedRightTailBudget_iff_rightBudget_of_exactOffLineQuartetBand
      (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths,
    hedenmalmCurvatureNormalizedRightBudget_iff_riemannHypothesis]

end

end RHTower
