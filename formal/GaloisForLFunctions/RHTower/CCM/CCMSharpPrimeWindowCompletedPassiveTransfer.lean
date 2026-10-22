import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowPassiveNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.XiHerglotzCriterion
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# Completed passive transfer of the sharp dyadic prime source

The raw sharp-window impedance has both imaginary signs arbitrarily high in the upper half-plane.
Its canonical noncensored pole-phase normalization is nevertheless exact: subtract the
holomorphic polar-zeta and quadrature backgrounds, divide by twice the nonvanishing sharp-window
Mellin factor, and add the archimedean completion.  After the impedance-coordinate rotation, this
is literally `logDeriv XiC (-z)`.

Thus the nontrivial completed passive survivor is not a new Route-I endpoint.  Its positivity is
exactly the already-published Sondow--Dumitrescu horizontal Xi-growth criterion, with Planat's
theta-kernel representation and critical-strip localization.  The file records the exact source
handoff and its RH-equivalent sign law without an RH assumption in any theorem.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Remove the two holomorphic sharp-window backgrounds and divide by the exact nonvanishing
Mellin coupling. -/
def dyadicSharpPrimeZetaLogDerivCore (s : ℂ) : ℂ :=
  (dyadicSharpPrimeContinuedSource s -
      2 * sharpPrimeWindowMellin (Real.log 2) (3 / 2) *
        riemannZeta (s - 1 / 2) +
      2 * dyadicSharpPrimeWindowErrorSeries s) /
    (2 * sharpPrimeWindowMellin (Real.log 2) s)

/-- On the literal Dirichlet-source overlap, normalized sharp-window data recover exactly the
shifted zeta logarithmic derivative. -/
theorem dyadicSharpPrimeZetaLogDerivCore_eq
    {s : ℂ} (hs : 3 / 2 < s.re) :
    dyadicSharpPrimeZetaLogDerivCore s = zetaLogDeriv (s - 1 / 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : sharpPrimeWindowMellin (Real.log 2) s ≠ 0 :=
    sharpPrimeWindowMellin_ne_zero_of_one_lt_re hlog (by linarith)
  rw [dyadicSharpPrimeZetaLogDerivCore,
    dyadicSharpPrimeContinuedSource_eq_zetaLogDeriv hs]
  field_simp
  ring

/-- Source-side completion: pole and Gamma terms complete the normalized zeta response, while
`I` performs the impedance-coordinate rotation. -/
def dyadicSharpPrimeCompletedSourceNormalization (z : ℂ) : ℂ :=
  let s := 1 - Complex.I * z
  let t := s - 1 / 2
  Complex.I * (dyadicSharpPrimeZetaLogDerivCore s +
    t⁻¹ + (t - 1)⁻¹ + logDeriv Complex.Gammaℝ t)

/-- Canonical completed passive response already owned by horizontal Xi-growth theory. -/
def dyadicSharpPrimeCompletedPassiveResponse (z : ℂ) : ℂ :=
  logDeriv XiC (-z)

/-- **Exact Route-I to published-growth handoff.**  On the full sharp-source overlap, the
source-normalized response is literally the reflected centered-Xi logarithmic derivative. -/
theorem dyadicSharpPrimeCompletedSourceNormalization_eq_passiveResponse
    {z : ℂ} (hz : 1 / 2 < z.im) :
    dyadicSharpPrimeCompletedSourceNormalization z =
      dyadicSharpPrimeCompletedPassiveResponse z := by
  let s : ℂ := 1 - Complex.I * z
  let t : ℂ := s - 1 / 2
  have hs : 3 / 2 < s.re := by
    dsimp only [s]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    linarith
  have ht : 1 < t.re := by
    dsimp only [t]
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hcoord : 1 / 2 + (-z) * Complex.I = t := by
    dsimp only [t, s]
    ring
  rw [dyadicSharpPrimeCompletedSourceNormalization,
    dyadicSharpPrimeCompletedPassiveResponse]
  rw [dyadicSharpPrimeZetaLogDerivCore_eq hs,
    logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord,
    logDeriv_xi_eq ht, logDeriv_completedRiemannZeta_eq ht]
  simp only [t, s, zetaLogDeriv, logDeriv_apply]
  ring

/-- Global nonnegative-imaginary-part predicate for the completed response.  The nonvanishing
guard is exactly the usual logarithmic-derivative domain guard. -/
def DyadicSharpPrimeCompletedPassiveResponseNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → XiC z ≠ 0 →
    0 ≤ (dyadicSharpPrimeCompletedPassiveResponse z).im

/-- Completed Route-I passivity is exactly the classical horizontal Xi-growth RH criterion. -/
theorem dyadicSharpPrimeCompletedPassiveResponseNonnegative_iff_riemannHypothesis :
    DyadicSharpPrimeCompletedPassiveResponseNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_im_logDeriv_nonpos
    intro z hz hXi
    have hzsign := h z hz hXi
    rw [dyadicSharpPrimeCompletedPassiveResponse, logDeriv_XiC_neg,
      Complex.neg_im] at hzsign
    linarith
  · intro hRH z hz hXi
    have hzsign := im_logDeriv_XiC_nonpos_of_rh hRH hz hXi
    rw [dyadicSharpPrimeCompletedPassiveResponse, logDeriv_XiC_neg,
      Complex.neg_im]
    linarith

/-- Exact strict Sondow--Dumitrescu orientation after the dyadic source transfer: every aperture
strictly beyond a closed horizontal Xi-divisor bound has positive completed response. -/
theorem dyadicSharpPrimeCompletedPassiveResponse_im_pos_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    {z : ℂ} (hz : alpha < z.im) :
    0 < (dyadicSharpPrimeCompletedPassiveResponse z).im := by
  have hzneg : (-z).im < -alpha := by simp; linarith
  have hXi : XiC (-z) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (-z)).mp hzero
    have hqAbs : |(xiSpectralPoint q).im| ≤ alpha := by
      rw [xiSpectralPoint_im_eq]
      simpa [abs_sub_comm] using
        abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
    have hqLower : -alpha ≤ (xiSpectralPoint q).im := (abs_le.mp hqAbs).1
    have him := congrArg Complex.im hq
    linarith
  rw [dyadicSharpPrimeCompletedPassiveResponse,
    logDeriv_XiC_eq_relativeResolventTrace hXi]
  exact xiRelativeResolventTrace_im_pos_of_halfPlaneBound
    halpha hzeros (-z) hzneg

end

end RHTower
