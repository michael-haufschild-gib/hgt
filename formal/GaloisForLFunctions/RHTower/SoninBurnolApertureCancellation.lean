import GaloisForLFunctions.RHTower.SoninApertureFlagChain

/-!
# The conductor counterterm cancels the principal aperture anomaly

The extended trace of a strict aperture step is the logarithmic aperture cocycle plus a Schatten-1
residual.  The Burnol conductor at dilation ratio `b/a` extracts exactly `log(b/a)`, so subtracting
that counterterm removes the entire principal term and leaves a pure trace-class quantity.

The point is not the arithmetic of logarithms but the parameter dependence: the counterterm is a
function of the aperture ratio alone.  It contains no prime and no dilation scale, so a single
counterterm cancels the principal anomaly simultaneously at every prime of the semilocal graph.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open SoninPrincipalRelativeOperator

/-- The Burnol counterterm for one aperture step: the logarithm of the aperture ratio. -/
def soninBurnolApertureCounterterm (a b : ℝ) : ℂ := ((Real.log (b / a) : ℝ) : ℂ)

theorem soninBurnolApertureCounterterm_eq_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    soninBurnolApertureCounterterm a b = ((Real.log b - Real.log a : ℝ) : ℂ) := by
  rw [soninBurnolApertureCounterterm, Real.log_div hb.ne' ha.ne']

/-- **Exact conductor cancellation.**  Subtracting the counterterm from the extended trace of an
aperture step removes the principal term exactly, leaving the ordinary trace of the Schatten-1
shell residual.  The counterterm does not depend on the prime scale `r`, so the same subtraction
works at every prime at once. -/
theorem extendedTrace_sub_soninBurnolApertureCounterterm
    (e a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (hea : e ≤ r * a) :
    extendedTrace (soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea) -
        soninBurnolApertureCounterterm a b =
      soninApertureResidualTrace a b r hr := by
  have hb : 0 < b := ha.trans hab
  rw [extendedTrace_soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea,
    soninBurnolApertureCounterterm_eq_sub ha hb, soninApertureResidualTrace]
  ring

/-- **One counterterm for the whole semilocal graph.**  For every prime scale whose crossing
chamber contains the step, the same counterterm removes the principal anomaly. -/
theorem forall_prime_extendedTrace_sub_soninBurnolApertureCounterterm
    (e a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ r : ℝ, ∀ hr : 1 < r, ∀ hbr : b < r * a, ∀ hea : e ≤ r * a,
      extendedTrace
          (soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea) -
          soninBurnolApertureCounterterm a b =
        soninApertureResidualTrace a b r hr :=
  fun r hr hbr hea =>
    extendedTrace_sub_soninBurnolApertureCounterterm e a b r ha hab hr hbr hea

/-- The conductor-corrected aperture trace is real: the counterterm is real and the extended trace
of an aperture step is real. -/
theorem im_extendedTrace_sub_soninBurnolApertureCounterterm
    (e a b r : ℝ) (ha : 0 < a) (hab : a < b) (hr : 1 < r)
    (hbr : b < r * a) (hea : e ≤ r * a) :
    (extendedTrace (soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea) -
      soninBurnolApertureCounterterm a b).im = 0 := by
  rw [Complex.sub_im,
    im_extendedTrace_soninApertureRestrictionDefectPresentation e a b r ha hab hr hbr hea,
    soninBurnolApertureCounterterm, Complex.ofReal_im, sub_zero]

/-- **Corrected chain law.**  After the counterterm is removed at every step, the chain law of the
refinement has no principal term left: the corrected total is the sum of the corrected steps minus
the accumulated coupling energy. -/
theorem re_soninApertureResidualTrace_chain_corrected {r : ℝ} (hr : 1 < r) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hstep : ∀ i, x i < x (i + 1)) (m : ℕ) (hm : 1 ≤ m)
    (hcham : x m < r * x 0) :
    (soninApertureResidualTrace (x 0) (x m) r hr).re +
        ∑ j ∈ Finset.Ico 1 m,
          hsNormSq (evenSoninApertureSuccessiveLayerTransition
            (x 0) (x j) (x (j + 1)) r hr) =
      ∑ i ∈ Finset.range m, (soninApertureResidualTrace (x i) (x (i + 1)) r hr).re := by
  rw [re_soninApertureResidualTrace_chain hr x hx0 hstep m hm hcham]
  ring

end RHTower
