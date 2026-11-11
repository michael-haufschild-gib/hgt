import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingDetectsTheCompleteWeilFormDomain
import GaloisForLFunctions.SquareRootThreshold.PolarGroundEnergyAndPoleFreeLagAbscissaBridge

/-!
# The clock regulator lies below Weil's form

The clock regulator of an aperture replaces the archimedean jump energy of Weil's form by the
damped energy `∫ a_r(t) ‖τ_t f − f‖² dt`, `0 ≤ r < 1`, and keeps the polar and prime terms. The
damped kernels increase with `r`, so the regulated forms `E_r` increase to Weil's form `W`.

* `greenWeilEnergy_mono`: `E_r ≤ E_s` for `r ≤ s < 1`.
* `greenWeilEnergy_le_form`: `E_r ≤ W` on the form domain, at every cutoff.
* `greenWeilEnergy_neg_of_form_neg`: a negative direction of Weil's form is a negative
  direction of the regulator at every cutoff.
* `riemannHypothesis_of_greenWeilEnergy_nonneg`: a sign of the regulator at one cutoff for
  each aperture gives the Riemann hypothesis.
* `riemannHypothesis_of_greenWeilEnergy_floor`: so does a floor `−C‖f‖²` with one constant for
  all large apertures.

At every cutoff the regulator has at least the negative directions of its limit. A sign, a
floor or a bound for the negative index before the limit is at least as strong as the same
statement for Weil's form: the clock supplies no unit gap.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open _root_.RHTower HyperbolicArakelovTheory

/-- The regulated forms increase with the cutoff. -/
theorem greenWeilEnergy_mono (a : SuzukiPositiveAperture) {r s : ℝ} (hr0 : 0 ≤ r)
    (hrs : r ≤ s) (hs1 : s < 1) (f : suzukiApertureHilbert a) :
    greenWeilEnergy a r f ≤ greenWeilEnergy a s f := by
  have h := greenJumpEnergy_mono hr0 hrs hs1 f.1
  unfold greenWeilEnergy
  linarith only [h]

/-- **The regulator lies below Weil's form** at every cutoff. -/
theorem greenWeilEnergy_le_form (a : SuzukiPositiveAperture) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (u : CCMArchimedeanFormDomain a) :
    greenWeilEnergy a r (ccmArchimedeanFormToAperture a u) ≤
      (ccmRestrictedWeilForm a u u).re := by
  refine ge_of_tendsto (tendsto_greenWeilEnergy_form a u) ?_
  filter_upwards [Ioo_mem_nhdsLT hr1] with s hs
  exact greenWeilEnergy_mono a hr0 hs.1.le hs.2 _

/-- A negative direction of Weil's form is a negative direction of the regulator at every
cutoff. -/
theorem greenWeilEnergy_neg_of_form_neg (a : SuzukiPositiveAperture) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) {u : CCMArchimedeanFormDomain a} (hneg : (ccmRestrictedWeilForm a u u).re < 0) :
    greenWeilEnergy a r (ccmArchimedeanFormToAperture a u) < 0 :=
  (greenWeilEnergy_le_form a hr0 hr1 u).trans_lt hneg

/-- A floor of the regulator at one cutoff is a floor of Weil's form. -/
theorem form_floor_of_greenWeilEnergy_floor (a : SuzukiPositiveAperture) {r C : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ u : CCMArchimedeanFormDomain a, -C * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤
      greenWeilEnergy a r (ccmArchimedeanFormToAperture a u))
    (u : CCMArchimedeanFormDomain a) :
    -C * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ ccmRestrictedWeilSourceQuadratic a u := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source]
  exact (h u).trans (greenWeilEnergy_le_form a hr0 hr1 u)

/-- **A floor of the regulator gives the Riemann hypothesis.** One constant `C`, and for each
large aperture one cutoff at which the regulated form is at least `−C‖f‖²`. -/
theorem riemannHypothesis_of_greenWeilEnergy_floor {C A₀ : ℝ}
    (h : ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 → ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ u : CCMArchimedeanFormDomain a, -C * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤
        greenWeilEnergy a r (ccmArchimedeanFormToAperture a u)) :
    RiemannHypothesis := by
  rw [SquareRootThreshold.riemannHypothesis_iff_ccmRestrictedWeilPolarGroundEnergy_bddBelow]
  refine ⟨C, A₀, fun a ha => ?_⟩
  obtain ⟨r, hr0, hr1, hfloor⟩ := h a ha
  exact le_ccmRestrictedWeilPolarGroundEnergy_of_floor a fun u _ =>
    form_floor_of_greenWeilEnergy_floor a hr0 hr1 hfloor u

/-- **A sign of the regulator gives the Riemann hypothesis.** For each aperture one cutoff at
which the regulated form is nonnegative. -/
theorem riemannHypothesis_of_greenWeilEnergy_nonneg
    (h : ∀ a : SuzukiPositiveAperture, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        0 ≤ greenWeilEnergy a r (ccmArchimedeanFormToAperture a u)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_greenWeilEnergy_floor (C := 0) (A₀ := 0) fun a _ => ?_
  obtain ⟨r, hr0, hr1, hnn⟩ := h a
  refine ⟨r, hr0, hr1, fun u => ?_⟩
  rw [neg_zero, zero_mul]
  exact hnn u

end GaloisForLFunctions.FloorFreeArithmetic
