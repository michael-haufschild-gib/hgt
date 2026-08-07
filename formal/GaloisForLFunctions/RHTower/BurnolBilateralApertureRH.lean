import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinReflection
import GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientOrder
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.BurnolSoninCrossApertureRiesz

/-!
# The source-side consumers of the bilateral aperture-defect energy law

The signed bilateral defect energy of Burnol's continuous evaluation vector is
`(r^(2 Re w - 1) - r^(1 - 2 Re w)) ‖k_{w,a}‖²`.  Since the evaluation vector is never zero on the
open right half of the critical strip, the sign of that energy is exactly the sign of
`Re w - 1/2`.  Consequently a one-sided defect contraction on the actual zeta zeros of the right
half strip, the corresponding order on the finite aperture holonomy, and the nonpositivity of the
source-defined co-Poisson Berezin reader are each equivalent to the Riemann hypothesis in the
forward direction.

Every hypothesis below is a statement about the concrete Sonine carrier and the concrete finite
holonomy; none mentions a chosen zero, a zero enumeration, or an Xi-divisor-built object.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- **Strict orientation of the bilateral defect energy on a right-half strip point.** -/
theorem burnolExtended_bilateralApertureDefects_lt_of_half_lt_re
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 1 < r) :
    ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ <
      ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ :=
  (burnolExtended_bilateralApertureDefects_oriented_right_iff hlo hhi ha hr
    (burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1)).mpr hlo

/-- **The bilateral defect contraction on the actual zeta zeros implies RH.**

This is the unconditional form of the top-down chain of the bilateral aperture-defect energy law:
a source-side inequality between the inverse- and forward-dilation cross-aperture defect energies
at every zeta zero of the open right half strip leaves no such zero at all. -/
theorem riemannHypothesis_of_burnol_bilateral_defect_le
    {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r)
    (h : ∀ (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1), riemannZeta w = 0 →
      ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ≤
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hlo hhi hzero
  have hstrict := burnolExtended_bilateralApertureDefects_lt_of_half_lt_re hlo hhi ha ha1 hr
  exact absurd (h s hlo hhi hzero) (not_le.mpr hstrict)

/-- **The exact source criterion.**  On the open right half strip the defect energies are balanced
at a point exactly when that point is not a zeta zero, so RH is exactly the statement that the
defects are never balanced there. -/
theorem riemannHypothesis_iff_burnol_bilateral_defects_ne
    {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r) :
    RiemannHypothesis ↔
      ∀ (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1), riemannZeta w = 0 →
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ≤
          ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ := by
  constructor
  · intro hRH w hlo hhi hzero
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip] at hRH
    exact absurd hzero (hRH w hlo hhi)
  · exact riemannHypothesis_of_burnol_bilateral_defect_le ha ha1 hr

/-- **The compressed-holonomy quadratic form is strictly positive on a right-half zero fibre.** -/
theorem re_inner_burnolExtendedBilateralApertureHolonomy_pos
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 1 < r) :
    let b : ℝ := r⁻¹ * a
    let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
    0 < (⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
      burnolExtendedBilateralApertureHolonomy a ha r hr
        (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)⟫_ℂ).re := by
  intro b hb
  have hval := burnolExtended_bilateralApertureDefectEnergy_eq_holonomy hlo hhi ha hr
  have henergy := burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr
  have hne : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
    burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1
  have hpos : 0 < ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hcoeff : 0 < r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re) :=
    (burnol_rpowOrientation_pos_iff r w.re hr).mpr hlo
  have hchain : 0 < ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
      ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 := by
    rw [henergy]
    exact mul_pos hcoeff hpos
  rw [hval] at hchain
  exact hchain

/-- **The finite-holonomy order on the actual zeta-zero fibres implies RH.**

This discharges the top-down chain of the co-Poisson quotient bilateral-order law: any order that
makes the finite bilateral aperture holonomy nonpositive on the evaluation vectors of the actual
zeta zeros of the right half strip already excludes those zeros. -/
theorem riemannHypothesis_of_burnolExtendedBilateralApertureHolonomy_nonpos
    {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r)
    (h : ∀ (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1), riemannZeta w = 0 →
      (⟪(burnolExtendedSoninEvaluationVector w (r⁻¹ * a) hlo hhi
            (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha) : evenSubspace),
        burnolExtendedBilateralApertureHolonomy a ha r hr
          (burnolExtendedSoninEvaluationVector w (r⁻¹ * a) hlo hhi
            (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha) : evenSubspace)⟫_ℂ).re ≤ 0) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hlo hhi hzero
  have hpos := re_inner_burnolExtendedBilateralApertureHolonomy_pos hlo hhi ha ha1 hr
  exact absurd (h s hlo hhi hzero) (not_le.mpr hpos)

/-- **The normalized co-Poisson Berezin reader is strictly positive on a right-half annihilator
fibre.**  This is the exact fibre value `2 sinh (2 log r (Re w - 1/2))` of the Berezin diagonal
reflection law, now with its sign, because the evaluation vector is never zero. -/
theorem burnolCoPoissonNormalizedHolonomy_pos_of_annihilator
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 1 < r)
    (hann : BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha)) :
    0 < burnolCoPoissonNormalizedHolonomy hlo hhi ha hr := by
  rw [burnolCoPoissonNormalizedHolonomy_eq_two_sinh_of_annihilator hlo hhi ha hr hann
    (burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1)]
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have harg : 0 < 2 * Real.log r * (w.re - 1 / 2) := by
    have : 0 < w.re - 1 / 2 := by linarith
    positivity
  have := Real.sinh_pos_iff.mpr harg
  linarith

/-- **No right-half co-Poisson annihilator character survives a nonpositive Berezin reader.**

This is the exact contrapositive of the top-down reduction of the Berezin diagonal reflection law:
the normalized finite-holonomy Berezin value is strictly positive on every right-half annihilator
fibre, so a source theorem forcing it to be nonpositive leaves no such fibre. -/
theorem not_burnolCoPoissonAnnihilatorPoint_of_normalizedHolonomy_nonpos
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 1 < r) (hnonpos : burnolCoPoissonNormalizedHolonomy hlo hhi ha hr ≤ 0) :
    ¬ BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha) := by
  intro hann
  exact absurd hnonpos
    (not_le.mpr (burnolCoPoissonNormalizedHolonomy_pos_of_annihilator hlo hhi ha ha1 hr hann))


/-! ## The aperture-type law without its nonvanishing premise -/

/-- **Unconditional aperture-type exponent.**  The logarithmic growth of the norms of the
completed-Mellin evaluation vectors along a geometric aperture tower is exactly the horizontal
displacement `|Re w - 1/2|`, at every point of the open right half of the critical strip.  The
nonzero-fibre premise of the two-sided law is now discharged. -/
theorem tendsto_log_norm_burnolExtendedSoninEvaluationVector_unconditional
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 1 < r) :
    Filter.Tendsto
      (fun N : ℕ => Real.log ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans hr) N)) ha)‖ / (N * Real.log r))
      Filter.atTop (nhds |w.re - 1 / 2|) :=
  tendsto_log_norm_burnolExtendedSoninEvaluationVector hlo hhi ha hr
    (burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1)

/-! ## The co-Poisson quotient evaluation vectors -/

/-- **The co-Poisson quotient evaluation vector is nonzero on a right-half annihilator fibre.**

On an annihilator fibre the quotient kernel is the ambient Sonine kernel, and that kernel never
vanishes on the open right half of the critical strip.  This is the quotient-side counterpart of
the annihilation statement: the co-Poisson quotient is inhabited by the actual evaluation vector
at every such point. -/
theorem burnolCoPoissonQuotientEvaluationVector_ne_zero_of_annihilator
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hann : BurnolCoPoissonAnnihilatorPoint w b hlo hhi hb) :
    burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb ≠ 0 := by
  intro hzero
  have hcoe := coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator hlo hhi hb hann
  rw [hzero] at hcoe
  have hk : (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) = 0 := by
    rw [← hcoe]
    rfl
  exact burnolExtendedSoninEvaluationVector_ne_zero hlo hhi hb hb1 (Subtype.ext hk)

end RHTower
