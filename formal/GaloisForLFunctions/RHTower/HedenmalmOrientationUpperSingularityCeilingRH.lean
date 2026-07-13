import GaloisForLFunctions.RHTower.HedenmalmOrientationResidues

/-!
# A one-aperture upper singularity ceiling forces RH

For the canonical Hedenmalm orientation multiplier `Q_a`, it is enough to exclude singularities
strictly above the horizontal line `Im b = a` at one positive aperture.  Every Xi zero reaches a
left `2a`-translation boundary after finitely many predecessor steps.  Forced singularity at that
boundary and the upper ceiling place the boundary zero on or right of the critical line.  Every
successor remains on or right of that line, and functional-equation reflection then pins every Xi
zero to the critical line.

This is a terminal analytic bridge, not a source-side proof of the ceiling and not a proof of RH.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The canonical orientation multiplier has no singularity strictly above `Im b = a`. -/
def XiCanonicalOrientationUpperSingularityCeiling (a : ℝ) : Prop :=
  ∀ b : ℂ, ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a) b → b.im ≤ a

/-- The affine Hedenmalm frequency records horizontal Xi displacement as vertical frequency. -/
theorem xiOrientationFrequencyOfPoint_im (a : ℝ) (ρ : ℂ) :
    (xiOrientationFrequencyOfPoint a ρ).im = (1 / 2 : ℝ) + a - ρ.re := by
  unfold xiOrientationFrequencyOfPoint
  simp [Complex.mul_im]

/-- Under the upper singularity ceiling, every forced left-boundary zero lies on or to the right
of the critical line. -/
theorem xiLeftShiftBoundary_re_ge_half_of_orientationUpperSingularityCeiling
    {a : ℝ} (hceiling : XiCanonicalOrientationUpperSingularityCeiling a)
    {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    (1 / 2 : ℝ) ≤ ρ.re := by
  have hsingular : ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      (xiOrientationFrequencyOfPoint a ρ) :=
    not_analyticAt_canonicalOrientation_of_xiLeftBoundary hρ
  have him := hceiling (xiOrientationFrequencyOfPoint a ρ) hsingular
  rw [xiOrientationFrequencyOfPoint_im] at him
  linarith

/-- A one-sided real-part bound on one positive translation boundary propagates to every Xi
zero.  This is the Xi-specific translation-exhaustion interface, independent of Hedenmalm data. -/
theorem xiZeroSet_re_ge_half_of_leftShiftBoundary_re_ge_half
    {h : ℝ} (hh : 0 < h)
    (hboundary : ∀ {ρ : ℂ}, ρ ∈ xiLeftShiftBoundary h → (1 / 2 : ℝ) ≤ ρ.re)
    {ρ : ℂ} (hρ : ρ ∈ xiZeroSet) :
    (1 / 2 : ℝ) ≤ ρ.re := by
  obtain ⟨n, hnBoundary⟩ := exists_nat_sub_mem_leftShiftBoundary
    (S := xiZeroSet) (fun z hz => (xiZeroSet_mem_openUnitStrip hz).1) hh hρ
  have hnRe := hboundary hnBoundary
  have hnNonneg : 0 ≤ (n : ℝ) * h :=
    mul_nonneg (Nat.cast_nonneg n) (le_of_lt hh)
  simp only [sub_re, ofReal_re] at hnRe
  linarith

/-- Functional-equation reflection upgrades a one-sided positive-translation boundary chamber to
exact critical-line placement for every Xi zero. -/
theorem xiZeroSet_re_eq_half_of_leftShiftBoundary_re_ge_half
    {h : ℝ} (hh : 0 < h)
    (hboundary : ∀ {ρ : ℂ}, ρ ∈ xiLeftShiftBoundary h → (1 / 2 : ℝ) ≤ ρ.re)
    {ρ : ℂ} (hρ : ρ ∈ xiZeroSet) :
    ρ.re = (1 / 2 : ℝ) := by
  have hright :=
    xiZeroSet_re_ge_half_of_leftShiftBoundary_re_ge_half hh hboundary hρ
  have hreflected : 1 - ρ ∈ xiZeroSet := by
    change xi (1 - ρ) = 0
    rw [xi_one_sub]
    exact hρ
  have hleft :=
    xiZeroSet_re_ge_half_of_leftShiftBoundary_re_ge_half
      hh hboundary hreflected
  simp only [sub_re, one_re] at hleft
  linarith

/-- **Positive translation-boundary criterion.**  If every left boundary zero for one positive
real translation lies on or right of the critical line, then RH follows. -/
theorem riemannHypothesis_of_xiLeftShiftBoundary_re_ge_half
    {h : ℝ} (hh : 0 < h)
    (hboundary : ∀ {ρ : ℂ}, ρ ∈ xiLeftShiftBoundary h → (1 / 2 : ℝ) ≤ ρ.re) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρright hρzero
  have hρmem : ρ ∈ xiZeroSet := hρzero
  have hre :=
    xiZeroSet_re_eq_half_of_leftShiftBoundary_re_ge_half hh hboundary hρmem
  rw [mem_rightHalf] at hρright
  linarith

/-- At every positive aperture, predecessor exhaustion transports the boundary inequality to
every Xi zero. -/
theorem xiZeroSet_re_ge_half_of_orientationUpperSingularityCeiling
    {a : ℝ} (ha : 0 < a)
    (hceiling : XiCanonicalOrientationUpperSingularityCeiling a)
    {ρ : ℂ} (hρ : ρ ∈ xiZeroSet) :
    (1 / 2 : ℝ) ≤ ρ.re := by
  apply xiZeroSet_re_ge_half_of_leftShiftBoundary_re_ge_half (h := 2 * a)
    (by linarith) (fun hboundary => ?_) hρ
  exact xiLeftShiftBoundary_re_ge_half_of_orientationUpperSingularityCeiling
    hceiling hboundary

/-- Functional-equation reflection turns the one-sided conclusion into exact critical-line
placement for every Xi zero. -/
theorem xiZeroSet_re_eq_half_of_orientationUpperSingularityCeiling
    {a : ℝ} (ha : 0 < a)
    (hceiling : XiCanonicalOrientationUpperSingularityCeiling a)
    {ρ : ℂ} (hρ : ρ ∈ xiZeroSet) :
    ρ.re = (1 / 2 : ℝ) := by
  apply xiZeroSet_re_eq_half_of_leftShiftBoundary_re_ge_half (h := 2 * a)
    (by linarith) (fun hboundary => ?_) hρ
  exact xiLeftShiftBoundary_re_ge_half_of_orientationUpperSingularityCeiling
    hceiling hboundary

/-- **One-aperture upper-singularity-ceiling criterion.**  If the canonical orientation
multiplier has no singularity above `Im b = a` for one positive `a`, then RH holds. -/
theorem riemannHypothesis_of_orientationUpperSingularityCeiling
    {a : ℝ} (ha : 0 < a)
    (hceiling : XiCanonicalOrientationUpperSingularityCeiling a) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiLeftShiftBoundary_re_ge_half (h := 2 * a)
    (by linarith)
  intro ρ hρ
  exact xiLeftShiftBoundary_re_ge_half_of_orientationUpperSingularityCeiling
    hceiling hρ

/-- Analyticity on the open upper frequency half-plane is the direct source-facing hypothesis. -/
theorem riemannHypothesis_of_canonicalOrientation_analyticOnNhd_upperHalfPlane
    {a : ℝ} (ha : 0 < a)
    (hanalytic : AnalyticOnNhd ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      {b : ℂ | a < b.im}) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_orientationUpperSingularityCeiling ha
  intro b hsingular
  by_contra hba
  have hbmem : b ∈ {w : ℂ | a < w.im} := by
    exact lt_of_not_ge hba
  exact hsingular (hanalytic b hbmem)

end

end RHTower
