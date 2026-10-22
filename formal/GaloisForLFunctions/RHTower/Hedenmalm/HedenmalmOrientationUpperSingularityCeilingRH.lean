import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmOrientationResidues

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

/-- Under RH and at positive aperture, both Xi arguments in the canonical orientation multiplier
are regular at every frequency strictly above the aperture line. -/
theorem canonicalOrientation_analyticAt_of_riemannHypothesis
    {a : ℝ} (ha : 0 < a) (hRH : RiemannHypothesis) {b : ℂ} (hb : a < b.im) :
    AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a) b := by
  let s : ℂ := (1 : ℂ) / 2 + (a : ℂ) + b * I
  let t : ℂ := (1 : ℂ) / 2 + (a : ℂ) - b * I
  have hsre : s.re < 1 / 2 := by
    dsimp only [s]
    norm_num [Complex.div_re, Complex.mul_re]
    linarith
  have htRe : 1 / 2 < t.re := by
    dsimp only [t]
    norm_num [Complex.div_re, Complex.mul_re]
    linarith
  have hsReflectRight : 1 - s ∈ rightHalf := by
    rw [mem_rightHalf]
    simp only [sub_re, one_re]
    linarith
  have hsReflectNe : xi (1 - s) ≠ 0 :=
    (rh_iff_xi_ne_zero_right.mp hRH) (1 - s) hsReflectRight
  have hsNe : xi s ≠ 0 := by
    rw [xi_one_sub] at hsReflectNe
    exact hsReflectNe
  have htNe : xi t ≠ 0 :=
    (rh_iff_xi_ne_zero_right.mp hRH) t (mem_rightHalf.mpr htRe)
  have hlogS : AnalyticAt ℂ (logDeriv xi) s := by
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) s
    exact (xi_analyticOnNhd_univ s (Set.mem_univ s)).deriv.div
      (xi_analyticOnNhd_univ s (Set.mem_univ s)) hsNe
  have hlogT : AnalyticAt ℂ (logDeriv xi) t := by
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) t
    exact (xi_analyticOnNhd_univ t (Set.mem_univ t)).deriv.div
      (xi_analyticOnNhd_univ t (Set.mem_univ t)) htNe
  have hinnerS : AnalyticAt ℂ
      (fun z : ℂ => (1 : ℂ) / 2 + (a : ℂ) + z * I) b := by
    fun_prop
  have hinnerT : AnalyticAt ℂ
      (fun z : ℂ => (1 : ℂ) / 2 + (a : ℂ) - z * I) b := by
    fun_prop
  have hfirst : AnalyticAt ℂ
      (fun z : ℂ => logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) + z * I)) b := by
    exact hlogS.comp (f := fun z : ℂ =>
      (1 : ℂ) / 2 + (a : ℂ) + z * I) hinnerS
  have hsecond : AnalyticAt ℂ
      (fun z : ℂ => logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) - z * I)) b := by
    exact hlogT.comp (f := fun z : ℂ =>
      (1 : ℂ) / 2 + (a : ℂ) - z * I) hinnerT
  change AnalyticAt ℂ (fun z : ℂ =>
    logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) + z * I) +
      logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) - z * I)) b
  exact hfirst.add hsecond

/-- RH discharges the one-aperture upper-singularity ceiling at every positive aperture. -/
theorem orientationUpperSingularityCeiling_of_riemannHypothesis
    {a : ℝ} (ha : 0 < a) (hRH : RiemannHypothesis) :
    XiCanonicalOrientationUpperSingularityCeiling a := by
  intro b hsingular
  by_contra hnot
  exact hsingular
    (canonicalOrientation_analyticAt_of_riemannHypothesis ha hRH
      (lt_of_not_ge hnot))

/-- **Exact canonical-orientation singularity-ceiling criterion for RH.** -/
theorem orientationUpperSingularityCeiling_iff_riemannHypothesis
    {a : ℝ} (ha : 0 < a) :
    XiCanonicalOrientationUpperSingularityCeiling a ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_orientationUpperSingularityCeiling ha,
    orientationUpperSingularityCeiling_of_riemannHypothesis ha⟩

/-- Under RH the canonical orientation multiplier is analytic throughout the strict upper
frequency half-plane. -/
theorem canonicalOrientation_analyticOnNhd_upperHalfPlane_of_riemannHypothesis
    {a : ℝ} (ha : 0 < a) (hRH : RiemannHypothesis) :
    AnalyticOnNhd ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      {b : ℂ | a < b.im} := by
  intro b hb
  exact canonicalOrientation_analyticAt_of_riemannHypothesis ha hRH hb

/-- **Exact upper-half-plane analyticity criterion for RH.** -/
theorem canonicalOrientation_analyticOnNhd_upperHalfPlane_iff_riemannHypothesis
    {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ (xiCanonicalHorizontalOrientationMultiplier a)
        {b : ℂ | a < b.im} ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_canonicalOrientation_analyticOnNhd_upperHalfPlane ha,
    canonicalOrientation_analyticOnNhd_upperHalfPlane_of_riemannHypothesis ha⟩

end

end RHTower
