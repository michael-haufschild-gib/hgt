import GaloisForLFunctions.RHTower.XiShiftedArcsineVacuumCompletedSourceCharge
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRecessionFlow

/-!
# Mixed mass flow of the pole-free completed arithmetic source charge

The arcsine-vacuum source charge has a native squared-mass evolution.  Its derivative is the
negative of three current-admission terms: next completed arithmetic layer, inverse-Hankel
admission connection, and newborn-norm vacuum flux.  This is the missing mixed mass--admission
law; no fixed-mass transport curvature or posterior wall reporter occurs.

The exact mean-value budget shows that every finite charge loss is paid by this same density at
one interior mass.  No pointwise sign is asserted.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Squared-mass form of the pole-free completed source charge. -/
def xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n -
    32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
      xiShiftedCanonicalAdmissionNorm y (n + 1)

/-- Native mixed mass density of the pole-free source charge. -/
def xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass y n -
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n +
    32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
      xiShiftedCanonicalAdmissionNormFlux y (n + 1)

/-- Actual moving coefficient source is exactly twice current canonical adaptive shear. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_two_mul_adaptiveShear
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n =
      2 * xiShiftedCanonicalAdmissionAdaptiveShear y n := by
  rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass,
    xiShiftedAdaptiveBilinearCoefficientSourceMass_eq_momentFunctional hy]
  simp only [finitePolynomialVelocity, xiShiftedCanonicalAdmissionCurve,
    HTGeometry.monicMomentAdmissionPolynomial,
    HTGeometry.finiteHankelNullPolynomial,
    xiShiftedCanonicalAdmissionAdaptiveShear, HTGeometry.momentInner_def,
    xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
    HTGeometry.momentFunctional_add]
  ring

/-- Source-mass charge agrees with pole-free completed source charge at every positive mass. -/
theorem xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_eq
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass y n =
      xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge y n := by
  rw [xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass,
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_two_mul_adaptiveShear hy]

/-- Square-mass presentation is the literal adaptive mixed rational--Gamma/von-Mangoldt source
minus current newborn-norm arcsine vacuum. -/
theorem xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_sq_eq_literal
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass (w ^ (2 : ℕ)) n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) -
        32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := by
  rw [xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic hw]

/-- Fixed-degree newborn admitted norm tends to zero in square-root mass coordinates.  The proof
uses completed source itself as the dominating function; no moment computation is needed. -/
theorem tendsto_xiShiftedCanonicalAdmissionNorm_succ_square_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1))
      atTop (nhds 0) := by
  have hsource :=
    XiShiftedCanonicalAdmission.tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_square_zero hn
  have hupper : Tendsto
      (fun w : ℝ =>
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ (2 : ℕ)) n /
          (2 * (n + 1 : ℝ))) atTop (nhds 0) := by
    simpa using hsource.div_const (2 * (n + 1 : ℝ))
  have hevent : ∀ᶠ w : ℝ in atTop,
      0 ≤ xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) ∧
      xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) ≤
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ (2 : ℕ)) n /
          (2 * (n + 1 : ℝ)) := by
    filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2),
      eventually_gt_atTop (1 : ℝ)] with w hH hw
    let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re
    have hheadN : (HTGeometry.momentHankelMatrix s n).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    have hheadNext : (HTGeometry.momentHankelMatrix s (n + 1)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
        HTGeometry.monicOrtho s n := by
      exact xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hheadN
    have hNeq : xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) =
        HTGeometry.monicOrthoNormSq s (n + 1) := by
      exact xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hheadNext
    have hs : xiShiftedRealMomentSequence w = s := by rfl
    have hNpos : 0 < xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := by
      rw [hNeq]
      exact HTGeometry.monicOrthoNorm_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
    have hsplit :=
      xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_gaussBulk_add_nextEdge
        (by linarith : 1 / 2 < w) hn hH
    have hbulk := xiShiftedAdaptiveGaussArithmeticBulk_pos hn hH
    have hsourceEq :=
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic
        (by linarith : 1 / 2 < w) n
    rw [hs] at hsplit hsourceEq
    constructor
    · exact hNpos.le
    · rw [hsourceEq, hP, hNeq, hsplit]
      have hden : 0 < 2 * (n + 1 : ℝ) := by positivity
      apply (le_div_iff₀ hden).2
      nlinarith
  exact squeeze_zero' (hevent.mono fun _ h => h.1)
    (hevent.mono fun _ h => h.2) hupper

/-- Fixed-degree newborn norm also tends to zero in squared-mass coordinate. -/
theorem tendsto_xiShiftedCanonicalAdmissionNorm_succ_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => xiShiftedCanonicalAdmissionNorm y (n + 1))
      atTop (nhds 0) := by
  have h := (tendsto_xiShiftedCanonicalAdmissionNorm_succ_square_zero hn).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply, Real.sq_sqrt hy]

/-- Pole-free completed source charge tends to zero at every fixed positive degree. -/
theorem tendsto_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun y : ℝ =>
        xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass y n)
      atTop (nhds 0) := by
  have hsource :=
    XiShiftedCanonicalAdmission.tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_zero hn
  have hnorm := tendsto_xiShiftedCanonicalAdmissionNorm_succ_zero hn
  have hscaled : Tendsto
      (fun y : ℝ => 32 *
        XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
          xiShiftedCanonicalAdmissionNorm y (n + 1)) atTop (nhds 0) := by
    simpa using hnorm.const_mul
      (32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n)
  simpa [xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass] using
    hsource.sub hscaled

/-- **Exact mixed mass--admission source law.**  On every positive finite chamber, pole-free
completed charge differentiates to negative next-layer/connection/vacuum-flux density. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass
    {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass v n)
      (-xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity y n) y := by
  have hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0 :=
    xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hnextH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hsource :=
    hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass hy n hdet
  have hnorm := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
    hy (by omega : 0 < n + 1) (ne_of_gt hnextH.det_pos)
  have h := hsource.sub
    (hnorm.const_mul
      (32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n))
  change HasDerivAt
    ((fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n) -
      (fun v => 32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
        xiShiftedCanonicalAdmissionNorm v (n + 1)))
    (-xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity y n) y
  apply h.congr_deriv
  unfold xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity
  ring

/-- **Exact finite mass budget.**  Every pole-free source-charge loss across one positive chamber
is paid by the native mixed density at an interior mass. -/
theorem exists_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_secant
    {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hchamber : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    ∃ c ∈ Ioo a b,
      (b - a) *
          xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity c n =
        xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass a n -
          xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass b n := by
  let f := fun y : ℝ =>
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass y n
  let f' := fun y : ℝ =>
    -xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity y n
  have hflow : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y := by
    intro y hy
    exact hasDerivAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass
      (ha.trans_le hy.1) (hchamber y hy)
  have hcont : ContinuousOn f (Icc a b) := by
    intro y hy
    exact (hflow y hy).continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y := by
    intro y hy
    exact hflow y ⟨hy.1.le, hy.2.le⟩
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  refine ⟨c, hc, ?_⟩
  dsimp only [f, f'] at hslope ⊢
  have hden : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hslope' := (eq_div_iff hden).mp hslope
  linarith

/-- **Strict-frontier mass discharge.**  Every occupied strict frontier forces a strictly positive
native mixed source-charge density at some later mass.  This converts local positive arithmetic
charge into actual mass-flow action without dividing by the newborn norm. -/
theorem exists_pos_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity_after_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    let d := n + 1
    ∃ b c : ℝ, y < b ∧ c ∈ Ioo y b ∧
      0 < xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity c d ∧
      (b - y) *
          xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity c d =
        xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass y d -
          xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass b d := by
  dsimp only
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let f := fun v : ℝ =>
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass v d
  let density := fun v : ℝ =>
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeDensity v d
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hfy : 0 < f y := by
    rw [show f y =
        xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge y d by
      exact xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_eq hy d]
    simpa only [f, d, y] using
      xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_pos_at_strict_frontier
        hne hstrict
  have hlim : Tendsto f atTop (nhds 0) := by
    simpa only [f, d] using
      tendsto_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_zero
        (by omega : 0 < d)
  have hsmall := hlim.eventually
    (Iio_mem_nhds (by linarith : (0 : ℝ) < f y / 2))
  obtain ⟨b, hbsmall, hyb⟩ := (hsmall.and (eventually_gt_atTop y)).exists
  have hfdrop : f b < f y := by linarith
  have hcontY : ContinuousAt f y := by
    have hcharge :=
      continuousAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_at_strict_frontier
        hne hstrict
    apply ContinuousAt.congr_of_eventuallyEq hcharge
    filter_upwards [Ioi_mem_nhds hy] with v hv
    simpa only [f, d] using
      xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass_eq hv d
  have hchamber : ∀ v, y < v →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (d + 2)).PosDef := by
    intro v hv
    have hv0 : 0 ≤ v := (hy.trans hv).le
    simpa only [d, y] using
      (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) hv0 hv)
  have hcont : ContinuousOn f (Icc y b) := by
    intro v hv
    by_cases hvy : v = y
    · subst v
      exact hcontY.continuousWithinAt
    · have hyv : y < v := lt_of_le_of_ne hv.1 (Ne.symm hvy)
      exact (hasDerivAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass
        (hy.trans hyv) (hchamber v hyv)).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Ioo y b, HasDerivAt f (-density v) v := by
    intro v hv
    exact hasDerivAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceChargeMass
      (hy.trans hv.1) (hchamber v hv.1)
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f (fun v => -density v) hyb hcont hderiv
  have hden : b - y ≠ 0 := sub_ne_zero.mpr hyb.ne'
  have hslope' := (eq_div_iff hden).mp hslope
  have hbudget : (b - y) * density c = f y - f b := by
    dsimp only [f, density] at hslope' ⊢
    linarith
  have hdensity : 0 < density c := by
    have hlength : 0 < b - y := sub_pos.mpr hyb
    have hpay : 0 < f y - f b := sub_pos.mpr hfdrop
    rw [← hbudget] at hpay
    nlinarith
  exact ⟨b, c, hyb, hc, hdensity, hbudget⟩

end

end RHTower
