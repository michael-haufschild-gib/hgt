import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRecessionConnection
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Recession budget for the actual adaptive arithmetic source

Fixed-degree source recession and the full moving source law interact nontrivially.  The actual
canonical source tends to zero while remaining positive on a terminal chamber.  Consequently its
full covariant derivative is strictly negative at cofinally many masses: the next completed
arithmetic layer strictly dominates reciprocal-admission connection there.

This is weaker than eventual monotonicity and stronger than a value recession statement.  The
remaining cofinal obstruction is synchronization: fixed-degree descent masses need not coincide
with a degree-changing first-contact schedule.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- The fixed-degree canonical literal arithmetic source itself tends to zero.  Its positive
scaled arcsine limit is multiplied by the vanishing homogeneous factor
`log w / w^(4n+5)`. -/
theorem tendsto_canonicalArithmeticSource_zero
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (sourceCoordinateAdmission w n))
      atTop (nhds 0) := by
  have hp : (0 : ℝ) < (4 * n + 5 : ℕ) := by positivity
  have hweight : Tendsto (fun w : ℝ => Real.log w / w ^ (4 * n + 5))
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      Real.tendsto_pow_log_div_pow_atTop ((4 * n + 5 : ℕ) : ℝ) 1 hp
  have hscaled := tendsto_scaled_canonicalArithmeticSource hn
  have hmul := hweight.mul hscaled
  simpa only [zero_mul] using hmul.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
    have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
    have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
    field_simp [hw0, hlog])

/-- Square-root-mass recession of the actual moving canonical source. -/
theorem tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_square_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ 2) n)
      atTop (nhds 0) := by
  have h := tendsto_canonicalArithmeticSource_zero (Nat.ne_of_gt hn)
  apply h.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n,
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually n,
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hNdet : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) n).det ≠ 0 := ne_of_gt hN.det_pos
  have hAdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n).det ≠ 0 :=
    ne_of_gt hA.det_pos
  have heq : sourceCoordinateAdmission w n =
      HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n := by
    change sourceCoordinateAdmission w n =
      HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n
    exact sourceCoordinateAdmission_eq_actualAdmission hw hn hNdet hAdet
  rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic
      (by linarith : 1 / 2 < w) n,
    ← heq]

/-- Actual squared-mass source tends to zero without retaining the square-root coordinate. -/
theorem tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun y : ℝ => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n)
      atTop (nhds 0) := by
  have h :=
    (tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_square_zero hn).comp
      Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply]
  rw [Real.sq_sqrt hy]

/-- The actual moving canonical source remains strictly positive sufficiently far right. -/
theorem eventually_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ y : ℝ in atTop,
      0 < xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n := by
  have hsquare : ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ 2) n := by
    filter_upwards [canonicalArithmeticSource_eventually_pos (Nat.ne_of_gt hn),
      xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n,
      xiShiftedMomentHankelMatrix_squareParam_posDef_eventually n,
      eventually_gt_atTop (1 : ℝ)] with w hpos hN hA hw
    have hNdet : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) n).det ≠ 0 := ne_of_gt hN.det_pos
    have hAdet : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n).det ≠ 0 :=
      ne_of_gt hA.det_pos
    have heq : sourceCoordinateAdmission w n =
        HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n := by
      change sourceCoordinateAdmission w n =
        HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n
      exact sourceCoordinateAdmission_eq_actualAdmission hw hn hNdet hAdet
    rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic
        (by linarith : 1 / 2 < w) n,
      ← heq]
    exact hpos
  have h := Real.tendsto_sqrt_atTop.eventually hsquare
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with y hpos hy
  simpa only [Function.comp_apply, Real.sq_sqrt hy] using hpos

/-- A differentiable positive tail converging to zero has strict descent points cofinally. -/
theorem exists_deriv_neg_above_of_pos_tendsto_zero
    {f : ℝ → ℝ} {A B : ℝ}
    (hlim : Tendsto f atTop (nhds 0))
    (hpos : ∀ x, A < x → 0 < f x)
    (hdiff : ∀ x, A < x → DifferentiableAt ℝ f x) :
    ∃ x, max A B < x ∧ deriv f x < 0 := by
  let C := max A B
  by_contra hnone
  push Not at hnone
  have hderiv : ∀ x, C < x → 0 ≤ deriv f x := by
    intro x hx
    exact hnone x hx
  have hCA : A ≤ C := le_max_left _ _
  have hmono : MonotoneOn f (Ioi C) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi C)
    · intro x hx
      exact (hdiff x (lt_of_le_of_lt hCA hx)).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      intro x hx
      exact (hdiff x (lt_of_le_of_lt hCA hx)).differentiableWithinAt
    · rw [interior_Ioi]
      intro x hx
      exact hderiv x hx
  let x := C + 1
  have hxC : C < x := by dsimp only [x]; linarith
  have hxpos : 0 < f x := hpos x (lt_of_le_of_lt hCA hxC)
  have hsmall := hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < f x / 2))
  obtain ⟨t, ht, hxt⟩ := (hsmall.and (eventually_gt_atTop x)).exists
  have htC : C < t := hxC.trans hxt
  have hle := hmono (Set.mem_Ioi.mpr hxC) (Set.mem_Ioi.mpr htC) hxt.le
  linarith

/-- Actual canonical adaptive source has strict descent points above every mass threshold. -/
theorem exists_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_deriv_neg_above
    {n : ℕ} (hn : 0 < n) (B : ℝ) :
    ∃ y, B < y ∧
      deriv (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n) y < 0 := by
  obtain ⟨Apos, hpos⟩ :=
    (eventually_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_pos hn
      ).exists_forall_of_atTop
  obtain ⟨Ach, hAch, hchamber⟩ :=
    exists_xiShiftedCanonicalAdmissionTerminalChamber n
  let A := max Apos Ach
  have hposA : ∀ y, A < y →
      0 < xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n := by
    intro y hy
    exact hpos y (lt_of_le_of_lt (le_max_left _ _) hy).le
  have hdiffA : ∀ y, A < y → DifferentiableAt ℝ
      (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n) y := by
    intro y hy
    have hyAch : Ach < y := lt_of_le_of_lt (le_max_right _ _) hy
    have hy0 : 0 < y := lt_of_le_of_lt hAch hyAch
    have hH := hchamber y hyAch
    have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
    exact (hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
      hy0 n hdet).differentiableAt
  obtain ⟨y, hy, hneg⟩ := exists_deriv_neg_above_of_pos_tendsto_zero
    (tendsto_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_zero hn)
    hposA hdiffA (B := B)
  exact ⟨y, lt_of_le_of_lt (le_max_right A B) hy, hneg⟩

/-- At cofinally many effective masses, next arithmetic layer strictly dominates admission
connection. -/
theorem exists_xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_strict_domination_above
    {n : ℕ} (hn : 0 < n) (B : ℝ) :
    ∃ y, B < y ∧
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n <
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass y n := by
  obtain ⟨Ach, hAch, hchamber⟩ :=
    exists_xiShiftedCanonicalAdmissionTerminalChamber n
  obtain ⟨y, hy, hneg⟩ :=
    exists_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_deriv_neg_above
      hn (max B Ach)
  have hyAch : Ach < y := lt_of_le_of_lt (le_max_right _ _) hy
  have hy0 : 0 < y := lt_of_le_of_lt hAch hyAch
  have hH := hchamber y hyAch
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
    hy0 n hdet).deriv] at hneg
  exact ⟨y, lt_of_le_of_lt (le_max_left _ _) hy, by linarith⟩

/-- Literal square-root form: cofinally, next completed rational--Gamma/von Mangoldt source
strictly dominates the bilinear inverse-Hankel connection source. -/
theorem exists_literal_xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_strict_domination_above
    {n : ℕ} (hn : 0 < n) (W : ℝ) :
    ∃ w, max (1 / 2 : ℝ) W < w ∧
      2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w
          (finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity (w ^ 2) n))
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) <
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration w n := by
  let C := max (1 / 2 : ℝ) W
  obtain ⟨y, hy, hdom⟩ :=
    exists_xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_strict_domination_above
      hn (C ^ 2)
  let w := Real.sqrt y
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_left _ _)
  have hy0 : 0 < y := lt_of_le_of_lt (sq_nonneg C) hy
  have hwC : C < w := by
    dsimp only [w]
    apply (Real.lt_sqrt hC0).2
    exact hy
  have hw : 1 / 2 < w := lt_of_le_of_lt (le_max_left _ _) hwC
  have hwsq : w ^ 2 = y := Real.sq_sqrt hy0.le
  rw [← hwsq,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass_sq_eq_arithmetic hw n,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass_sq_eq_arithmetic hw n]
    at hdom
  exact ⟨w, hwC, hdom⟩

/-- Exact secant budget: on one effective chamber, finite source loss is realized by one
pointwise excess of next arithmetic layer over admission connection. -/
theorem exists_xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_secant_domination
    {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hchamber : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    ∃ c ∈ Ioo a b,
      (b - a) *
          (xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass c n -
            xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass c n) =
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass a n -
          xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass b n := by
  let f := fun y : ℝ => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n
  let f' := fun y : ℝ =>
    -xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass y n +
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n
  have hflow : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y := by
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef (hchamber y hy)
    exact hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass hy0 n hdet
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

end
end XiShiftedCanonicalAdmission
end RHTower
