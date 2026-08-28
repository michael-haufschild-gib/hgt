import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceFifthRootDividedDropWall
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationaryCurvature
import GaloisForLFunctions.HilbertMetric.FifthRootCurvatureCusp

/-!
# Exact curvature of the theta-source fifth-root divided drop

For one reflected source fibre write `A = P(0)-P(t)`, `D=-P'(t)`, and `J=D'(t)`.
The squared-variable divided drop is `G(t²)=A/t²`.  This module identifies the exact numerator
controlling curvature of `G^(1/5)`:

`C₅ = 24A² - 9tAD + t²(5AJ - 4D²)`.

It also exposes the decomposition of `C₅` into five times the ordinary log-convexity numerator
of `G` plus the square of the already-controlled decrease defect.
-/

open Set

namespace RHTower

noncomputable section

/-- Divided drop in the natural squared-displacement coordinate. -/
def thetaCuspReflectedSourceSquaredDividedDrop (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceDividedDrop u (Real.sqrt x)

/-- First squared-variable derivative of the divided drop, in source coordinates. -/
def thetaCuspReflectedSourceSquaredDividedDropSlope (u x : ℝ) : ℝ :=
  let t := Real.sqrt x
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  (t * D - 2 * A) / (2 * t ^ 4)

/-- Second squared-variable derivative of the divided drop, in source coordinates. -/
def thetaCuspReflectedSourceSquaredDividedDropCurvature (u x : ℝ) : ℝ :=
  let t := Real.sqrt x
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  (t ^ 2 * J - 5 * t * D + 8 * A) / (4 * t ^ 6)

/-- Exact numerator of squared-variable fifth-root curvature. -/
def thetaCuspReflectedSourceFifthRootCurvatureNumerator (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  24 * A ^ 2 - 9 * t * A * D + t ^ 2 * (5 * A * J - 4 * D ^ 2)

/-- Exact numerator of ordinary log-convexity for the squared-variable divided drop. -/
def thetaCuspReflectedSourceDividedDropLogConvexityNumerator (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  4 * A ^ 2 - t * A * D + t ^ 2 * (A * J - D ^ 2)

/-- Dimensionless action form of the exact fifth-root curvature numerator. -/
def thetaCuspReflectedActionFifthRootCurvatureNumerator (u t : ℝ) : ℝ :=
  let r := Real.exp (thetaCuspReflectedLogAction u t) - 1
  let q₁ := thetaCuspReflectedLogJetOne u t
  let q₂ := thetaCuspReflectedLogJetTwo u t
  24 * r ^ 2 - 9 * t * r * q₁ +
    t ^ 2 * (5 * r * (q₂ - q₁ ^ 2) - 4 * q₁ ^ 2)

/-- Projective slope ratio of the source divided drop.  Its monotonicity is exactly the `C₅`
sign, after global divided-drop decrease makes the denominator positive. -/
def thetaCuspReflectedSourceFifthRootProjectiveRatio (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  (2 * A - t * D) / (t ^ 2 * (12 * A - t * D))

/-- Fifth-root curvature is five log-convexity numerators plus the squared decrease defect. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_five_logConvexity_add_sq
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      5 * thetaCuspReflectedSourceDividedDropLogConvexityNumerator u t +
        (2 * thetaCuspReflectedSourceFirstDrop u t -
          t * thetaCuspReflectedSourceDecayFlux u t) ^ 2 := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceDividedDropLogConvexityNumerator
  ring

/-- Negative fifth-root curvature necessarily breaks ordinary divided-drop log-convexity. -/
theorem thetaCuspReflectedSourceDividedDropLogConvexityNumerator_neg_of_fifthRoot_neg
    {u t : ℝ} (hneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0) :
    thetaCuspReflectedSourceDividedDropLogConvexityNumerator u t < 0 := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_five_logConvexity_add_sq]
    at hneg
  nlinarith [sq_nonneg
    (2 * thetaCuspReflectedSourceFirstDrop u t -
      t * thetaCuspReflectedSourceDecayFlux u t)]

/-- The first drop is the current product times the exact exponential action defect. -/
theorem thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one
    (u t : ℝ) :
    thetaCuspReflectedSourceFirstDrop u t =
      thetaCuspReflectedSourceProduct u t *
        (Real.exp (thetaCuspReflectedLogAction u t) - 1) := by
  have hP0 : 0 < thetaCuspReflectedSourceProduct u 0 := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hnorm :
      Real.exp (-thetaCuspReflectedLogAction u t) =
        thetaCuspReflectedSourceProduct u t /
          thetaCuspReflectedSourceProduct u 0 := by
    simpa [thetaCuspReflectedSourceProduct, pow_two] using
      exp_neg_thetaCuspReflectedLogAction u t
  have hmul :
      thetaCuspReflectedSourceProduct u 0 *
          Real.exp (-thetaCuspReflectedLogAction u t) =
        thetaCuspReflectedSourceProduct u t := by
    rw [hnorm]
    field_simp [hP0.ne']
  have hexp :
      Real.exp (-thetaCuspReflectedLogAction u t) *
          Real.exp (thetaCuspReflectedLogAction u t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  unfold thetaCuspReflectedSourceFirstDrop
  calc
    thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u t =
        thetaCuspReflectedSourceProduct u 0 *
              (Real.exp (-thetaCuspReflectedLogAction u t) *
                Real.exp (thetaCuspReflectedLogAction u t)) -
            thetaCuspReflectedSourceProduct u t := by rw [hexp]; ring
    _ = (thetaCuspReflectedSourceProduct u 0 *
            Real.exp (-thetaCuspReflectedLogAction u t)) *
              Real.exp (thetaCuspReflectedLogAction u t) -
          thetaCuspReflectedSourceProduct u t := by ring
    _ = thetaCuspReflectedSourceProduct u t *
          (Real.exp (thetaCuspReflectedLogAction u t) - 1) := by
      rw [hmul]
      ring

/-- Exact normalization: `C₅` is the positive source-product square times one dimensionless
action inequality involving only `q,q′,q″`. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_product_sq_mul_action
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      thetaCuspReflectedSourceProduct u t ^ 2 *
        thetaCuspReflectedActionFifthRootCurvatureNumerator u t := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
  rw [thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one]
  unfold thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedActionFifthRootCurvatureNumerator
  ring

/-- The remaining source sign is equivalently the dimensionless action sign; normalization loses
nothing because every reflected source product is strictly positive. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_action
    (u t : ℝ) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t ↔
      0 ≤ thetaCuspReflectedActionFifthRootCurvatureNumerator u t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_product_sq_mul_action]
  have hP : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  exact mul_nonneg_iff_of_pos_left (sq_pos_of_pos hP)

theorem hasDerivAt_thetaCuspReflectedSourceFirstDrop (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceFirstDrop u)
      (thetaCuspReflectedSourceDecayFlux u t) t := by
  unfold thetaCuspReflectedSourceFirstDrop
  have hraw :=
    (hasDerivAt_const t (thetaCuspReflectedSourceProduct u 0)).sub
      (hasDerivAt_thetaCuspReflectedSourceProduct u t)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring

/-- First displacement derivative of the divided drop. -/
theorem hasDerivAt_thetaCuspReflectedSourceDividedDrop
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspReflectedSourceDividedDrop u)
      ((t * thetaCuspReflectedSourceDecayFlux u t -
          2 * thetaCuspReflectedSourceFirstDrop u t) / t ^ 3) t := by
  have hA := hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have ht2 := (hasDerivAt_id t).pow 2
  have hraw := hA.div ht2 (pow_ne_zero 2 ht.ne')
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, mul_one] at hraw
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp [thetaCuspReflectedSourceDividedDrop,
      thetaCuspReflectedSourceFirstDrop]
  · field_simp [ht.ne']

/-- Global source-angle concavity makes the projective decrease defect nonnegative. -/
theorem thetaCuspReflectedSourceProjectiveDecreaseDefect_nonneg
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ 2 * thetaCuspReflectedSourceFirstDrop u t -
      t * thetaCuspReflectedSourceDecayFlux u t := by
  have hderiv := hasDerivAt_thetaCuspReflectedSourceDividedDrop u ht
  have hnonpos := hderiv.hasDerivWithinAt.nonpos_of_antitoneOn
    (isOpen_Ioi.preperfect t ht)
    (antitoneOn_thetaCuspReflectedSourceDividedDrop u)
  have ht3 : 0 < t ^ 3 := by positivity
  rcases (div_nonpos_iff.mp hnonpos) with hbad | hgood
  · exact (not_le_of_gt ht3 hbad.2).elim
  · linarith [hgood.1]

/-- The second projective denominator is strictly positive on every positive source scale. -/
theorem thetaCuspReflectedSourceProjectiveDenominator_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < 12 * thetaCuspReflectedSourceFirstDrop u t -
      t * thetaCuspReflectedSourceDecayFlux u t := by
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hdefect := thetaCuspReflectedSourceProjectiveDecreaseDefect_nonneg u ht
  nlinarith

/-- Exact projective derivative identity: fifth-root curvature is the negative projective
velocity, up to a strictly positive factor. -/
theorem hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspReflectedSourceFifthRootProjectiveRatio u)
      (-2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator u t /
        (t ^ 3 *
          (12 * thetaCuspReflectedSourceFirstDrop u t -
            t * thetaCuspReflectedSourceDecayFlux u t) ^ 2)) t := by
  have hA := hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hD := hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have htD := (hasDerivAt_id t).mul hD
  have hNraw := (hA.const_mul 2).sub htD
  have hN : HasDerivAt
      (fun s : ℝ =>
        2 * thetaCuspReflectedSourceFirstDrop u s -
          s * thetaCuspReflectedSourceDecayFlux u s)
      (thetaCuspReflectedSourceDecayFlux u t -
        t * thetaCuspReflectedSourceDecayFluxCurvature u t) t := by
    refine (hNraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hMraw := (hA.const_mul 12).sub htD
  have hM : HasDerivAt
      (fun s : ℝ =>
        12 * thetaCuspReflectedSourceFirstDrop u s -
          s * thetaCuspReflectedSourceDecayFlux u s)
      (11 * thetaCuspReflectedSourceDecayFlux u t -
        t * thetaCuspReflectedSourceDecayFluxCurvature u t) t := by
    refine (hMraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hdenRaw := ((hasDerivAt_id t).pow 2).mul hM
  have hden : HasDerivAt
      (fun s : ℝ =>
        s ^ 2 * (12 * thetaCuspReflectedSourceFirstDrop u s -
          s * thetaCuspReflectedSourceDecayFlux u s))
      (2 * t * (12 * thetaCuspReflectedSourceFirstDrop u t -
          t * thetaCuspReflectedSourceDecayFlux u t) +
        t ^ 2 * (11 * thetaCuspReflectedSourceDecayFlux u t -
          t * thetaCuspReflectedSourceDecayFluxCurvature u t)) t := by
    refine (hdenRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    ring
  have hMpos := thetaCuspReflectedSourceProjectiveDenominator_pos u ht
  have hdenne :
      t ^ 2 * (12 * thetaCuspReflectedSourceFirstDrop u t -
        t * thetaCuspReflectedSourceDecayFlux u t) ≠ 0 := by
    positivity
  have hraw := hN.div hden hdenne
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · rfl
  · unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    field_simp [ht.ne', hMpos.ne']
    ring

/-- Pointwise fifth-root curvature is exactly projective nonincrease. -/
theorem deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_nonpos_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (thetaCuspReflectedSourceFifthRootProjectiveRatio u) t ≤ 0 ↔
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t := by
  rw [(hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht).deriv]
  have hMpos := thetaCuspReflectedSourceProjectiveDenominator_pos u ht
  have hdenpos : 0 <
      t ^ 3 *
        (12 * thetaCuspReflectedSourceFirstDrop u t -
          t * thetaCuspReflectedSourceDecayFlux u t) ^ 2 := by
    positivity
  constructor
  · intro hnonpos
    rcases (div_nonpos_iff.mp hnonpos) with hbad | hgood
    · exact (not_le_of_gt hdenpos hbad.2).elim
    · nlinarith [hgood.1]
  · intro hcurv
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hdenpos.le

/-- Negative fifth-root curvature is exactly strict projective increase. -/
theorem deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_pos_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < deriv (thetaCuspReflectedSourceFifthRootProjectiveRatio u) t ↔
      thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 := by
  rw [(hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht).deriv]
  have hMpos := thetaCuspReflectedSourceProjectiveDenominator_pos u ht
  have hdenpos : 0 <
      t ^ 3 *
        (12 * thetaCuspReflectedSourceFirstDrop u t -
          t * thetaCuspReflectedSourceDecayFlux u t) ^ 2 := by
    positivity
  constructor
  · intro hpos
    rcases (div_pos_iff.mp hpos) with hgood | hbad
    · nlinarith [hgood.1]
    · exact (not_lt_of_ge hdenpos.le hbad.2).elim
  · intro hcurv
    exact div_pos (by nlinarith) hdenpos

/-- Global exact reformulation of the source fifth-root problem: `C₅` is nonnegative on every
positive displacement iff the projective ratio is antitone on the positive half-line. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_all_iff_projectiveRatio_antitone
    (u : ℝ) :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator u t) ↔
      AntitoneOn (thetaCuspReflectedSourceFifthRootProjectiveRatio u) (Ioi 0) := by
  constructor
  · intro hcurv
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro t ht
      exact
        (hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      exact
        (hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      exact
        (deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_nonpos_iff u ht).2
          (hcurv t ht)
  · intro hanti t ht
    apply
      (deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_nonpos_iff u ht).1
    have hderiv := hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht
    rw [hderiv.deriv]
    exact hderiv.hasDerivWithinAt.nonpos_of_antitoneOn
      (isOpen_Ioi.preperfect t ht) hanti

/-- Second displacement derivative of the divided drop. -/
theorem hasDerivAt_thetaCuspReflectedSourceDividedDropSlope
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ =>
        (s * thetaCuspReflectedSourceDecayFlux u s -
            2 * thetaCuspReflectedSourceFirstDrop u s) / s ^ 3)
      ((t ^ 2 * thetaCuspReflectedSourceDecayFluxCurvature u t -
          4 * t * thetaCuspReflectedSourceDecayFlux u t +
          6 * thetaCuspReflectedSourceFirstDrop u t) / t ^ 4) t := by
  have hD := hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hA := hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hnumRaw := ((hasDerivAt_id t).mul hD).sub (hA.const_mul 2)
  have hnum : HasDerivAt
      (fun s : ℝ =>
        s * thetaCuspReflectedSourceDecayFlux u s -
          2 * thetaCuspReflectedSourceFirstDrop u s)
      (t * thetaCuspReflectedSourceDecayFluxCurvature u t -
        thetaCuspReflectedSourceDecayFlux u t) t := by
    refine (hnumRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hden := (hasDerivAt_id t).pow 3
  have hraw := hnum.div hden (pow_ne_zero 3 ht.ne')
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, mul_one] at hraw
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  field_simp [ht.ne']
  ring

/-- The named squared-variable slope differentiates in displacement before square-root
composition. -/
private theorem hasDerivAt_thetaCuspReflectedSourceSquaredDropSlope_displacement
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ =>
        (s * thetaCuspReflectedSourceDecayFlux u s -
            2 * thetaCuspReflectedSourceFirstDrop u s) / (2 * s ^ 4))
      ((t ^ 2 * thetaCuspReflectedSourceDecayFluxCurvature u t -
          5 * t * thetaCuspReflectedSourceDecayFlux u t +
          8 * thetaCuspReflectedSourceFirstDrop u t) / (2 * t ^ 5)) t := by
  have hD := hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hA := hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hnumRaw := ((hasDerivAt_id t).mul hD).sub (hA.const_mul 2)
  have hnum : HasDerivAt
      (fun s : ℝ =>
        s * thetaCuspReflectedSourceDecayFlux u s -
          2 * thetaCuspReflectedSourceFirstDrop u s)
      (t * thetaCuspReflectedSourceDecayFluxCurvature u t -
        thetaCuspReflectedSourceDecayFlux u t) t := by
    refine (hnumRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hdenRaw := ((hasDerivAt_id t).pow 4).const_mul 2
  have hden : HasDerivAt (fun s : ℝ => 2 * s ^ 4) (8 * t ^ 3) t := by
    refine (hdenRaw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [id_eq]
    ring
  have hraw := hnum.div hden (by positivity : 2 * t ^ 4 ≠ 0)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  field_simp [ht.ne']
  ring

/-- Exact first squared-variable derivative of the ordinary divided drop. -/
theorem hasDerivAt_thetaCuspReflectedSourceSquaredDividedDrop
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredDividedDrop u)
      (thetaCuspReflectedSourceSquaredDividedDropSlope u x) x := by
  let t := Real.sqrt x
  have ht : 0 < t := Real.sqrt_pos.2 hx
  have hsqrt := Real.hasDerivAt_sqrt hx.ne'
  have hdrop := hasDerivAt_thetaCuspReflectedSourceDividedDrop u ht
  have hcomp := hdrop.comp x hsqrt
  unfold thetaCuspReflectedSourceSquaredDividedDrop
    thetaCuspReflectedSourceSquaredDividedDropSlope
  dsimp only [t] at hcomp ⊢
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  field_simp [ht.ne']

/-- Exact second squared-variable derivative of the ordinary divided drop. -/
theorem hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropSlope
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredDividedDropSlope u)
      (thetaCuspReflectedSourceSquaredDividedDropCurvature u x) x := by
  let t := Real.sqrt x
  have ht : 0 < t := Real.sqrt_pos.2 hx
  have hsqrt := Real.hasDerivAt_sqrt hx.ne'
  have hslope := hasDerivAt_thetaCuspReflectedSourceSquaredDropSlope_displacement u ht
  have hcomp := hslope.comp x hsqrt
  unfold thetaCuspReflectedSourceSquaredDividedDropSlope
    thetaCuspReflectedSourceSquaredDividedDropCurvature
  dsimp only [t] at hcomp ⊢
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  field_simp [ht.ne']
  ring

/-- First derivative model for the squared-variable fifth-root divided drop. -/
def thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceSquaredDividedDropSlope u x * (5 : ℝ)⁻¹ *
    thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 1)

/-- Exact second derivative model for the squared-variable fifth-root divided drop. -/
def thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature (u x : ℝ) : ℝ :=
  (25 : ℝ)⁻¹ * thetaCuspReflectedSourceSquaredDividedDrop u x ^ (-(9 : ℝ) / 5) *
    (5 * thetaCuspReflectedSourceSquaredDividedDrop u x *
        thetaCuspReflectedSourceSquaredDividedDropCurvature u x -
      4 * thetaCuspReflectedSourceSquaredDividedDropSlope u x ^ 2)

theorem thetaCuspReflectedSourceSquaredDividedDrop_pos
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspReflectedSourceSquaredDividedDrop u x := by
  unfold thetaCuspReflectedSourceSquaredDividedDrop
  exact thetaCuspReflectedSourceDividedDrop_pos u (Real.sqrt_pos.2 hx)

/-- Exact first derivative of the squared-variable fifth-root profile. -/
theorem hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)
      (thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope u x) x := by
  have hG := hasDerivAt_thetaCuspReflectedSourceSquaredDividedDrop u hx
  have hGpos := thetaCuspReflectedSourceSquaredDividedDrop_pos u hx
  have hraw := hG.rpow_const (p := (5 : ℝ)⁻¹) (Or.inl hGpos.ne')
  unfold thetaCuspReflectedSourceSquaredDividedDropFifthRoot
    thetaCuspReflectedSourceDividedDropFifthRoot
    thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope
    thetaCuspReflectedSourceSquaredDividedDrop
  exact hraw

/-- Exact second derivative of the squared-variable fifth-root profile. -/
theorem hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope u)
      (thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature u x) x := by
  have hG := hasDerivAt_thetaCuspReflectedSourceSquaredDividedDrop u hx
  have hG1 := hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropSlope u hx
  have hGpos := thetaCuspReflectedSourceSquaredDividedDrop_pos u hx
  have hpow := hG.rpow_const (p := (5 : ℝ)⁻¹ - 1) (Or.inl hGpos.ne')
  have hraw := (hG1.mul_const (5 : ℝ)⁻¹).mul hpow
  have hshift :
      thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 1) =
        thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 2) *
          thetaCuspReflectedSourceSquaredDividedDrop u x := by
    calc
      thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 1) =
          thetaCuspReflectedSourceSquaredDividedDrop u x ^
            (((5 : ℝ)⁻¹ - 2) + 1) := by
              congr 1
              ring
      _ = thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 2) *
          thetaCuspReflectedSourceSquaredDividedDrop u x ^ 1 :=
        Real.rpow_add hGpos _ _
      _ = thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 2) *
          thetaCuspReflectedSourceSquaredDividedDrop u x := by
        rw [Real.rpow_one]
  have hshift' :
      thetaCuspReflectedSourceSquaredDividedDrop u x ^
          ((5 : ℝ)⁻¹ - 1 - 1) =
        thetaCuspReflectedSourceSquaredDividedDrop u x ^ ((5 : ℝ)⁻¹ - 2) := by
    congr 1
    ring
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  unfold thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature
  rw [hshift, hshift']
  norm_num
  ring

/-- The literal second iterated derivative agrees with the exact curvature model at every
positive squared displacement. -/
theorem iteratedDeriv_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    (deriv^[2] (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)) x =
      thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature u x := by
  have hlocal :
      deriv (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u) =ᶠ[nhds x]
        thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope u := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropFifthRoot u hy).deriv
  calc
    (deriv^[2] (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)) x =
        deriv (deriv (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)) x := by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_succ_apply',
            Function.iterate_one]
    _ = deriv (thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope u) x :=
      hlocal.deriv_eq
    _ = thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature u x :=
      (hasDerivAt_thetaCuspReflectedSourceSquaredDividedDropFifthRootSlope u hx).deriv

/-- At a squared displacement, the fifth-root curvature is a strictly positive factor times the
literal `A,D,J` numerator `C₅`. -/
theorem thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature_sq
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature u (t ^ 2) =
      thetaCuspReflectedSourceSquaredDividedDrop u (t ^ 2) ^ (-(9 : ℝ) / 5) *
        thetaCuspReflectedSourceFifthRootCurvatureNumerator u t / (100 * t ^ 8) := by
  unfold thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature
    thetaCuspReflectedSourceSquaredDividedDrop
    thetaCuspReflectedSourceSquaredDividedDropSlope
    thetaCuspReflectedSourceSquaredDividedDropCurvature
    thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceDividedDrop
    thetaCuspReflectedSourceFirstDrop
  simp only [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  field_simp [ht.ne']
  ring

/-- Negative fifth-root curvature at a squared displacement is exactly negative `C₅`; no sign is
lost in the fifth-root or square-coordinate transformations. -/
theorem iteratedDeriv_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq_neg_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (deriv^[2] (thetaCuspReflectedSourceSquaredDividedDropFifthRoot u)) (t ^ 2) < 0 ↔
      thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 := by
  rw [iteratedDeriv_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot u (sq_pos_of_pos ht),
    thetaCuspReflectedSourceSquaredDividedDropFifthRootCurvature_sq u ht]
  have hGpos := thetaCuspReflectedSourceSquaredDividedDrop_pos u (sq_pos_of_pos ht)
  have hfactor : 0 <
      thetaCuspReflectedSourceSquaredDividedDrop u (t ^ 2) ^ (-(9 : ℝ) / 5) /
        (100 * t ^ 8) := by
    exact div_pos (Real.rpow_pos_of_pos hGpos _) (by positivity)
  rw [show
    thetaCuspReflectedSourceSquaredDividedDrop u (t ^ 2) ^ (-(9 : ℝ) / 5) *
          thetaCuspReflectedSourceFifthRootCurvatureNumerator u t / (100 * t ^ 8) =
        (thetaCuspReflectedSourceSquaredDividedDrop u (t ^ 2) ^ (-(9 : ℝ) / 5) /
          (100 * t ^ 8)) *
            thetaCuspReflectedSourceFifthRootCurvatureNumerator u t by ring]
  constructor
  · intro hneg
    by_contra hnot
    exact (not_lt_of_ge (mul_nonneg hfactor.le (le_of_not_gt hnot))) hneg
  · exact mul_neg_of_pos_of_neg hfactor

/-- **Source-jet localization of every possible rank-four failure.**  A negative source wall
forces the exact `A,D,J` fifth-root curvature numerator to be negative at a displacement strictly
between `t` and `3t`. -/
theorem thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureNumeratorFailure
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      ∃ r ∈ Ioo t (3 * t),
        thetaCuspReflectedSourceFifthRootCurvatureNumerator u r < 0 := by
  by_cases ht : 0 < t
  · right
    rcases thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureFailure u t with
      hnonpos | hwall | ⟨x, hx, hcurv⟩
    · exact False.elim (not_le_of_gt ht hnonpos)
    · exact Or.inl hwall
    right
    have hxpos : 0 < x := (sq_pos_of_pos ht).trans hx.1
    let r := Real.sqrt x
    have hr : 0 < r := Real.sqrt_pos.2 hxpos
    have hrsq : r ^ 2 = x := Real.sq_sqrt hxpos.le
    have htr : t < r := by
      by_contra hnot
      have hle : r ≤ t := le_of_not_gt hnot
      have hsquares : r ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hr.le ht.le).2 hle
      linarith [hx.1, hrsq, hsquares]
    have hr3t : r < 3 * t := by
      by_contra hnot
      have hle : 3 * t ≤ r := le_of_not_gt hnot
      have hsquares : (3 * t) ^ 2 ≤ r ^ 2 :=
        (sq_le_sq₀ (by positivity) hr.le).2 hle
      nlinarith [hx.2, hrsq, hsquares]
    refine ⟨r, ⟨htr, hr3t⟩, ?_⟩
    apply (iteratedDeriv_two_thetaCuspReflectedSourceSquaredDividedDropFifthRoot_sq_neg_iff
      u hr).mp
    rw [hrsq]
    exact hcurv
  · left
    exact le_of_not_gt ht

/-- **Projective localization of every possible rank-four failure.**  A negative source wall
forces strict increase of the exact projective ratio at a displacement strictly between `t` and
`3t`.  Thus the remaining rank-four burden is a literal source monotonicity problem. -/
theorem thetaCuspReflectedSourceOddParityWall_or_exists_projectiveRatioIncrease
    (u t : ℝ) :
    t ≤ 0 ∨
      0 ≤ thetaCuspReflectedSourceOddParityWall u t ∨
      ∃ r ∈ Ioo t (3 * t),
        0 < deriv (thetaCuspReflectedSourceFifthRootProjectiveRatio u) r := by
  by_cases ht : 0 < t
  · rcases
        thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureNumeratorFailure u t with
      hnonpos | hwall | ⟨r, hr, hcurv⟩
    · exact False.elim (not_le_of_gt ht hnonpos)
    · exact Or.inr (Or.inl hwall)
    · refine Or.inr (Or.inr ⟨r, hr, ?_⟩)
      have hrpos : 0 < r := ht.trans hr.1
      exact
        (deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_pos_iff u hrpos).2 hcurv
  · exact Or.inl (le_of_not_gt ht)

/-- The source `A,D,J` curvature numerator is the generic fifth-root divided-drop numerator
of the reflected source product. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_generic
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureNumerator u t =
      HilbertMetric.fifthRootDividedDropCurvatureNumerator
        (thetaCuspReflectedSourceProduct u) t := by
  let f := thetaCuspReflectedSourceProduct u
  have h₁ : iteratedDeriv 1 f t =
      -thetaCuspReflectedSourceDecayFlux u t := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspReflectedSourceProduct u t).deriv
  have h₁fun : iteratedDeriv 1 f =
      fun s => -thetaCuspReflectedSourceDecayFlux u s := by
    funext s
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspReflectedSourceProduct u s).deriv
  have h₂ : iteratedDeriv 2 f t =
      -thetaCuspReflectedSourceDecayFluxCurvature u t := by
    rw [show iteratedDeriv 2 f = deriv (iteratedDeriv 1 f) by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]]
    rw [h₁fun]
    exact (hasDerivAt_thetaCuspReflectedSourceDecayFlux u t).neg.deriv
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    HilbertMetric.fifthRootDividedDropCurvatureNumerator
    thetaCuspReflectedSourceFirstDrop
  rw [h₁, h₂]
  ring

/-- **Unconditional local C5 positivity.**  The completed theta source's strict second--sixth
Hankel curvature forces the exact fifth-root numerator to be positive at every sufficiently
small positive displacement. -/
theorem exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right (u : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator u t := by
  have hHankel : 0 <
      iteratedDeriv 2 (thetaCuspReflectedSourceProduct u) 0 *
          iteratedDeriv 6 (thetaCuspReflectedSourceProduct u) 0 -
        iteratedDeriv 4 (thetaCuspReflectedSourceProduct u) 0 ^ 2 := by
    rw [thetaCuspReflectedSourceProduct_secondSixthHankel_zero]
    exact thetaCuspFullSourceReflectionSecondSixthCurvature_pos u
  rcases HilbertMetric.exists_fifthRootDividedDropCurvatureNumerator_pos_right
      (contDiff_thetaCuspReflectedSourceProduct u)
      (thetaCuspReflectedSourceProduct_even u) hHankel with
    ⟨delta, hdelta, hpos⟩
  refine ⟨delta, hdelta, fun t ht htδ => ?_⟩
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_generic]
  exact hpos t ht htδ

/-- Strict fifth-root curvature is exactly strict projective decrease. -/
theorem deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_neg_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (thetaCuspReflectedSourceFifthRootProjectiveRatio u) t < 0 ↔
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator u t := by
  rw [(hasDerivAt_thetaCuspReflectedSourceFifthRootProjectiveRatio u ht).deriv]
  have hMpos := thetaCuspReflectedSourceProjectiveDenominator_pos u ht
  have hdenpos : 0 <
      t ^ 3 *
        (12 * thetaCuspReflectedSourceFirstDrop u t -
          t * thetaCuspReflectedSourceDecayFlux u t) ^ 2 := by
    positivity
  constructor
  · intro hneg
    rcases (div_neg_iff.mp hneg) with hgood | hbad
    · exact (not_lt_of_ge hdenpos.le hgood.2).elim
    · nlinarith [hbad.1]
  · intro hcurv
    exact div_neg_of_neg_of_pos (by nlinarith) hdenpos

/-- The projective C5 observable is strictly decreasing infinitesimally throughout a punctured
right neighborhood of every coalesced source fibre. -/
theorem exists_deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_neg_right (u : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      deriv (thetaCuspReflectedSourceFifthRootProjectiveRatio u) t < 0 := by
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right u with
    ⟨delta, hdelta, hcurv⟩
  refine ⟨delta, hdelta, fun t ht htδ => ?_⟩
  exact (deriv_thetaCuspReflectedSourceFifthRootProjectiveRatio_neg_iff u ht).2
    (hcurv t ht htδ)

end

end RHTower
