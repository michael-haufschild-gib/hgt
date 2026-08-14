import GaloisForLFunctions.RHTower.SuzukiOriginRemainderWeilBridge
import GaloisForLFunctions.RHTower.SuzukiOriginRemainderRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set intervalIntegral
open scoped Topology

namespace GaloisForLFunctions.RHTower

theorem neg_integral_abs_mul_secondDeriv {R : ℝ} (hR : 0 < R)
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    -(∫ x in (-R)..R, |x| * φ'' x) = -2 * φ 0 := by
  have hleftInt : IntervalIntegrable (fun x => (-x) * φ'' x) volume (-R) 0 := by
    exact (continuous_neg.mul hφ''cont).intervalIntegrable (-R) 0
  have hrightInt : IntervalIntegrable (fun x => x * φ'' x) volume 0 R := by
    exact (continuous_id.mul hφ''cont).intervalIntegrable 0 R
  have habsInt : IntervalIntegrable (fun x => |x| * φ'' x) volume (-R) 0 := by
    exact (continuous_abs.mul hφ''cont).intervalIntegrable (-R) 0
  have habsInt' : IntervalIntegrable (fun x => |x| * φ'' x) volume 0 R := by
    exact (continuous_abs.mul hφ''cont).intervalIntegrable 0 R
  have hleft := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => -x) (u' := fun _ => -1)
    (v := φ') (v' := φ'')
    (fun x _ => (hasDerivAt_id x).neg)
    (fun x _ => hφ' x)
    (continuous_const.intervalIntegrable (-R) 0)
    (hφ''cont.intervalIntegrable (-R) 0)
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x) (u' := fun _ => 1)
    (v := φ') (v' := φ'')
    (fun x _ => hasDerivAt_id x)
    (fun x _ => hφ' x)
    (continuous_const.intervalIntegrable 0 R)
    (hφ''cont.intervalIntegrable 0 R)
  have hφ'intLeft : IntervalIntegrable φ' volume (-R) 0 :=
    (continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt).intervalIntegrable (-R) 0
  have hφ'intRight : IntervalIntegrable φ' volume 0 R :=
    (continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt).intervalIntegrable 0 R
  have hfundLeft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) hφ'intLeft
  have hfundRight := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) hφ'intRight
  have hsplit := intervalIntegral.integral_add_adjacent_intervals habsInt habsInt'
  have habsLeft : (∫ x in (-R)..0, |x| * φ'' x) =
      ∫ x in (-R)..0, (-x) * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -R ≤ 0)] at hx
    dsimp only
    rw [abs_of_nonpos hx.2]
  have habsRight : (∫ x in 0..R, |x| * φ'' x) =
      ∫ x in 0..R, x * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hR.le] at hx
    dsimp only
    rw [abs_of_nonneg hx.1]
  rw [habsLeft, habsRight] at hsplit
  rw [hφ'nR] at hleft
  rw [hφ'R] at hright
  rw [hφnR] at hfundLeft
  rw [hφR] at hfundRight
  simp only [neg_mul, neg_neg, mul_zero, zero_mul, sub_zero, zero_sub,
    one_mul, intervalIntegral.integral_neg] at hleft hright hfundLeft hfundRight
  have hleft' : (∫ x in (-R)..0, (-x) * φ'' x) = φ 0 := by
    calc
      (∫ x in (-R)..0, (-x) * φ'' x) =
          ∫ x in (-R)..0, -(x * φ'' x) := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
      _ = -(∫ x in (-R)..0, x * φ'' x) :=
        intervalIntegral.integral_neg
      _ = φ 0 := by linarith [hleft, hfundLeft]
  have hright' : (∫ x in 0..R, x * φ'' x) = φ 0 := by
    linarith [hright, hfundRight]
  rw [← hsplit]
  rw [hleft', hright']
  ring

theorem neg_integral_hinge_mul_secondDeriv {R ell : ℝ}
    (hell : 0 < ell) (hellR : ell < R)
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    -(∫ x in (-R)..R, max 0 (|x| - ell) * φ'' x) =
      -(φ ell + φ (-ell)) := by
  have hR : 0 < R := hell.trans hellR
  have hkernel : Continuous fun x : ℝ => max 0 (|x| - ell) := by fun_prop
  have hfullInt : IntervalIntegrable
      (fun x => max 0 (|x| - ell) * φ'' x) volume (-R) R :=
    (hkernel.mul hφ''cont).intervalIntegrable (-R) R
  have hleftInt : IntervalIntegrable
      (fun x => max 0 (|x| - ell) * φ'' x) volume (-R) (-ell) :=
    (hkernel.mul hφ''cont).intervalIntegrable (-R) (-ell)
  have hmiddleInt : IntervalIntegrable
      (fun x => max 0 (|x| - ell) * φ'' x) volume (-ell) ell :=
    (hkernel.mul hφ''cont).intervalIntegrable (-ell) ell
  have hrightInt : IntervalIntegrable
      (fun x => max 0 (|x| - ell) * φ'' x) volume ell R :=
    (hkernel.mul hφ''cont).intervalIntegrable ell R
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals hleftInt hmiddleInt
  have hleftMiddleInt : IntervalIntegrable
      (fun x => max 0 (|x| - ell) * φ'' x) volume (-R) ell :=
    hleftInt.trans hmiddleInt
  have hsplitRight := intervalIntegral.integral_add_adjacent_intervals hleftMiddleInt hrightInt
  have hleftFormula : (∫ x in (-R)..(-ell), max 0 (|x| - ell) * φ'' x) =
      ∫ x in (-R)..(-ell), (-x - ell) * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -R ≤ -ell)] at hx
    dsimp only
    rw [abs_of_nonpos (by linarith [hx.2]), max_eq_right (by linarith [hx.2])]
  have hmiddleFormula : (∫ x in (-ell)..ell, max 0 (|x| - ell) * φ'' x) = 0 := by
    rw [show (∫ x in (-ell)..ell, max 0 (|x| - ell) * φ'' x) =
        ∫ _x in (-ell)..ell, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : -ell ≤ ell)] at hx
      dsimp only
      have habs : |x| ≤ ell := (abs_le).2 hx
      rw [max_eq_left (by linarith), zero_mul], intervalIntegral.integral_zero]
  have hrightFormula : (∫ x in ell..R, max 0 (|x| - ell) * φ'' x) =
      ∫ x in ell..R, (x - ell) * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hellR.le] at hx
    dsimp only
    rw [abs_of_nonneg (hell.le.trans hx.1), max_eq_right (by linarith [hx.1])]
  have hφ'intLeft : IntervalIntegrable φ' volume (-R) (-ell) :=
    (continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt).intervalIntegrable _ _
  have hφ'intRight : IntervalIntegrable φ' volume ell R :=
    (continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt).intervalIntegrable _ _
  have hleftIBP :
      (∫ x in (-R)..(-ell), (-x - ell) * φ'' x) =
        (-(-ell) - ell) * φ' (-ell) - (-(-R) - ell) * φ' (-R) -
          ∫ x in (-R)..(-ell), (-1) * φ' x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => -x - ell) (u' := fun _ => -1)
    (v := φ') (v' := φ'')
    (fun x _ => (hasDerivAt_id x).neg.sub_const ell)
    (fun x _ => hφ' x)
    (continuous_const.intervalIntegrable (-R) (-ell))
    (hφ''cont.intervalIntegrable (-R) (-ell))
  have hrightIBP :
      (∫ x in ell..R, (x - ell) * φ'' x) =
        (R - ell) * φ' R - (ell - ell) * φ' ell -
          ∫ x in ell..R, 1 * φ' x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x - ell) (u' := fun _ => 1)
    (v := φ') (v' := φ'')
    (fun x _ => (hasDerivAt_id x).sub_const ell)
    (fun x _ => hφ' x)
    (continuous_const.intervalIntegrable ell R)
    (hφ''cont.intervalIntegrable ell R)
  have hfundLeft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) hφ'intLeft
  have hfundRight := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) hφ'intRight
  rw [hφ'nR] at hleftIBP
  rw [hφ'R] at hrightIBP
  rw [hφnR] at hfundLeft
  rw [hφR] at hfundRight
  simp only [sub_self, zero_mul, mul_zero, sub_zero, neg_mul, one_mul,
    intervalIntegral.integral_neg, neg_neg] at hleftIBP hrightIBP hfundLeft hfundRight
  rw [hleftFormula, hmiddleFormula, add_zero] at hsplitLeft
  rw [← hsplitLeft, hrightFormula] at hsplitRight
  rw [← hsplitRight]
  linarith

/-- Endpoint-closed hinge identity. Suzuki's visible-prime cutoff is `n ≤ exp(2a)`, so the
possible atom at `log n = 2a` must not be discarded. At the endpoint its hinge vanishes on the
whole difference interval and both boundary samples vanish. -/
theorem neg_integral_hinge_mul_secondDeriv_of_le {R ell : ℝ}
    (hell : 0 < ell) (hellR : ell ≤ R)
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    -(∫ x in (-R)..R, max 0 (|x| - ell) * φ'' x) =
      -(φ ell + φ (-ell)) := by
  rcases hellR.eq_or_lt with rfl | hellR
  · have hkernel : ∀ x ∈ uIcc (-ell) ell, max 0 (|x| - ell) = 0 := by
      intro x hx
      rw [uIcc_of_le (by linarith [hell] : -ell ≤ ell)] at hx
      rw [max_eq_left]
      exact sub_nonpos.mpr ((abs_le).2 hx)
    have hintegral : (∫ x in (-ell)..ell, max 0 (|x| - ell) * φ'' x) = 0 := by
      rw [show (∫ x in (-ell)..ell, max 0 (|x| - ell) * φ'' x) =
          ∫ _x in (-ell)..ell, (0 : ℝ) by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hkernel x hx, zero_mul], intervalIntegral.integral_zero]
    rw [hintegral, neg_zero, hφR, hφnR]
    ring
  · exact neg_integral_hinge_mul_secondDeriv hell hellR φ φ' φ'' hφ hφ'
      hφ''cont hφR hφnR hφ'R hφ'nR

theorem neg_integral_mul_secondDeriv_eq_neg_integral_secondDeriv_mul
    {R : ℝ}
    (f f' f'' φ φ' φ'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hf''cont : Continuous f'') (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    -(∫ x in (-R)..R, f x * φ'' x) =
      -(∫ x in (-R)..R, f'' x * φ x) := by
  have hf'cont : Continuous f' :=
    continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
  have hφ'cont : Continuous φ' :=
    continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hφcont : Continuous φ :=
    continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hfirst :
      (∫ x in (-R)..R, f x * φ'' x) =
        f R * φ' R - f (-R) * φ' (-R) -
          ∫ x in (-R)..R, f' x * φ' x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := f') (v := φ') (v' := φ'')
    (fun x _ => hf x) (fun x _ => hφ' x)
    (hf'cont.intervalIntegrable (-R) R) (hφ''cont.intervalIntegrable (-R) R)
  have hsecond :
      (∫ x in (-R)..R, f' x * φ' x) =
        f' R * φ R - f' (-R) * φ (-R) -
          ∫ x in (-R)..R, f'' x * φ x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f') (u' := f'') (v := φ) (v' := φ')
    (fun x _ => hf' x) (fun x _ => hφ x)
    (hf''cont.intervalIntegrable (-R) R) (hφ'cont.intervalIntegrable (-R) R)
  rw [hφ'nR, hφ'R] at hfirst
  rw [hφnR, hφR] at hsecond
  simp only [mul_zero, sub_zero, zero_sub] at hfirst hsecond
  linarith

theorem neg_integral_suzukiOriginRemainder_mul_secondDeriv
    {R : ℝ}
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    -(∫ x in (-R)..R, GaloisForLFunctions.RHTower.suzukiOriginRemainder x * φ'' x) =
      -(∫ x in (-R)..R, GaloisForLFunctions.RHTower.suzukiOriginRemainderCurvature x * φ x) := by
  open GaloisForLFunctions.RHTower in
  exact neg_integral_mul_secondDeriv_eq_neg_integral_secondDeriv_mul
    suzukiOriginRemainder suzukiOriginRemainderDerivative
    suzukiOriginRemainderCurvature φ φ' φ''
    hasDerivAt_suzukiOriginRemainder
    hasDerivAt_suzukiOriginRemainderDerivative hφ hφ'
    continuous_suzukiOriginRemainderCurvature hφ''cont
    hφR hφnR hφ'R hφ'nR

noncomputable def centeredCauchyFinitePart (R : ℝ) (φ : ℝ → ℝ) : ℝ :=
  -(∫ x in (-R)..0, dslope φ 0 x) +
    (∫ x in 0..R, dslope φ 0 x) + 2 * φ 0 * Real.log R

theorem integral_abs_mul_log_mul_secondDeriv {R : ℝ} (hR : 0 < R)
    (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''cont : Continuous φ'')
    (hφR : φ R = 0) (hφnR : φ (-R) = 0)
    (hφ'R : φ' R = 0) (hφ'nR : φ' (-R) = 0) :
    (∫ x in (-R)..R, |x| * Real.log |x| * φ'' x) =
      centeredCauchyFinitePart R φ + 2 * φ 0 := by
  have hφcont : Continuous φ :=
    continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hφ'cont : Continuous φ' :=
    continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt
  have hdslope : Continuous (dslope φ 0) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (s := Set.univ) Filter.univ_mem).2
      ⟨hφcont.continuousOn, (hφ 0).differentiableAt⟩
  let m : ℝ → ℝ := fun x => x * Real.log x
  let bRight : ℝ → ℝ := fun x =>
    m x * φ' x - (m x + x) * dslope φ 0 x
  let bLeft : ℝ → ℝ := fun x =>
    m (-x) * φ' x - (m (-x) + (-x)) * dslope φ 0 x
  have hm : Continuous m := Real.continuous_mul_log
  have hbRightCont : Continuous bRight :=
    (hm.mul hφ'cont).sub ((hm.add continuous_id).mul hdslope)
  have hbLeftCont : Continuous bLeft :=
    ((hm.comp continuous_neg).mul hφ'cont).sub
      (((hm.comp continuous_neg).add continuous_neg).mul hdslope)
  have hbRightDeriv : ∀ x ∈ Ioo 0 R,
      HasDerivAt bRight (m x * φ'' x - dslope φ 0 x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hmDeriv : HasDerivAt m (Real.log x + 1) x := by
      exact Real.hasDerivAt_mul_log hx0
    have hquot : dslope φ 0 x = (φ x - φ 0) * x⁻¹ := by
      rw [dslope_of_ne φ hx0]
      simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
      ring
    let old : ℝ → ℝ := fun y =>
      m y * φ' y - (Real.log y + 1) * (φ y - φ 0)
    have holdRaw := (hmDeriv.mul (hφ' x)).sub
      (((Real.hasDerivAt_log hx0).add_const 1).mul ((hφ x).sub_const (φ 0)))
    have hfun :
        m * φ' - (fun y => Real.log y + 1) * (fun y => φ y - φ 0) = old := by
      funext y
      rfl
    rw [hfun] at holdRaw
    have hold : HasDerivAt old (m x * φ'' x - (φ x - φ 0) * x⁻¹) x := by
      have hcoeff :
          (Real.log x + 1) * φ' x + m x * φ'' x -
              (x⁻¹ * (φ x - φ 0) + (Real.log x + 1) * φ' x) =
            m x * φ'' x - (φ x - φ 0) * x⁻¹ := by
        ring
      rw [hcoeff] at holdRaw
      exact holdRaw
    have heq : bRight =ᶠ[𝓝 x] old := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      dsimp only [bRight, old]
      rw [dslope_of_ne φ hy]
      simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
      field_simp
      ring
    rw [hquot]
    exact hold.congr_of_eventuallyEq heq
  have hbLeftDeriv : ∀ x ∈ Ioo (-R) 0,
      HasDerivAt bLeft (m (-x) * φ'' x + dslope φ 0 x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.2.ne
    have hnx0 : -x ≠ 0 := neg_ne_zero.mpr hx0
    have hmNegDeriv : HasDerivAt (fun y => m (-y)) (-(Real.log (-x) + 1)) x := by
      have hraw := (Real.hasDerivAt_mul_log hnx0).comp x (hasDerivAt_id x).neg
      have hfun : (fun z : ℝ => z * Real.log z) ∘ (fun y : ℝ => -y) =
          fun y => m (-y) := by
        funext y
        rfl
      rw [hfun] at hraw
      have hcoeff : (Real.log (-x) + 1) * (-1) = -(Real.log (-x) + 1) := by ring
      rw [hcoeff] at hraw
      exact hraw
    have hquot : dslope φ 0 x = (φ x - φ 0) * x⁻¹ := by
      rw [dslope_of_ne φ hx0]
      simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
      ring
    let old : ℝ → ℝ := fun y =>
      m (-y) * φ' y + (Real.log (-y) + 1) * (φ y - φ 0)
    have hlogNeg : HasDerivAt (fun y => Real.log (-y)) x⁻¹ x := by
      have hraw := (Real.hasDerivAt_log hnx0).comp x (hasDerivAt_id x).neg
      have hfun : Real.log ∘ (fun y : ℝ => -y) = fun y => Real.log (-y) := by
        rfl
      rw [hfun] at hraw
      have hcoeff : (-x)⁻¹ * (-1) = x⁻¹ := by rw [inv_neg]; ring
      rw [hcoeff] at hraw
      exact hraw
    have holdRaw := (hmNegDeriv.mul (hφ' x)).add
      ((hlogNeg.add_const 1).mul ((hφ x).sub_const (φ 0)))
    have hfun :
        (fun y => m (-y)) * φ' + (fun y => Real.log (-y) + 1) *
          (fun y => φ y - φ 0) = old := by
      funext y
      rfl
    rw [hfun] at holdRaw
    have hold : HasDerivAt old (m (-x) * φ'' x + (φ x - φ 0) * x⁻¹) x := by
      have hcoeff :
          -(Real.log (-x) + 1) * φ' x + m (-x) * φ'' x +
              (x⁻¹ * (φ x - φ 0) + (Real.log (-x) + 1) * φ' x) =
            m (-x) * φ'' x + (φ x - φ 0) * x⁻¹ := by
        ring
      rw [hcoeff] at holdRaw
      exact holdRaw
    have heq : bLeft =ᶠ[𝓝 x] old := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      dsimp only [bLeft, old]
      rw [dslope_of_ne φ hy]
      simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
      field_simp
      ring
    rw [hquot]
    exact hold.congr_of_eventuallyEq heq
  have hrightInt : IntervalIntegrable
      (fun x => m x * φ'' x - dslope φ 0 x) volume 0 R :=
    ((hm.mul hφ''cont).sub hdslope).intervalIntegrable 0 R
  have hleftInt : IntervalIntegrable
      (fun x => m (-x) * φ'' x + dslope φ 0 x) volume (-R) 0 :=
    (((hm.comp continuous_neg).mul hφ''cont).add hdslope).intervalIntegrable (-R) 0
  have hrightFTC :
      (∫ x in 0..R, (m x * φ'' x - dslope φ 0 x)) = bRight R - bRight 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
      hbRightCont.continuousOn hbRightDeriv hrightInt
  have hleftFTC :
      (∫ x in (-R)..0, (m (-x) * φ'' x + dslope φ 0 x)) = bLeft 0 - bLeft (-R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith)
      hbLeftCont.continuousOn hbLeftDeriv hleftInt
  have hdsR : dslope φ 0 R = -(φ 0) / R := by
    rw [dslope_of_ne φ hR.ne']
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub, hφR]
    field_simp
    ring
  have hdsnR : dslope φ 0 (-R) = φ 0 / R := by
    rw [dslope_of_ne φ (neg_ne_zero.mpr hR.ne')]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub, hφnR]
    field_simp
    ring
  have hmR : m R = R * Real.log R := rfl
  have hmnR : m (-(-R)) = R * Real.log R := by simp [m]
  have hbR : bRight R = (Real.log R + 1) * φ 0 := by
    dsimp only [bRight]
    rw [hφ'R, mul_zero, hdsR, hmR]
    field_simp
    ring
  have hb0 : bRight 0 = 0 := by simp [bRight, m]
  have hbnR : bLeft (-R) = -(Real.log R + 1) * φ 0 := by
    dsimp only [bLeft]
    rw [hφ'nR, mul_zero, hdsnR, hmnR]
    field_simp
    ring
  have hbl0 : bLeft 0 = 0 := by simp [bLeft, m]
  rw [hbR, hb0, sub_zero] at hrightFTC
  rw [hbl0, hbnR] at hleftFTC
  have hleftFTC' :
      (∫ x in (-R)..0, (m (-x) * φ'' x + dslope φ 0 x)) =
        (Real.log R + 1) * φ 0 := by
    linarith [hleftFTC]
  have hkernelInt : IntervalIntegrable
      (fun x => |x| * Real.log |x| * φ'' x) volume (-R) R :=
    ((Real.continuous_mul_log.comp continuous_abs).mul hφ''cont).intervalIntegrable (-R) R
  have hkernelLeft : (∫ x in (-R)..0, |x| * Real.log |x| * φ'' x) =
      ∫ x in (-R)..0, m (-x) * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -R ≤ 0)] at hx
    change |x| * Real.log |x| * φ'' x = m (-x) * φ'' x
    rw [abs_of_nonpos hx.2]
  have hkernelRight : (∫ x in 0..R, |x| * Real.log |x| * φ'' x) =
      ∫ x in 0..R, m x * φ'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hR.le] at hx
    change |x| * Real.log |x| * φ'' x = m x * φ'' x
    rw [abs_of_nonneg hx.1]
  have hkernelLeftInt : IntervalIntegrable
      (fun x => |x| * Real.log |x| * φ'' x) volume (-R) 0 :=
    ((Real.continuous_mul_log.comp continuous_abs).mul hφ''cont).intervalIntegrable
      (-R) 0
  have hkernelRightInt : IntervalIntegrable
      (fun x => |x| * Real.log |x| * φ'' x) volume 0 R :=
    ((Real.continuous_mul_log.comp continuous_abs).mul hφ''cont).intervalIntegrable
      0 R
  have hkernelSplit := intervalIntegral.integral_add_adjacent_intervals
    hkernelLeftInt hkernelRightInt
  rw [hkernelLeft, hkernelRight] at hkernelSplit
  have hrightSplit :
      (∫ x in 0..R, (m x * φ'' x - dslope φ 0 x)) =
        (∫ x in 0..R, m x * φ'' x) - ∫ x in 0..R, dslope φ 0 x := by
    exact intervalIntegral.integral_sub
      ((hm.mul hφ''cont).intervalIntegrable 0 R) (hdslope.intervalIntegrable 0 R)
  have hleftSplit :
      (∫ x in (-R)..0, (m (-x) * φ'' x + dslope φ 0 x)) =
        (∫ x in (-R)..0, m (-x) * φ'' x) + ∫ x in (-R)..0, dslope φ 0 x := by
    exact intervalIntegral.integral_add
      (((hm.comp continuous_neg).mul hφ''cont).intervalIntegrable (-R) 0)
      (hdslope.intervalIntegrable (-R) 0)
  rw [hrightSplit] at hrightFTC
  rw [hleftSplit] at hleftFTC'
  rw [← hkernelSplit]
  unfold centeredCauchyFinitePart
  linarith [hleftFTC']

end GaloisForLFunctions.RHTower
