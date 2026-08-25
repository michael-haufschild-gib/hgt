import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKreinTransform
import GaloisForLFunctions.RHTower.XiBezoutianPointedIncidence
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Double Laplace transform of the theta tail first-moment kernel

This module supplies the absolute-integrability and three-variable Fubini step connecting the
literal positive theta tail-density to the integrated two-channel Krein difference.  The resulting
double Laplace transform is identified with the actual theta-transform Bezoutian throughout its
right Fubini domain.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ComplexOrder

noncomputable section

namespace RHTower

/-- One source leg of a shifted Krein channel; `d=c` and `d=-c` give its two signs. -/
def thetaTailChannelIntegrand (d : ℝ) (w : ℂ) (s x : ℝ) : ℂ :=
  ((x + s + d : ℝ) : ℂ) * (thetaCuspFullSource (x + s) : ℂ) *
    Complex.exp (w * (x : ℂ))

lemma integrable_thetaTailChannelIntegrand_zero (d : ℝ) (w : ℂ) :
    Integrable (thetaTailChannelIntegrand d w 0) := by
  have hm := integrable_thetaBilateralLaplaceMoment w
  have hb := integrable_thetaBilateralLaplace w
  apply (hm.add (hb.const_mul (d : ℂ))).congr
  filter_upwards with x
  unfold thetaTailChannelIntegrand
  simp only [Pi.add_apply, add_zero]
  push_cast
  ring

lemma thetaTailChannelIntegrand_eq_shift (d : ℝ) (w : ℂ) (s x : ℝ) :
    thetaTailChannelIntegrand d w s x =
      Complex.exp (-(w * (s : ℂ))) * thetaTailChannelIntegrand d w 0 (x + s) := by
  unfold thetaTailChannelIntegrand
  rw [show w * (x : ℂ) = -(w * (s : ℂ)) + w * ((x + s : ℝ) : ℂ) by
    push_cast
    ring, Complex.exp_add]
  push_cast
  ring

lemma integrable_thetaTailChannelIntegrand (d : ℝ) (w : ℂ) (s : ℝ) :
    Integrable (thetaTailChannelIntegrand d w s) := by
  have h := (integrable_thetaTailChannelIntegrand_zero d w).comp_add_right s
  have h' := h.const_mul (Complex.exp (-(w * (s : ℂ))))
  apply h'.congr
  filter_upwards with x
  exact (thetaTailChannelIntegrand_eq_shift d w s x).symm

lemma integral_norm_thetaTailChannelIntegrand_eq (d : ℝ) (w : ℂ) (s : ℝ) :
    (∫ x : ℝ, ‖thetaTailChannelIntegrand d w s x‖) =
      Real.exp (-(w.re * s)) *
        ∫ y : ℝ, ‖thetaTailChannelIntegrand d w 0 y‖ := by
  rw [show (fun x : ℝ => ‖thetaTailChannelIntegrand d w s x‖) =
      fun x => Real.exp (-(w.re * s)) *
        ‖thetaTailChannelIntegrand d w 0 (x + s)‖ by
    funext x
    rw [thetaTailChannelIntegrand_eq_shift, norm_mul, Complex.norm_exp]
    congr 2
    simp]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add_right_eq_self
      (fun y : ℝ => ‖thetaTailChannelIntegrand d w 0 y‖) s]

lemma integrableOn_exp_neg_real_mul_Ioi {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s))) (Ioi (0 : ℝ)) := by
  simpa only [neg_mul] using
    (integrableOn_exp_mul_Ioi (a := -q) (neg_lt_zero.mpr hq) 0)

/-- Absolute integrability of one sign of the sheared three-variable Krein kernel. -/
lemma integrable_thetaTailChannelTriple (d : ℝ) {w v : ℂ}
    (hwv : 0 < w.re + v.re) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      thetaTailChannelIntegrand d w p.1 p.2.1 *
        (starRingEnd ℂ) (thetaTailChannelIntegrand d v p.1 p.2.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
  let F : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    thetaTailChannelIntegrand d w p.1 p.2.1 *
      (starRingEnd ℂ) (thetaTailChannelIntegrand d v p.1 p.2.2)
  have hk : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hleft : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      thetaTailChannelIntegrand d w p.1 p.2.1) := by
    unfold thetaTailChannelIntegrand
    have hcoef : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        ((p.2.1 + p.1 + d : ℝ) : ℂ)) := by fun_prop
    have hsource : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        (thetaCuspFullSource (p.2.1 + p.1) : ℂ)) :=
      Complex.continuous_ofReal.comp (hk.comp (by fun_prop))
    have hphase : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        Complex.exp (w * (p.2.1 : ℂ))) := by fun_prop
    exact (hcoef.mul hsource).mul hphase
  have hright : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      thetaTailChannelIntegrand d v p.1 p.2.2) := by
    unfold thetaTailChannelIntegrand
    have hcoef : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        ((p.2.2 + p.1 + d : ℝ) : ℂ)) := by fun_prop
    have hsource : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        (thetaCuspFullSource (p.2.2 + p.1) : ℂ)) :=
      Complex.continuous_ofReal.comp (hk.comp (by fun_prop))
    have hphase : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        Complex.exp (v * (p.2.2 : ℂ))) := by fun_prop
    exact (hcoef.mul hsource).mul hphase
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
    exact (hleft.mul (Complex.continuous_conj.comp hright)).aestronglyMeasurable
  rw [show (fun p : ℝ × (ℝ × ℝ) =>
      thetaTailChannelIntegrand d w p.1 p.2.1 *
        (starRingEnd ℂ) (thetaTailChannelIntegrand d v p.1 p.2.2)) = F from rfl]
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with s
    have hv := integrable_thetaTailChannelIntegrand d v s
    have hvconj : Integrable (fun t : ℝ =>
        (starRingEnd ℂ) (thetaTailChannelIntegrand d v s t)) := by
      apply Integrable.mono hv.norm
      · apply Continuous.aestronglyMeasurable
        apply Complex.continuous_conj.comp
        unfold thetaTailChannelIntegrand
        have hcoef : Continuous (fun t : ℝ => ((t + s + d : ℝ) : ℂ)) := by fun_prop
        have hsource : Continuous (fun t : ℝ =>
            (thetaCuspFullSource (t + s) : ℂ)) :=
          Complex.continuous_ofReal.comp
            (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop))
        have hphase : Continuous (fun t : ℝ => Complex.exp (v * (t : ℂ))) := by fun_prop
        exact (hcoef.mul hsource).mul hphase
      · filter_upwards with t
        simp
    exact (integrable_thetaTailChannelIntegrand d w s).mul_prod hvconj
  · let Cw : ℝ := ∫ x : ℝ, ‖thetaTailChannelIntegrand d w 0 x‖
    let Cv : ℝ := ∫ x : ℝ, ‖thetaTailChannelIntegrand d v 0 x‖
    have hexp := (integrableOn_exp_neg_real_mul_Ioi hwv).const_mul (Cw * Cv)
    apply hexp.congr
    filter_upwards with s
    dsimp [F]
    rw [show (fun z : ℝ × ℝ =>
        ‖thetaTailChannelIntegrand d w s z.1 *
          (starRingEnd ℂ) (thetaTailChannelIntegrand d v s z.2)‖) =
        fun z => ‖thetaTailChannelIntegrand d w s z.1‖ *
          ‖thetaTailChannelIntegrand d v s z.2‖ by
      funext z
      rw [norm_mul, norm_conj]]
    rw [MeasureTheory.integral_prod_mul
      (μ := volume) (ν := volume)
      (fun x : ℝ => ‖thetaTailChannelIntegrand d w s x‖)
      (fun y : ℝ => ‖thetaTailChannelIntegrand d v s y‖)]
    have hws := integral_norm_thetaTailChannelIntegrand_eq d w s
    have hvs := integral_norm_thetaTailChannelIntegrand_eq d v s
    rw [hws, hvs]
    dsimp [Cw, Cv]
    have he : Real.exp (-((w.re + v.re) * s)) =
        Real.exp (-(w.re * s)) * Real.exp (-(v.re * s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring

/-- Difference of the two sheared Krein channels before integration. -/
def thetaTailKreinTripleIntegrand (c : ℝ) (w v : ℂ)
    (s : ℝ) (z : ℝ × ℝ) : ℂ :=
  thetaTailChannelIntegrand c w s z.1 *
      (starRingEnd ℂ) (thetaTailChannelIntegrand c v s z.2) -
    thetaTailChannelIntegrand (-c) w s z.1 *
      (starRingEnd ℂ) (thetaTailChannelIntegrand (-c) v s z.2)

lemma integrable_thetaTailKreinTripleIntegrand
    (c : ℝ) {w v : ℂ} (hwv : 0 < w.re + v.re) :
    Integrable (Function.uncurry (thetaTailKreinTripleIntegrand c w v))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
  exact (integrable_thetaTailChannelTriple c hwv).sub
    (integrable_thetaTailChannelTriple (-c) hwv)

lemma integral_prod_thetaTailKreinTripleIntegrand (c : ℝ) (w v : ℂ) (s : ℝ) :
    (∫ z : ℝ × ℝ, thetaTailKreinTripleIntegrand c w v s z
        ∂(volume.prod volume)) =
      thetaTailKreinPlusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinPlusTransform c v s) -
        thetaTailKreinMinusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinMinusTransform c v s) := by
  have hp : Integrable (fun z : ℝ × ℝ =>
      thetaTailChannelIntegrand c w s z.1 *
        (starRingEnd ℂ) (thetaTailChannelIntegrand c v s z.2))
      (volume.prod volume) := by
    have hv := integrable_thetaTailChannelIntegrand c v s
    have hvconj : Integrable (fun t : ℝ =>
        (starRingEnd ℂ) (thetaTailChannelIntegrand c v s t)) := by
      apply Integrable.mono hv.norm
      · apply Continuous.aestronglyMeasurable
        apply Complex.continuous_conj.comp
        unfold thetaTailChannelIntegrand
        have hcoef : Continuous (fun t : ℝ => ((t + s + c : ℝ) : ℂ)) := by fun_prop
        have hsource : Continuous (fun t : ℝ =>
            (thetaCuspFullSource (t + s) : ℂ)) :=
          Complex.continuous_ofReal.comp
            (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop))
        have hphase : Continuous (fun t : ℝ => Complex.exp (v * (t : ℂ))) := by fun_prop
        exact (hcoef.mul hsource).mul hphase
      · filter_upwards with t
        simp
    exact (integrable_thetaTailChannelIntegrand c w s).mul_prod hvconj
  have hm : Integrable (fun z : ℝ × ℝ =>
      thetaTailChannelIntegrand (-c) w s z.1 *
        (starRingEnd ℂ) (thetaTailChannelIntegrand (-c) v s z.2))
      (volume.prod volume) := by
    have hv := integrable_thetaTailChannelIntegrand (-c) v s
    have hvconj : Integrable (fun t : ℝ =>
        (starRingEnd ℂ) (thetaTailChannelIntegrand (-c) v s t)) := by
      apply Integrable.mono hv.norm
      · apply Continuous.aestronglyMeasurable
        apply Complex.continuous_conj.comp
        unfold thetaTailChannelIntegrand
        have hcoef : Continuous (fun t : ℝ => ((t + s - c : ℝ) : ℂ)) := by fun_prop
        have hsource : Continuous (fun t : ℝ =>
            (thetaCuspFullSource (t + s) : ℂ)) :=
          Complex.continuous_ofReal.comp
            (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop))
        have hphase : Continuous (fun t : ℝ => Complex.exp (v * (t : ℂ))) := by fun_prop
        exact (hcoef.mul hsource).mul hphase
      · filter_upwards with t
        simp
    exact (integrable_thetaTailChannelIntegrand (-c) w s).mul_prod hvconj
  unfold thetaTailKreinTripleIntegrand
  rw [integral_sub hp hm,
    MeasureTheory.integral_prod_mul (μ := volume) (ν := volume)
      (thetaTailChannelIntegrand c w s)
      (fun t : ℝ => (starRingEnd ℂ) (thetaTailChannelIntegrand c v s t)),
    MeasureTheory.integral_prod_mul (μ := volume) (ν := volume)
      (thetaTailChannelIntegrand (-c) w s)
      (fun t : ℝ => (starRingEnd ℂ) (thetaTailChannelIntegrand (-c) v s t)),
    integral_conj, integral_conj]
  rfl

/-- Three-variable Fubini interchange for the literal theta Krein kernel. -/
theorem integral_thetaTailKreinTriple_swap (c : ℝ) {w v : ℂ}
    (hwv : 0 < w.re + v.re) :
    (∫ s in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
        thetaTailKreinTripleIntegrand c w v s z ∂(volume.prod volume)) =
      ∫ z : ℝ × ℝ, (∫ s in Ioi (0 : ℝ),
        thetaTailKreinTripleIntegrand c w v s z) ∂(volume.prod volume) := by
  exact MeasureTheory.integral_integral_swap
    (integrable_thetaTailKreinTripleIntegrand c hwv)

/-- Literal double-Laplace integrand of the theta tail first-moment kernel. -/
def thetaTailDoubleLaplaceIntegrand (w v : ℂ) (z : ℝ × ℝ) : ℂ :=
  (thetaTailFirstMomentKernel z.1 z.2 : ℂ) *
    Complex.exp (w * (z.1 : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (v * (z.2 : ℂ)))

lemma thetaTailDoubleLaplaceIntegrand_neg_neg (w v : ℂ) (z : ℝ × ℝ) :
    thetaTailDoubleLaplaceIntegrand (-w) (-v) (-z.1, -z.2) =
      thetaTailDoubleLaplaceIntegrand w v z := by
  unfold thetaTailDoubleLaplaceIntegrand
  rw [thetaTailFirstMomentKernel_neg_neg]
  simp only [ofReal_neg, neg_mul]
  rw [show -(w * -((z.1 : ℝ) : ℂ)) = w * (z.1 : ℂ) by ring,
    show -(v * -((z.2 : ℝ) : ℂ)) = v * (z.2 : ℂ) by ring]

lemma norm_thetaTailDoubleLaplaceIntegrand (w v : ℂ) (z : ℝ × ℝ) :
    ‖thetaTailDoubleLaplaceIntegrand w v z‖ =
      thetaTailFirstMomentKernel z.1 z.2 *
        Real.exp (w.re * z.1 + v.re * z.2) := by
  unfold thetaTailDoubleLaplaceIntegrand
  rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thetaTailFirstMomentKernel_nonneg _ _),
    Complex.norm_exp, norm_conj, Complex.norm_exp]
  rw [show (w * (z.1 : ℂ)).re = w.re * z.1 by simp [Complex.mul_re],
    show (v * (z.2 : ℂ)).re = v.re * z.2 by simp [Complex.mul_re],
    mul_assoc, ← Real.exp_add]

lemma norm_thetaTailDoubleLaplaceIntegrand_real_tilt_le_unit_tilts
    (w v : ℂ) {r : ℝ} (hr : |r| ≤ 1) (z : ℝ × ℝ) :
    ‖thetaTailDoubleLaplaceIntegrand (w + r) (v + r) z‖ ≤
      ‖thetaTailDoubleLaplaceIntegrand (w + 1) (v + 1) z‖ +
        ‖thetaTailDoubleLaplaceIntegrand (w - 1) (v - 1) z‖ := by
  rw [norm_thetaTailDoubleLaplaceIntegrand,
    norm_thetaTailDoubleLaplaceIntegrand,
    norm_thetaTailDoubleLaplaceIntegrand]
  let H : ℝ := thetaTailFirstMomentKernel z.1 z.2
  let A : ℝ := w.re * z.1 + v.re * z.2
  let R : ℝ := z.1 + z.2
  change H * Real.exp ((w + r).re * z.1 + (v + r).re * z.2) ≤
    H * Real.exp ((w + 1).re * z.1 + (v + 1).re * z.2) +
      H * Real.exp ((w - 1).re * z.1 + (v - 1).re * z.2)
  have hH : 0 ≤ H := thetaTailFirstMomentKernel_nonneg _ _
  have hrbounds := abs_le.mp hr
  have hnegler : -1 ≤ r := hrbounds.1
  have hrle : r ≤ 1 := hrbounds.2
  have htilt :
      (w + r).re * z.1 + (v + r).re * z.2 = A + r * R := by
    simp [A, R]
    ring
  have hplus :
      (w + 1).re * z.1 + (v + 1).re * z.2 = A + R := by
    simp [A, R]
    ring
  have hminus :
      (w - 1).re * z.1 + (v - 1).re * z.2 = A - R := by
    simp [A, R]
    ring
  rw [htilt, hplus, hminus]
  by_cases hR : 0 ≤ R
  · have harg : A + r * R ≤ A + R := by nlinarith
    have hmain : H * Real.exp (A + r * R) ≤ H * Real.exp (A + R) := by
      gcongr
    have hother : 0 ≤ H * Real.exp (A - R) :=
      mul_nonneg hH (Real.exp_pos _).le
    linarith
  · have hR' : R ≤ 0 := le_of_not_ge hR
    have harg : A + r * R ≤ A - R := by nlinarith
    have hmain : H * Real.exp (A + r * R) ≤ H * Real.exp (A - R) := by
      gcongr
    have hother : 0 ≤ H * Real.exp (A + R) :=
      mul_nonneg hH (Real.exp_pos _).le
    linarith

lemma norm_thetaTailDoubleLaplaceIntegrand_first_real_tilt_le_unit_tilts
    (w v : ℂ) {r : ℝ} (hr : |r| ≤ 1) (z : ℝ × ℝ) :
    ‖thetaTailDoubleLaplaceIntegrand (w + r) v z‖ ≤
      ‖thetaTailDoubleLaplaceIntegrand (w + 1) v z‖ +
        ‖thetaTailDoubleLaplaceIntegrand (w - 1) v z‖ := by
  rw [norm_thetaTailDoubleLaplaceIntegrand,
    norm_thetaTailDoubleLaplaceIntegrand,
    norm_thetaTailDoubleLaplaceIntegrand]
  let H : ℝ := thetaTailFirstMomentKernel z.1 z.2
  let A : ℝ := w.re * z.1 + v.re * z.2
  change H * Real.exp ((w + r).re * z.1 + v.re * z.2) ≤
    H * Real.exp ((w + 1).re * z.1 + v.re * z.2) +
      H * Real.exp ((w - 1).re * z.1 + v.re * z.2)
  have hH : 0 ≤ H := thetaTailFirstMomentKernel_nonneg _ _
  have hrbounds := abs_le.mp hr
  have hnegler : -1 ≤ r := hrbounds.1
  have hrle : r ≤ 1 := hrbounds.2
  have htilt :
      (w + r).re * z.1 + v.re * z.2 = A + r * z.1 := by
    simp [A]
    ring
  have hplus :
      (w + 1).re * z.1 + v.re * z.2 = A + z.1 := by
    simp [A]
    ring
  have hminus :
      (w - 1).re * z.1 + v.re * z.2 = A - z.1 := by
    simp [A]
    ring
  rw [htilt, hplus, hminus]
  by_cases hx : 0 ≤ z.1
  · have harg : A + r * z.1 ≤ A + z.1 := by nlinarith
    have hmain : H * Real.exp (A + r * z.1) ≤ H * Real.exp (A + z.1) := by
      gcongr
    have hother : 0 ≤ H * Real.exp (A - z.1) :=
      mul_nonneg hH (Real.exp_pos _).le
    linarith
  · have hx' : z.1 ≤ 0 := le_of_not_ge hx
    have harg : A + r * z.1 ≤ A - z.1 := by nlinarith
    have hmain : H * Real.exp (A + r * z.1) ≤ H * Real.exp (A - z.1) := by
      gcongr
    have hother : 0 ≤ H * Real.exp (A + z.1) :=
      mul_nonneg hH (Real.exp_pos _).le
    linarith

lemma integral_thetaTailKreinTripleIntegrand_eq_kernel
    {c : ℝ} (hc : 0 < c) (w v : ℂ) (x t : ℝ) :
    (1 / (2 * c : ℂ)) * ∫ s in Ioi (0 : ℝ),
      thetaTailKreinTripleIntegrand c w v s (x, t) =
        thetaTailDoubleLaplaceIntegrand w v (x, t) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  let P : ℂ := Complex.exp (w * (x : ℂ)) *
    (starRingEnd ℂ) (Complex.exp (v * (t : ℂ)))
  let R : ℝ → ℝ := fun s =>
    thetaTailKreinPlus c x s * thetaTailKreinPlus c t s -
      thetaTailKreinMinus c x s * thetaTailKreinMinus c t s
  have hpoint (s : ℝ) :
      thetaTailKreinTripleIntegrand c w v s (x, t) = P * (R s : ℂ) := by
    unfold thetaTailKreinTripleIntegrand thetaTailChannelIntegrand
    dsimp [P, R, thetaTailKreinPlus, thetaTailKreinMinus]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hK := thetaTailFirstMomentKernel_eq_kreinDifference hc x t
  have hKc := congrArg (fun r : ℝ => (r : ℂ)) hK
  have hcast :
      ((∫ s in Ioi (0 : ℝ), R s : ℝ) : ℂ) =
        ∫ s in Ioi (0 : ℝ), (R s : ℂ) := by
    exact (integral_ofReal (μ := volume.restrict (Ioi (0 : ℝ)))).symm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpoint s),
    MeasureTheory.integral_const_mul]
  unfold thetaTailDoubleLaplaceIntegrand
  dsimp only
  rw [show (thetaTailFirstMomentKernel x t : ℂ) * Complex.exp (w * (x : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (v * (t : ℂ))) =
      (thetaTailFirstMomentKernel x t : ℂ) * P by dsimp [P]; ring]
  change (1 / (2 * c : ℂ)) * (P * ∫ s in Ioi (0 : ℝ), (R s : ℂ)) =
    (thetaTailFirstMomentKernel x t : ℂ) * P
  rw [← hcast]
  push_cast at hKc
  have hKc' : (thetaTailFirstMomentKernel x t : ℂ) =
      (1 / (2 * c : ℂ)) * ((∫ s in Ioi (0 : ℝ), R s : ℝ) : ℂ) := by
    simpa [R] using hKc
  rw [hKc']
  ring

/-- Absolute integrability of the literal theta-tail double-Laplace kernel on the right
Fubini domain. -/
theorem integrable_thetaTailDoubleLaplaceIntegrand
    {c : ℝ} (hc : 0 < c) {w v : ℂ} (hwv : 0 < w.re + v.re) :
    Integrable (thetaTailDoubleLaplaceIntegrand w v) (volume.prod volume) := by
  let μs : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let μz : Measure (ℝ × ℝ) := volume.prod volume
  let F : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    thetaTailKreinTripleIntegrand c w v p.2 p.1
  have htriple := integrable_thetaTailKreinTripleIntegrand c hwv
  have hswap : Integrable F (μz.prod μs) := by
    have hs := htriple.swap
    simpa [F, μs, μz, Function.comp_def, Function.uncurry] using hs
  have hparts := (integrable_prod_iff hswap.aestronglyMeasurable).mp hswap
  let G : ℝ × ℝ → ℂ := fun z =>
    ∫ s in Ioi (0 : ℝ), thetaTailKreinTripleIntegrand c w v s z
  have hGmeas : AEStronglyMeasurable G μz := by
    simpa [G, F, μs, μz] using hswap.aestronglyMeasurable.integral_prod_right'
  have hG : Integrable G μz := by
    apply Integrable.mono' hparts.2 hGmeas
    filter_upwards with z
    exact norm_integral_le_integral_norm _
  have hscaled := hG.const_mul (1 / (2 * c : ℂ))
  apply hscaled.congr
  filter_upwards with z
  exact integral_thetaTailKreinTripleIntegrand_eq_kernel hc w v z.1 z.2

theorem integrable_thetaTailDoubleLaplaceIntegrand_of_sum_re_neg
    {c : ℝ} (hc : 0 < c) {w v : ℂ} (hwv : w.re + v.re < 0) :
    Integrable (thetaTailDoubleLaplaceIntegrand w v) (volume.prod volume) := by
  have hpos : Integrable (thetaTailDoubleLaplaceIntegrand (-w) (-v))
      (volume.prod volume) := by
    apply integrable_thetaTailDoubleLaplaceIntegrand hc
    simp only [neg_re]
    linarith
  have hmp : MeasurePreserving
      (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have hemb : MeasurableEmbedding
      (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hcomp : Integrable (fun z : ℝ × ℝ =>
      thetaTailDoubleLaplaceIntegrand (-w) (-v) (-z.1, -z.2))
      (volume.prod volume) := by
    exact (hmp.integrable_comp_emb hemb).mpr hpos
  apply hcomp.congr
  filter_upwards with z
  exact thetaTailDoubleLaplaceIntegrand_neg_neg w v z

/-- The literal theta tail first-moment kernel has every two-variable exponential moment. -/
theorem integrable_thetaTailDoubleLaplaceIntegrand_all (w v : ℂ) :
    Integrable (thetaTailDoubleLaplaceIntegrand w v) (volume.prod volume) := by
  by_cases hpos : 0 < w.re + v.re
  · exact integrable_thetaTailDoubleLaplaceIntegrand (c := 1) (by norm_num) hpos
  by_cases hneg : w.re + v.re < 0
  · exact integrable_thetaTailDoubleLaplaceIntegrand_of_sum_re_neg
      (c := 1) (by norm_num) hneg
  have hzero : w.re + v.re = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
  have hp : Integrable
      (thetaTailDoubleLaplaceIntegrand (w + 1) (v + 1))
      (volume.prod volume) := by
    apply integrable_thetaTailDoubleLaplaceIntegrand (c := 1) (by norm_num)
    simp only [add_re, one_re]
    linarith
  have hm : Integrable
      (thetaTailDoubleLaplaceIntegrand (w - 1) (v - 1))
      (volume.prod volume) := by
    apply integrable_thetaTailDoubleLaplaceIntegrand_of_sum_re_neg
      (c := 1) (by norm_num)
    simp only [sub_re, one_re]
    linarith
  have hfactor : Continuous (fun z : ℝ × ℝ =>
      Complex.exp (-(((z.1 + z.2 : ℝ) : ℂ)))) := by fun_prop
  have hpoint (z : ℝ × ℝ) :
      thetaTailDoubleLaplaceIntegrand w v z =
        thetaTailDoubleLaplaceIntegrand (w + 1) (v + 1) z *
          Complex.exp (-(((z.1 + z.2 : ℝ) : ℂ))) := by
    unfold thetaTailDoubleLaplaceIntegrand
    rw [show (w + 1) * (z.1 : ℂ) = w * (z.1 : ℂ) + (z.1 : ℂ) by ring,
      show (v + 1) * (z.2 : ℂ) = v * (z.2 : ℂ) + (z.2 : ℂ) by ring,
      Complex.exp_add, Complex.exp_add, map_mul, ← Complex.exp_conj]
    simp_rw [← Complex.exp_conj]
    simp only [Complex.conj_ofReal, ofReal_add, Complex.exp_neg]
    rw [Complex.exp_add]
    field_simp [Complex.exp_ne_zero]
  have hmeasProd : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      thetaTailDoubleLaplaceIntegrand (w + 1) (v + 1) z *
        Complex.exp (-(((z.1 + z.2 : ℝ) : ℂ)))) (volume.prod volume) :=
    hp.aestronglyMeasurable.mul hfactor.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (thetaTailDoubleLaplaceIntegrand w v) (volume.prod volume) := by
    apply hmeasProd.congr
    filter_upwards with z
    exact (hpoint z).symm
  apply Integrable.mono' (hp.norm.add hm.norm) hmeas
  filter_upwards with z
  simpa only [ofReal_zero, add_zero, Pi.add_apply] using
    norm_thetaTailDoubleLaplaceIntegrand_real_tilt_le_unit_tilts
      w v (r := 0) (by norm_num) z

/-- Canonical positive real sequence decreasing to zero for the removable-hyperplane limit. -/
def thetaTailVanishingRealTilt (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Dominated convergence of the literal double Laplace integral under a vanishing positive real
tilt in its first spectral coordinate. -/
theorem tendsto_integral_thetaTailDoubleLaplaceIntegrand_first_real_tilt (w v : ℂ) :
    Tendsto
      (fun n : ℕ => ∫ z : ℝ × ℝ,
        thetaTailDoubleLaplaceIntegrand
          (w + (thetaTailVanishingRealTilt n : ℂ)) v z ∂(volume.prod volume))
      atTop
      (𝓝 (∫ z : ℝ × ℝ,
        thetaTailDoubleLaplaceIntegrand w v z ∂(volume.prod volume))) := by
  let g : ℝ × ℝ → ℝ := fun z =>
    ‖thetaTailDoubleLaplaceIntegrand (w + 1) v z‖ +
      ‖thetaTailDoubleLaplaceIntegrand (w - 1) v z‖
  have hr0 : Tendsto thetaTailVanishingRealTilt atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hrabs (n : ℕ) : |thetaTailVanishingRealTilt n| ≤ 1 := by
    dsimp [thetaTailVanishingRealTilt]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hg : Integrable g (volume.prod volume) := by
    exact (integrable_thetaTailDoubleLaplaceIntegrand_all (w + 1) v).norm.add
      (integrable_thetaTailDoubleLaplaceIntegrand_all (w - 1) v).norm
  refine tendsto_integral_of_dominated_convergence g
    (fun n => (integrable_thetaTailDoubleLaplaceIntegrand_all
      (w + (thetaTailVanishingRealTilt n : ℂ)) v).aestronglyMeasurable)
    hg ?_ ?_
  · intro n
    filter_upwards with z
    exact norm_thetaTailDoubleLaplaceIntegrand_first_real_tilt_le_unit_tilts
      w v (hrabs n) z
  · filter_upwards with z
    have hcont : Continuous (fun a : ℝ =>
        thetaTailDoubleLaplaceIntegrand (w + (a : ℂ)) v z) := by
      unfold thetaTailDoubleLaplaceIntegrand
      fun_prop
    simpa [Function.comp_def, ofReal_zero, add_zero] using
      hcont.continuousAt.tendsto.comp hr0

lemma integral_thetaTailDoubleLaplaceIntegrand_neg_neg (w v : ℂ) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      ∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand (-w) (-v) z
        ∂(volume.prod volume) := by
  have hmp : MeasurePreserving
      (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have hemb : MeasurableEmbedding
      (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hreflect := hmp.integral_comp hemb
    (thetaTailDoubleLaplaceIntegrand (-w) (-v))
  rw [show (fun z : ℝ × ℝ =>
      thetaTailDoubleLaplaceIntegrand (-w) (-v)
        (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ) z)) =
        thetaTailDoubleLaplaceIntegrand w v by
    funext z
    change thetaTailDoubleLaplaceIntegrand (-w) (-v) (-z.1, -z.2) = _
    exact thetaTailDoubleLaplaceIntegrand_neg_neg w v z] at hreflect
  exact hreflect

/-- Product-measure double Laplace transform of the positive theta tail-density is the actual
theta-transform Bezoutian throughout the right Fubini domain. -/
theorem integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      thetaBilateralLaplaceBezoutian w v := by
  have hsum : 0 < w.re + v.re := by simpa using hwv
  have hswap := integral_thetaTailKreinTriple_swap c hsum
  have hbez :=
    integral_thetaTailKreinDifference_eq_bilateralLaplaceBezoutian hc hwv
  have hleft :
      (1 / (2 * c : ℂ)) *
          (∫ s in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
            thetaTailKreinTripleIntegrand c w v s z ∂(volume.prod volume)) =
        thetaBilateralLaplaceBezoutian w v := by
    simpa only [integral_prod_thetaTailKreinTripleIntegrand] using hbez
  calc
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ, (1 / (2 * c : ℂ)) *
          (∫ s in Ioi (0 : ℝ), thetaTailKreinTripleIntegrand c w v s z)
            ∂(volume.prod volume) := by
          apply integral_congr_ae
          filter_upwards with z
          exact (integral_thetaTailKreinTripleIntegrand_eq_kernel hc w v z.1 z.2).symm
    _ = (1 / (2 * c : ℂ)) *
        (∫ z : ℝ × ℝ, (∫ s in Ioi (0 : ℝ),
          thetaTailKreinTripleIntegrand c w v s z) ∂(volume.prod volume)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = (1 / (2 * c : ℂ)) *
        (∫ s in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
          thetaTailKreinTripleIntegrand c w v s z ∂(volume.prod volume)) := by
          rw [← hswap]
    _ = thetaBilateralLaplaceBezoutian w v := hleft

/-- Iterated-integral form of the exact double Laplace identity. -/
theorem integral_integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    (∫ x : ℝ, ∫ t : ℝ, thetaTailDoubleLaplaceIntegrand w v (x, t)) =
      thetaBilateralLaplaceBezoutian w v := by
  have hsum : 0 < w.re + v.re := by simpa using hwv
  rw [← MeasureTheory.integral_prod
    (thetaTailDoubleLaplaceIntegrand w v)
    (integrable_thetaTailDoubleLaplaceIntegrand hc hsum)]
  exact integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian hc hwv

/-! ### Removable extension and the cofinal exponential-family criterion -/

theorem thetaBilateralLaplace_eq_xiCent (w : ℂ) :
    thetaBilateralLaplace w = xiCent w := by
  rw [thetaBilateralLaplace_eq_XiC]
  calc
    XiC (I * w) = XiC (-I * (-w)) := by congr 1 <;> ring
    _ = xiCent (-w) := (xiCent_eq_XiC (-w)).symm
    _ = xiCent w := xiCent_even w

theorem thetaBilateralLaplaceMoment_eq_deriv_xiCent (w : ℂ) :
    thetaBilateralLaplaceMoment w = deriv xiCent w := by
  rw [← deriv_thetaBilateralLaplace]
  congr 1
  funext z
  exact thetaBilateralLaplace_eq_xiCent z

/-- Entire theta tail first-moment Bezoutian in the holomorphic variable `y = conj v`. -/
def thetaTailFirstMomentBezoutian (w y : ℂ) : ℂ :=
  xiCentBezoutian w y

theorem differentiable_thetaTailFirstMomentBezoutian (w : ℂ) :
    Differentiable ℂ (thetaTailFirstMomentBezoutian w) := by
  exact differentiable_xiCentBezoutian w

theorem thetaTailFirstMomentBezoutian_neg_neg (w y : ℂ) :
    thetaTailFirstMomentBezoutian (-w) (-y) =
      thetaTailFirstMomentBezoutian w y := by
  have hfun : xiCentBezoutianNumerator (-w) =
      fun z => -xiCentBezoutianNumerator w (-z) := by
    funext z
    unfold xiCentBezoutianNumerator
    rw [deriv_xiCent_neg, xiCent_even, xiCent_even, deriv_xiCent_neg]
    ring
  unfold thetaTailFirstMomentBezoutian xiCentBezoutian
  rw [hfun]
  simpa using HTGeometry.dslope_neg_comp_neg
    (xiCentBezoutianNumerator w) (-w) (-y)

theorem thetaTailFirstMomentBezoutian_comm (w y : ℂ) :
    thetaTailFirstMomentBezoutian w y =
      thetaTailFirstMomentBezoutian y w := by
  by_cases h : w + y = 0
  · have hy : y = -w := by
      calc
        y = (w + y) - w := by ring
        _ = -w := by rw [h]; ring
    rw [hy]
    simpa only [neg_neg] using
      (thetaTailFirstMomentBezoutian_neg_neg w (-w)).symm
  · rw [thetaTailFirstMomentBezoutian, thetaTailFirstMomentBezoutian,
      xiCentBezoutian_eq_div h,
      xiCentBezoutian_eq_div (by intro hyw; apply h; rw [add_comm]; exact hyw),
      xiCentBezoutianNumerator, xiCentBezoutianNumerator]
    ring

theorem continuous_thetaTailFirstMomentBezoutian_left (y : ℂ) :
    Continuous (fun w => thetaTailFirstMomentBezoutian w y) := by
  have hfun : (fun w => thetaTailFirstMomentBezoutian w y) =
      thetaTailFirstMomentBezoutian y := by
    funext w
    exact thetaTailFirstMomentBezoutian_comm w y
  rw [hfun]
  exact (differentiable_thetaTailFirstMomentBezoutian y).continuous

theorem thetaTailFirstMomentBezoutian_eq_bilateralLaplaceBezoutian
    {w v : ℂ} (h : w + (starRingEnd ℂ) v ≠ 0) :
    thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) =
      thetaBilateralLaplaceBezoutian w v := by
  rw [thetaTailFirstMomentBezoutian, xiCentBezoutian_eq_div h,
    xiCentBezoutianNumerator, thetaBilateralLaplaceBezoutian,
    thetaBilateralLaplaceMoment_eq_deriv_xiCent w,
    thetaBilateralLaplaceMoment_eq_deriv_xiCent v,
    thetaBilateralLaplace_eq_xiCent w,
    thetaBilateralLaplace_eq_xiCent v,
    xiCent_conj, deriv_xiCent_conj]

theorem integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  rw [integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian hc hwv]
  exact (thetaTailFirstMomentBezoutian_eq_bilateralLaplaceBezoutian
    (ne_of_apply_ne Complex.re (ne_of_gt hwv))).symm

theorem integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_of_sum_re_neg
    {w v : ℂ} (hwv : (w + (starRingEnd ℂ) v).re < 0) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  have hpos : 0 < ((-w) + (starRingEnd ℂ) (-v)).re := by
    have hs : w.re + v.re < 0 := by simpa using hwv
    have : 0 < -w.re + -v.re := by linarith
    simpa using this
  calc
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand (-w) (-v) z
          ∂(volume.prod volume) :=
      integral_thetaTailDoubleLaplaceIntegrand_neg_neg w v
    _ = thetaTailFirstMomentBezoutian (-w) ((starRingEnd ℂ) (-v)) :=
      integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
        (c := 1) (by norm_num) hpos
    _ = thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
      simpa only [map_neg] using
        thetaTailFirstMomentBezoutian_neg_neg w ((starRingEnd ℂ) v)

theorem integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_of_sum_re_zero
    {w v : ℂ} (hwv : (w + (starRingEnd ℂ) v).re = 0) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  have hr0 : Tendsto thetaTailVanishingRealTilt atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft := tendsto_integral_thetaTailDoubleLaplaceIntegrand_first_real_tilt w v
  have hcont : Continuous (fun a : ℝ =>
      thetaTailFirstMomentBezoutian (w + (a : ℂ)) ((starRingEnd ℂ) v)) := by
    exact (continuous_thetaTailFirstMomentBezoutian_left
      ((starRingEnd ℂ) v)).comp (by fun_prop)
  have hright : Tendsto
      (fun n : ℕ => thetaTailFirstMomentBezoutian
        (w + (thetaTailVanishingRealTilt n : ℂ)) ((starRingEnd ℂ) v))
      atTop (𝓝 (thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v))) := by
    simpa [Function.comp_def, ofReal_zero, add_zero] using
      hcont.continuousAt.tendsto.comp hr0
  have heq (n : ℕ) :
      (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand
        (w + (thetaTailVanishingRealTilt n : ℂ)) v z
          ∂(volume.prod volume)) =
        thetaTailFirstMomentBezoutian
          (w + (thetaTailVanishingRealTilt n : ℂ)) ((starRingEnd ℂ) v) := by
    have hrpos : 0 < thetaTailVanishingRealTilt n := by
      unfold thetaTailVanishingRealTilt
      positivity
    have hpos : 0 <
        ((w + (thetaTailVanishingRealTilt n : ℂ)) +
          (starRingEnd ℂ) v).re := by
      have hs : 0 < w.re + thetaTailVanishingRealTilt n + v.re := by
        have hz : w.re + v.re = 0 := by simpa using hwv
        linarith
      simpa [add_assoc] using hs
    exact integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
      (c := 1) (by norm_num) hpos
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  exact (heq n).symm

/-- Equation (4), including the removable hyperplane: the literal product-measure double Laplace
transform of the positive theta tail-density equals the entire theta first-moment Bezoutian for
all complex spectral parameters. -/
theorem integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_all
    (w v : ℂ) :
    (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand w v z
        ∂(volume.prod volume)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  by_cases hpos : 0 < (w + (starRingEnd ℂ) v).re
  · exact integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
      (c := 1) (by norm_num) hpos
  by_cases hneg : (w + (starRingEnd ℂ) v).re < 0
  · exact integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_of_sum_re_neg
      hneg
  have hzero : (w + (starRingEnd ℂ) v).re = 0 :=
    le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
  exact integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_of_sum_re_zero
    hzero

/-- Iterated-integral form of the all-plane removable double Laplace identity. -/
theorem integral_integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_all
    (w v : ℂ) :
    (∫ x : ℝ, ∫ t : ℝ, thetaTailDoubleLaplaceIntegrand w v (x, t)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  rw [← MeasureTheory.integral_prod
    (thetaTailDoubleLaplaceIntegrand w v)
    (integrable_thetaTailDoubleLaplaceIntegrand_all w v)]
  exact integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian_all w v

theorem integral_integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    (∫ x : ℝ, ∫ t : ℝ, thetaTailDoubleLaplaceIntegrand w v (x, t)) =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  rw [integral_integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian hc hwv]
  exact (thetaTailFirstMomentBezoutian_eq_bilateralLaplaceBezoutian
    (ne_of_apply_ne Complex.re (ne_of_gt hwv))).symm

/-- RH is exactly positivity of the removable theta tail first-moment Bezoutian on every finite
system of nodes in the cofinal Euler half-plane. -/
theorem riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        (Matrix.of fun j k =>
          thetaTailFirstMomentBezoutian ((w j : ℂ))
            ((starRingEnd ℂ) ((w k : ℂ)))).PosSemidef := by
  simpa only [thetaTailFirstMomentBezoutian] using
    riemannHypothesis_iff_posSemidef_xiCentBezoutian

/-- Matrix entry of the exact two-Volterra Krein difference. -/
def thetaTailKreinDifferenceEntry (c : ℝ) (w v : ℂ) : ℂ :=
  (1 / (2 * c : ℂ)) * ∫ s in Ioi (0 : ℝ),
    (thetaTailKreinPlusTransform c w s *
        (starRingEnd ℂ) (thetaTailKreinPlusTransform c v s) -
      thetaTailKreinMinusTransform c w s *
        (starRingEnd ℂ) (thetaTailKreinMinusTransform c v s))

theorem thetaTailKreinDifferenceEntry_eq_thetaTailFirstMomentBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    thetaTailKreinDifferenceEntry c w v =
      thetaTailFirstMomentBezoutian w ((starRingEnd ℂ) v) := by
  unfold thetaTailKreinDifferenceEntry
  rw [integral_thetaTailKreinDifference_eq_bilateralLaplaceBezoutian hc hwv]
  exact (thetaTailFirstMomentBezoutian_eq_bilateralLaplaceBezoutian
    (ne_of_apply_ne Complex.re (ne_of_gt hwv))).symm

/-- Equation (25): for every aperture `c > 0`, RH is exactly positivity of the finite
two-Volterra Krein-difference matrices on the cofinal exponential family. -/
theorem riemannHypothesis_iff_posSemidef_thetaTailKreinDifference
    {c : ℝ} (hc : 0 < c) :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        (Matrix.of fun j k =>
          thetaTailKreinDifferenceEntry c ((w j : ℂ)) ((w k : ℂ))).PosSemidef := by
  rw [riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian]
  constructor
  · intro h n w
    have hpsd := h n w
    have heq :
        (Matrix.of fun j k =>
          thetaTailKreinDifferenceEntry c ((w j : ℂ)) ((w k : ℂ))) =
        Matrix.of fun j k =>
          thetaTailFirstMomentBezoutian ((w j : ℂ))
            ((starRingEnd ℂ) ((w k : ℂ))) := by
      ext j k
      have hj : 0 < ((w j : ℂ)).re := lt_trans (by norm_num) (w j).2
      have hk : 0 < ((w k : ℂ)).re := lt_trans (by norm_num) (w k).2
      have hsum : 0 < (((w j : ℂ)) + (starRingEnd ℂ) ((w k : ℂ))).re := by
        simpa using add_pos hj hk
      exact thetaTailKreinDifferenceEntry_eq_thetaTailFirstMomentBezoutian hc hsum
    rwa [heq]
  · intro h n w
    have hpsd := h n w
    have heq :
        (Matrix.of fun j k =>
          thetaTailKreinDifferenceEntry c ((w j : ℂ)) ((w k : ℂ))) =
        Matrix.of fun j k =>
          thetaTailFirstMomentBezoutian ((w j : ℂ))
            ((starRingEnd ℂ) ((w k : ℂ))) := by
      ext j k
      have hj : 0 < ((w j : ℂ)).re := lt_trans (by norm_num) (w j).2
      have hk : 0 < ((w k : ℂ)).re := lt_trans (by norm_num) (w k).2
      have hsum : 0 < (((w j : ℂ)) + (starRingEnd ℂ) ((w k : ℂ))).re := by
        simpa using add_pos hj hk
      exact thetaTailKreinDifferenceEntry_eq_thetaTailFirstMomentBezoutian hc hsum
    rwa [← heq]

/-- Exact source-side form of the cofinal exponential-family criterion: RH is equivalent to
positive semidefiniteness of every finite matrix of literal double Laplace integrals. -/
theorem riemannHypothesis_iff_posSemidef_thetaTailDoubleLaplace :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        (Matrix.of fun j k =>
          ∫ x : ℝ, ∫ t : ℝ,
            thetaTailDoubleLaplaceIntegrand ((w j : ℂ)) ((w k : ℂ)) (x, t)).PosSemidef := by
  rw [riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian]
  constructor
  · intro h n w
    have hpsd := h n w
    have heq :
        (Matrix.of fun j k =>
          ∫ x : ℝ, ∫ t : ℝ,
            thetaTailDoubleLaplaceIntegrand ((w j : ℂ)) ((w k : ℂ)) (x, t)) =
        Matrix.of fun j k =>
          thetaTailFirstMomentBezoutian ((w j : ℂ))
            ((starRingEnd ℂ) ((w k : ℂ))) := by
      ext j k
      have hj : 0 < ((w j : ℂ)).re := lt_trans (by norm_num) (w j).2
      have hk : 0 < ((w k : ℂ)).re := lt_trans (by norm_num) (w k).2
      have hsum : 0 < (((w j : ℂ)) + (starRingEnd ℂ) ((w k : ℂ))).re := by
        simpa using add_pos hj hk
      exact integral_integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
        (c := 1) (by norm_num) hsum
    rwa [heq]
  · intro h n w
    have hpsd := h n w
    have heq :
        (Matrix.of fun j k =>
          ∫ x : ℝ, ∫ t : ℝ,
            thetaTailDoubleLaplaceIntegrand ((w j : ℂ)) ((w k : ℂ)) (x, t)) =
        Matrix.of fun j k =>
          thetaTailFirstMomentBezoutian ((w j : ℂ))
            ((starRingEnd ℂ) ((w k : ℂ))) := by
      ext j k
      have hj : 0 < ((w j : ℂ)).re := lt_trans (by norm_num) (w j).2
      have hk : 0 < ((w k : ℂ)).re := lt_trans (by norm_num) (w k).2
      have hsum : 0 < (((w j : ℂ)) + (starRingEnd ℂ) ((w k : ℂ))).re := by
        simpa using add_pos hj hk
      exact integral_integral_thetaTailDoubleLaplaceIntegrand_eq_thetaTailFirstMomentBezoutian
        (c := 1) (by norm_num) hsum
    rwa [← heq]

end RHTower
