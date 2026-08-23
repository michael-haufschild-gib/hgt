import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorGenericCouplingMixingEndpoint
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.RHTower.DeckChargeInvariant

/-!
# Nonlinear divisor transport for the source-faithful Hawking theta mirror

The exact Davies--Fulling eikonal response already supplies a genuine moving-mirror scattering
dilation, not a scalar completion ansatz. This file complexifies its total-frequency variable while
keeping real background coupling. The resulting susceptibility is entire in frequency, agrees on
the real frequency axis with the coupling derivative of the full nonlinear theta-mirror response,
and reduces at zero background to `-i * XiC` on the physically tilted line.

Rouche divisor stability then yields the new endpoint: every centered Xi zero survives sufficiently
small nonlinear Hawking background coupling with exactly the same total local multiplicity. Thus
finite-coupling activation of all real tilted sectors cannot by itself prove RH; an off-line divisor
may leave the real sheet while persisting in complex frequency. Any RH-bearing dynamics must add an
orientation, minimum-phase, or first-coupling-order selection law.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Complex-frequency susceptibility density of exact theta-mirror eikonal scattering at a
nonperturbative real background coupling. -/
def thetaCuspHawkingNonlinearCarrierIntegrand
    (a t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * z * (x : ℂ)) *
    Complex.exp (-Complex.I * (t : ℂ) *
      (thetaCuspTiltedSource a x : ℂ)) *
    (-Complex.I * (thetaCuspTiltedSource a x : ℂ))

/-- Complex-frequency continuation of exact nonlinear theta-mirror susceptibility. -/
def thetaCuspHawkingNonlinearCarrier (a t : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, thetaCuspHawkingNonlinearCarrierIntegrand a t z x

def thetaCuspHawkingNonlinearCarrierDerivativeIntegrand
    (a t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (-Complex.I * (x : ℂ)) *
    thetaCuspHawkingNonlinearCarrierIntegrand a t z x

private def thetaCuspHawkingNonlinearSourceBound
    (a : ℝ) (ha : |a| < 1) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (thetaCuspTiltedSchwartzReal a ha)

private theorem thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspTiltedSource a x ∈
      Set.Icc 0 (thetaCuspHawkingNonlinearSourceBound a ha) := by
  constructor
  · unfold thetaCuspTiltedSource
    exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)).le
  · let source : SchwartzMap ℝ ℝ := thetaCuspTiltedSchwartzReal a ha
    have hpos : 0 < thetaCuspTiltedSource a x := by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
    have hnorm := SchwartzMap.norm_le_seminorm ℝ source x
    simpa [source, thetaCuspHawkingNonlinearSourceBound,
      Real.norm_eq_abs, abs_of_pos hpos] using hnorm

private theorem norm_exp_sub_one_le_nonlinearCarrier (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
  simpa [Finset.sum_range_succ, Nat.factorial] using h

private theorem hasDerivAt_thetaCuspHawkingNonlinearCarrierIntegrand
    (a t : ℝ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ =>
      thetaCuspHawkingNonlinearCarrierIntegrand a t w x)
      (thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z x) z := by
  have hlin : HasDerivAt (fun w : ℂ => -Complex.I * w * (x : ℂ))
      (-Complex.I * (x : ℂ)) z := by
    simpa using! (((hasDerivAt_id z).const_mul (-Complex.I)).mul_const (x : ℂ))
  have hprod := hlin.cexp.mul_const
    (Complex.exp (-Complex.I * (t : ℂ) *
      (thetaCuspTiltedSource a x : ℂ)) *
      (-Complex.I * (thetaCuspTiltedSource a x : ℂ)))
  simpa only [thetaCuspHawkingNonlinearCarrierIntegrand,
    thetaCuspHawkingNonlinearCarrierDerivativeIntegrand,
    mul_assoc, mul_comm, mul_left_comm] using hprod

private theorem norm_thetaCuspHawkingNonlinearCarrierIntegrand
    (a t : ℝ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspHawkingNonlinearCarrierIntegrand a t z x‖ =
      Real.exp (z.im * x) * thetaCuspTiltedSource a x := by
  rw [thetaCuspHawkingNonlinearCarrierIntegrand, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp, norm_mul, norm_neg, norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hk : 0 < thetaCuspTiltedSource a x := by
    unfold thetaCuspTiltedSource
    exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
  rw [abs_of_pos hk]
  have hfreq : (-Complex.I * z * (x : ℂ)).re = z.im * x := by
    simp [Complex.mul_re]
  have hcoupling :
      (-Complex.I * (t : ℂ) *
        (thetaCuspTiltedSource a x : ℂ)).re = 0 := by simp
  rw [hfreq, hcoupling, Real.exp_zero, mul_one]

private theorem norm_thetaCuspHawkingNonlinearCarrierDerivativeIntegrand
    (a t : ℝ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z x‖ =
      |x| * (Real.exp (z.im * x) * thetaCuspTiltedSource a x) := by
  rw [thetaCuspHawkingNonlinearCarrierDerivativeIntegrand, norm_mul,
    norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_thetaCuspHawkingNonlinearCarrierIntegrand]

private theorem integrable_thetaCuspHawkingNonlinearCarrierIntegrand
    (a t : ℝ) (z : ℂ) :
    Integrable (thetaCuspHawkingNonlinearCarrierIntegrand a t z) := by
  have hmajor := integrable_exp_abs_mul_thetaCuspFullSource (|z.im| + |a|)
  apply Integrable.mono hmajor
  · apply Continuous.aestronglyMeasurable
    unfold thetaCuspHawkingNonlinearCarrierIntegrand
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    fun_prop
  · filter_upwards with x
    rw [norm_thetaCuspHawkingNonlinearCarrierIntegrand]
    have hexp : z.im * x + a * x ≤ (|z.im| + |a|) * |x| := by
      calc
        z.im * x + a * x ≤ |z.im * x| + |a * x| := add_le_add (le_abs_self _) (le_abs_self _)
        _ = (|z.im| + |a|) * |x| := by rw [abs_mul, abs_mul]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos x).le),
      thetaCuspTiltedSource]
    calc
      Real.exp (z.im * x) *
          (Real.exp (a * x) * thetaCuspFullSource x) =
        Real.exp (z.im * x + a * x) * thetaCuspFullSource x := by
          rw [Real.exp_add]
          ring
      _ ≤ Real.exp ((|z.im| + |a|) * |x|) *
          thetaCuspFullSource x :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
          (thetaCuspFullSource_pos x).le

private theorem integrable_thetaCuspHawkingNonlinearCarrierDerivativeIntegrand
    (a t : ℝ) (z : ℂ) :
    Integrable (thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z) := by
  have hmajor :=
    integrable_abs_mul_exp_abs_mul_thetaCuspFullSource (|z.im| + |a|)
  apply Integrable.mono hmajor
  · apply Continuous.aestronglyMeasurable
    unfold thetaCuspHawkingNonlinearCarrierDerivativeIntegrand
      thetaCuspHawkingNonlinearCarrierIntegrand
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    fun_prop
  · filter_upwards with x
    rw [norm_thetaCuspHawkingNonlinearCarrierDerivativeIntegrand]
    have hexp : z.im * x + a * x ≤ (|z.im| + |a|) * |x| := by
      calc
        z.im * x + a * x ≤ |z.im * x| + |a * x| := add_le_add (le_abs_self _) (le_abs_self _)
        _ = (|z.im| + |a|) * |x| := by rw [abs_mul, abs_mul]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le)
        (thetaCuspFullSource_pos x).le), thetaCuspTiltedSource]
    calc
      |x| * (Real.exp (z.im * x) *
          (Real.exp (a * x) * thetaCuspFullSource x)) =
        |x| * (Real.exp (z.im * x + a * x) *
          thetaCuspFullSource x) := by rw [Real.exp_add]; ring
      _ ≤ |x| * (Real.exp ((|z.im| + |a|) * |x|) *
          thetaCuspFullSource x) := by
        gcongr
        exact (thetaCuspFullSource_pos x).le
      _ = |x| * Real.exp ((|z.im| + |a|) * |x|) *
          thetaCuspFullSource x := by ring

theorem hasDerivAt_thetaCuspHawkingNonlinearCarrier
    (a t : ℝ) (z₀ : ℂ) :
    HasDerivAt (thetaCuspHawkingNonlinearCarrier a t)
      (∫ x : ℝ,
        thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z₀ x) z₀ := by
  let B : ℝ := |z₀.im| + 1 + |a|
  let bound : ℝ → ℝ := fun x =>
    |x| * Real.exp (B * |x|) * thetaCuspFullSource x
  have hbound : Integrable bound :=
    integrable_abs_mul_exp_abs_mul_thetaCuspFullSource B
  have hdom : ∀ᵐ x : ℝ, ∀ z ∈ Metric.ball z₀ 1,
      ‖thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z x‖ ≤ bound x := by
    filter_upwards with x
    intro z hz
    have hdist : ‖z - z₀‖ < 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    have him : |z.im| ≤ |z₀.im| + 1 := by
      calc
        |z.im| = |z₀.im + (z.im - z₀.im)| := by ring_nf
        _ ≤ |z₀.im| + |z.im - z₀.im| := abs_add_le _ _
        _ ≤ |z₀.im| + 1 := by linarith
    rw [norm_thetaCuspHawkingNonlinearCarrierDerivativeIntegrand,
      thetaCuspTiltedSource]
    dsimp only [bound, B]
    have hexp : z.im * x + a * x ≤ (|z₀.im| + 1 + |a|) * |x| := by
      calc
        z.im * x + a * x ≤ |z.im| * |x| + |a| * |x| := by
          rw [← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
        _ ≤ (|z₀.im| + 1) * |x| + |a| * |x| := by gcongr
        _ = (|z₀.im| + 1 + |a|) * |x| := by ring
    calc
      |x| * (Real.exp (z.im * x) *
          (Real.exp (a * x) * thetaCuspFullSource x)) =
        |x| * (Real.exp (z.im * x + a * x) *
          thetaCuspFullSource x) := by rw [Real.exp_add]; ring
      _ ≤ |x| * (Real.exp ((|z₀.im| + 1 + |a|) * |x|) *
          thetaCuspFullSource x) := by
        gcongr
        exact (thetaCuspFullSource_pos x).le
      _ = |x| * Real.exp ((|z₀.im| + 1 + |a|) * |x|) *
          thetaCuspFullSource x := by ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => thetaCuspHawkingNonlinearCarrierIntegrand a t z x)
    (F' := fun z x => thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z x)
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := bound)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => by
      apply Continuous.aestronglyMeasurable
      unfold thetaCuspHawkingNonlinearCarrierIntegrand
      have hk : Continuous (thetaCuspTiltedSource a) :=
        (contDiff_thetaCuspTiltedSource a).continuous
      fun_prop)
    (integrable_thetaCuspHawkingNonlinearCarrierIntegrand a t z₀)
    (integrable_thetaCuspHawkingNonlinearCarrierDerivativeIntegrand a t z₀).1
    hdom hbound
    (by
      filter_upwards with x
      intro z _
      exact hasDerivAt_thetaCuspHawkingNonlinearCarrierIntegrand a t z x)
  exact hresult.2

theorem thetaCuspHawkingNonlinearCarrier_differentiable
    (a t : ℝ) : Differentiable ℂ (thetaCuspHawkingNonlinearCarrier a t) :=
  fun z => (hasDerivAt_thetaCuspHawkingNonlinearCarrier a t z).differentiableAt

/-- Uniform closed-disc weak-background bound for the full nonlinear susceptibility carrier. -/
theorem norm_thetaCuspHawkingNonlinearCarrier_sub_zero_le
    (a t w R : ℝ) (ha : |a| < 1) (ht : |t| ≤ 1)
    (z : ℂ) (hz : z ∈ Metric.closedBall (w : ℂ) R) :
    ‖thetaCuspHawkingNonlinearCarrier a t z -
        thetaCuspHawkingNonlinearCarrier a 0 z‖ ≤
      |t| * (Real.exp (thetaCuspHawkingNonlinearSourceBound a ha) *
        thetaCuspHawkingNonlinearSourceBound a ha) *
          ∫ x : ℝ,
            Real.exp ((R + |a|) * |x|) * thetaCuspFullSource x := by
  let M := thetaCuspHawkingNonlinearSourceBound a ha
  let C := Real.exp M * M
  let major : ℝ → ℝ := fun x =>
    Real.exp ((R + |a|) * |x|) * thetaCuspFullSource x
  have hM : 0 ≤ M :=
    (thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound a ha 0).1.trans
      (thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound a ha 0).2
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le hM
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hmajor : Integrable major :=
    integrable_exp_abs_mul_thetaCuspFullSource (R + |a|)
  have hscaled : Integrable (fun x : ℝ => (|t| * C) * major x) :=
    hmajor.const_mul (|t| * C)
  have hpoint : ∀ x : ℝ,
      ‖thetaCuspHawkingNonlinearCarrierIntegrand a t z x -
          thetaCuspHawkingNonlinearCarrierIntegrand a 0 z x‖ ≤
        (|t| * C) * major x := by
    intro x
    let k := thetaCuspTiltedSource a x
    have hk := thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound a ha x
    have hkpos : 0 < k := by
      dsimp only [k]
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
    have hrewrite :
        thetaCuspHawkingNonlinearCarrierIntegrand a t z x -
            thetaCuspHawkingNonlinearCarrierIntegrand a 0 z x =
          Complex.exp (-Complex.I * z * (x : ℂ)) *
            (Complex.exp (-Complex.I * (t : ℂ) * (k : ℂ)) - 1) *
              (-Complex.I * (k : ℂ)) := by
      unfold thetaCuspHawkingNonlinearCarrierIntegrand
      dsimp only [k]
      simp
      ring
    have hphase :
        ‖Complex.exp (-Complex.I * z * (x : ℂ))‖ =
          Real.exp (z.im * x) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have harg :
        ‖-Complex.I * (t : ℂ) * (k : ℂ)‖ = |t| * k := by
      rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hkpos]
    have hdefect := norm_exp_sub_one_le_nonlinearCarrier
      (-Complex.I * (t : ℂ) * (k : ℂ))
    rw [harg] at hdefect
    have htkM : |t| * k ≤ M := by
      calc
        |t| * k ≤ 1 * k := mul_le_mul_of_nonneg_right ht hk.1
        _ ≤ 1 * M := mul_le_mul_of_nonneg_left hk.2 zero_le_one
        _ = M := one_mul M
    have him : |z.im| ≤ R := by
      have hdist : ‖z - (w : ℂ)‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
      have himnorm : |z.im| ≤ ‖z - (w : ℂ)‖ := by
        have h := Complex.abs_im_le_norm (z - (w : ℂ))
        simpa using h
      exact himnorm.trans hdist
    have hexp : z.im * x + a * x ≤ (R + |a|) * |x| := by
      calc
        z.im * x + a * x ≤ |z.im| * |x| + |a| * |x| := by
          rw [← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
        _ ≤ R * |x| + |a| * |x| := by gcongr
        _ = (R + |a|) * |x| := by ring
    rw [hrewrite, norm_mul, norm_mul, hphase, norm_mul, norm_neg,
      norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkpos]
    calc
      Real.exp (z.im * x) *
          ‖Complex.exp (-Complex.I * (t : ℂ) * (k : ℂ)) - 1‖ * k
          ≤ Real.exp (z.im * x) *
              ((|t| * k) * Real.exp (|t| * k)) * k := by gcongr
      _ ≤ Real.exp (z.im * x) *
              ((|t| * k) * Real.exp M) * k := by
            gcongr
      _ = |t| * Real.exp M * (Real.exp (z.im * x) * (k * k)) := by ring
      _ ≤ |t| * Real.exp M * (Real.exp (z.im * x) * (M * k)) := by
            gcongr
            exact hk.2
      _ = (|t| * C) *
          (Real.exp (z.im * x) * k) := by
            dsimp only [C]
            ring
      _ ≤ (|t| * C) * major x := by
            have hcarrier : Real.exp (z.im * x) * k ≤ major x := by
              dsimp only [k, major]
              rw [thetaCuspTiltedSource]
              calc
                Real.exp (z.im * x) *
                    (Real.exp (a * x) * thetaCuspFullSource x) =
                  Real.exp (z.im * x + a * x) *
                    thetaCuspFullSource x := by rw [Real.exp_add]; ring
                _ ≤ Real.exp ((R + |a|) * |x|) *
                    thetaCuspFullSource x := by
                  gcongr
                  exact (thetaCuspFullSource_pos x).le
            exact mul_le_mul_of_nonneg_left hcarrier
              (mul_nonneg ht0 hC)
  change ‖(∫ x : ℝ, thetaCuspHawkingNonlinearCarrierIntegrand a t z x) -
      (∫ x : ℝ, thetaCuspHawkingNonlinearCarrierIntegrand a 0 z x)‖ ≤ _
  rw [← integral_sub
      (integrable_thetaCuspHawkingNonlinearCarrierIntegrand a t z)
      (integrable_thetaCuspHawkingNonlinearCarrierIntegrand a 0 z)]
  calc
    ‖∫ x : ℝ,
        (thetaCuspHawkingNonlinearCarrierIntegrand a t z x -
          thetaCuspHawkingNonlinearCarrierIntegrand a 0 z x)‖ ≤
        ∫ x : ℝ, (|t| * C) * major x :=
      norm_integral_le_of_norm_le hscaled
        (Filter.Eventually.of_forall hpoint)
    _ = |t| * C * ∫ x : ℝ, major x := by
      rw [integral_const_mul]
    _ = _ := by rfl

/-- At zero background coupling, exact nonlinear susceptibility is the tilted Xi carrier. -/
theorem thetaCuspHawkingNonlinearCarrier_zero_eq_XiC
    (a : ℝ) (z : ℂ) :
    thetaCuspHawkingNonlinearCarrier a 0 z =
      -Complex.I * XiC (z + (a : ℂ) * Complex.I) := by
  rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all,
    thetaCuspHawkingNonlinearCarrier,
    thetaCuspFourierLaplace, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaCuspHawkingNonlinearCarrierIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  simp only [ofReal_zero, mul_zero]
  have hphase :
      -Complex.I * (z + (a : ℂ) * Complex.I) * (x : ℂ) =
        -Complex.I * z * (x : ℂ) + (a * x : ℝ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    simp
  rw [hphase, Complex.exp_add, thetaCuspTiltedSource]
  push_cast
  simp
  ring

/-- The zero-background susceptibility divisor has exactly the Xi multiplicity after tilt. -/
theorem zeroMult_thetaCuspHawkingNonlinearCarrier_zero
    (a w : ℝ) :
    GaloisForLFunctions.HTGeometry.zeroMult
        (thetaCuspHawkingNonlinearCarrier a 0) (w : ℂ) =
      GaloisForLFunctions.HTGeometry.zeroMult XiC
        ((w : ℂ) + (a : ℂ) * Complex.I) := by
  rw [GaloisForLFunctions.HTGeometry.zeroMult,
    GaloisForLFunctions.HTGeometry.zeroMult]
  have hfun : thetaCuspHawkingNonlinearCarrier a 0 =
      fun z : ℂ => -Complex.I * XiC (z + (a : ℂ) * Complex.I) := by
    funext z
    exact thetaCuspHawkingNonlinearCarrier_zero_eq_XiC a z
  rw [hfun]
  change (analyticOrderAt
      ((fun _z : ℂ => -Complex.I) *
        (fun z : ℂ => XiC (z + (a : ℂ) * Complex.I))) (w : ℂ)).toNat = _
  have hshift : AnalyticAt ℂ
      (fun z : ℂ => XiC (z + (a : ℂ) * Complex.I)) (w : ℂ) := by
    exact (XiC_analytic _ (Set.mem_univ _)).comp
      (analyticAt_id.add (analyticAt_const.mul analyticAt_const))
  rw [analyticOrderAt_mul analyticAt_const hshift,
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by simp), zero_add,
    analyticOrderAt_comp_add]

private theorem exists_thetaCuspHawkingNonlinearCarrier_isolatingRadius
    (alpha : ℂ) :
    ∃ delta > 0, ∀ z ∈ Metric.closedBall (alpha.re : ℂ) (2 * delta),
      thetaCuspHawkingNonlinearCarrier alpha.im 0 z = 0 →
        z = (alpha.re : ℂ) := by
  have hpunct := eventually_XiC_ne_zero_punctured alpha
  change {w : ℂ | XiC w ≠ 0} ∈
    nhdsWithin alpha ({alpha} : Set ℂ)ᶜ at hpunct
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpunct
  obtain ⟨U, hUnhds, hU⟩ := hpunct
  obtain ⟨r, hr, hballU⟩ := Metric.eventually_nhds_iff.mp hUnhds
  refine ⟨r / 4, by positivity, ?_⟩
  intro z hz hcarrier
  let y : ℂ := z + (alpha.im : ℂ) * Complex.I
  have hdecomp : (alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I = alpha :=
    Complex.re_add_im alpha
  have hyDist : dist y alpha < r := by
    have heq : dist y alpha = dist z (alpha.re : ℂ) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      dsimp only [y]
      calc
        z + (alpha.im : ℂ) * Complex.I - alpha =
            z + (alpha.im : ℂ) * Complex.I -
              ((alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I) := by
                congr 1
                exact hdecomp.symm
        _ = z - (alpha.re : ℂ) := by ring
    rw [heq]
    have hz' := Metric.mem_closedBall.mp hz
    linarith
  have hyZero : XiC y = 0 := by
    have hbase := thetaCuspHawkingNonlinearCarrier_zero_eq_XiC alpha.im z
    rw [hcarrier] at hbase
    have hmul : -Complex.I * XiC y = 0 := by
      simpa only [y] using hbase.symm
    exact (mul_eq_zero.mp hmul).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  by_contra hzw
  have hyne : y ≠ alpha := by
    intro hy
    apply hzw
    calc
      z = y - (alpha.im : ℂ) * Complex.I := by dsimp only [y]; ring
      _ = alpha - (alpha.im : ℂ) * Complex.I := by rw [hy]
      _ = ((alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I) -
          (alpha.im : ℂ) * Complex.I := by
            congr 1
            exact hdecomp.symm
      _ = (alpha.re : ℂ) := by ring
  have hyU : y ∈ U := hballU hyDist
  have hyComp : y ∈ ({alpha} : Set ℂ)ᶜ := by simpa using hyne
  exact (hU ⟨hyU, hyComp⟩) hyZero

/-- **Multiplicity-exact nonlinear Hawking divisor transport.** Every centered Xi zero determines a
physical timelike theta-mirror tilt. At every sufficiently small real background coupling, the
exact nonlinear susceptibility retains precisely the same total local zero multiplicity, although
the individual complex-frequency resonances may move. -/
theorem exists_thetaCuspHawkingNonlinearCarrier_divisorTransport
    (alpha : ℂ) (halpha : XiC alpha = 0) :
    ∃ delta > 0, ∃ eta > 0,
      |alpha.im| < 1 ∧ eta ≤ 1 ∧
      ∀ t : ℝ, |t| < eta →
        ∃ Z : Finset ℂ,
          (∀ rho ∈ Z, rho ∈ Metric.ball (alpha.re : ℂ) delta) ∧
          (∀ z ∈ Metric.ball (alpha.re : ℂ) delta,
            thetaCuspHawkingNonlinearCarrier alpha.im t z = 0 ↔ z ∈ Z) ∧
          (∑ rho ∈ Z,
              GaloisForLFunctions.HTGeometry.zeroMult
                (thetaCuspHawkingNonlinearCarrier alpha.im t) rho) =
            GaloisForLFunctions.HTGeometry.zeroMult XiC alpha := by
  have ha : |alpha.im| < 1 := abs_im_lt_one_of_XiC_eq_zero halpha
  obtain ⟨delta, hdelta, honly⟩ :=
    exists_thetaCuspHawkingNonlinearCarrier_isolatingRadius alpha
  have hdecomp : (alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I = alpha :=
    Complex.re_add_im alpha
  have hcenter :
      thetaCuspHawkingNonlinearCarrier alpha.im 0 (alpha.re : ℂ) = 0 := by
    rw [thetaCuspHawkingNonlinearCarrier_zero_eq_XiC, hdecomp, halpha, mul_zero]
  obtain ⟨epsilon, hepsilon, hstable⟩ :=
    GaloisForLFunctions.HTGeometry.exists_local_zeroSet
      (U := Set.univ) isOpen_univ
      (f := thetaCuspHawkingNonlinearCarrier alpha.im 0)
      (thetaCuspHawkingNonlinearCarrier_differentiable
        alpha.im 0).differentiableOn
      hdelta (by simp) hcenter honly
  let M := thetaCuspHawkingNonlinearSourceBound alpha.im ha
  let C := Real.exp M * M
  let L := ∫ x : ℝ,
    Real.exp ((2 * delta + |alpha.im|) * |x|) * thetaCuspFullSource x
  let K := C * L
  have hM : 0 ≤ M :=
    (thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound alpha.im ha 0).1.trans
      (thetaCuspTiltedSource_mem_Icc_nonlinearSourceBound alpha.im ha 0).2
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le hM
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact integral_nonneg fun x =>
      mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos x).le
  have hK : 0 ≤ K := mul_nonneg hC hL
  let eta := min 1 (epsilon / (K + 1))
  have hKone : 0 < K + 1 := by linarith
  have heta : 0 < eta := by
    exact lt_min one_pos (div_pos hepsilon hKone)
  have hetaOne : eta ≤ 1 := min_le_left _ _
  refine ⟨delta, hdelta, eta, heta, ha, hetaOne, ?_⟩
  intro t ht
  have htOne : |t| ≤ 1 := (ht.trans_le hetaOne).le
  have htDiv : |t| < epsilon / (K + 1) :=
    ht.trans_le (min_le_right _ _)
  have htK : |t| * K < epsilon := by
    by_cases hKzero : K = 0
    · simp [hKzero, hepsilon]
    · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
      have hfracPos : 0 < epsilon / (K + 1) := div_pos hepsilon hKone
      calc
        |t| * K < (epsilon / (K + 1)) * K :=
          mul_lt_mul_of_pos_right htDiv hKpos
        _ < (epsilon / (K + 1)) * (K + 1) := by
          gcongr
          linarith
        _ = epsilon := by field_simp
  have hclose : ∀ z ∈ Metric.closedBall (alpha.re : ℂ) (2 * delta),
      ‖thetaCuspHawkingNonlinearCarrier alpha.im t z -
        thetaCuspHawkingNonlinearCarrier alpha.im 0 z‖ ≤ epsilon := by
    intro z hz
    have hbound := norm_thetaCuspHawkingNonlinearCarrier_sub_zero_le
      alpha.im t alpha.re (2 * delta) ha htOne z hz
    have hbound' :
        ‖thetaCuspHawkingNonlinearCarrier alpha.im t z -
          thetaCuspHawkingNonlinearCarrier alpha.im 0 z‖ ≤ |t| * K := by
      calc
        ‖thetaCuspHawkingNonlinearCarrier alpha.im t z -
            thetaCuspHawkingNonlinearCarrier alpha.im 0 z‖ ≤
          |t| * (Real.exp
              (thetaCuspHawkingNonlinearSourceBound alpha.im ha) *
              thetaCuspHawkingNonlinearSourceBound alpha.im ha) *
            ∫ x : ℝ, Real.exp ((2 * delta + |alpha.im|) * |x|) *
              thetaCuspFullSource x := hbound
        _ = |t| * K := by dsimp only [K, C, L, M]; ring
    exact hbound'.trans htK.le
  obtain ⟨Z, hZmem, hZzero, hZmult⟩ :=
    hstable (thetaCuspHawkingNonlinearCarrier alpha.im t)
      (thetaCuspHawkingNonlinearCarrier_differentiable
        alpha.im t).differentiableOn hclose
  refine ⟨Z, hZmem, hZzero, ?_⟩
  calc
    (∑ rho ∈ Z,
        GaloisForLFunctions.HTGeometry.zeroMult
          (thetaCuspHawkingNonlinearCarrier alpha.im t) rho) =
      GaloisForLFunctions.HTGeometry.zeroMult
        (thetaCuspHawkingNonlinearCarrier alpha.im 0) (alpha.re : ℂ) := hZmult
    _ = GaloisForLFunctions.HTGeometry.zeroMult XiC
        ((alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I) :=
      zeroMult_thetaCuspHawkingNonlinearCarrier_zero alpha.im alpha.re
    _ = GaloisForLFunctions.HTGeometry.zeroMult XiC alpha := by rw [hdecomp]

/-- On physical real frequency, the continued carrier is exactly the coupling derivative of the
full Davies--Fulling eikonal response. -/
theorem thetaCuspHawkingNonlinearCarrier_ofReal_eq_exactEikonalDerivative
    (a t total : ℝ) (ha : |a| < 1) :
    thetaCuspHawkingNonlinearCarrier a t (total : ℂ) =
      thetaCuspHawkingEikonalCouplingDerivativeEntire a total (t : ℂ) := by
  rw [thetaCuspHawkingEikonalCouplingDerivativeEntire_ofReal a ha total t,
    thetaCuspHawkingFullMirrorCouplingJetIntegral_eq_integral,
    thetaCuspHawkingNonlinearCarrier]
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaCuspHawkingNonlinearCarrierIntegrand]
  push_cast
  ring_nf

end RHTower
