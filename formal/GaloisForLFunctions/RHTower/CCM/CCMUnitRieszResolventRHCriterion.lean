import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszLogLatticeHandoff
import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeAbelCompleteness

/-!
# Unit-Riesz resolvent criterion for RH

This module closes the analytic handoff from the literal CCM unit-Riesz source to the critical
divisor frontier. A bounded Chebyshev resolvent has a Laplace transform on the right half-plane.
An absolutely-continuous integration-by-parts argument, valid across the prime-power staircase,
identifies its real-axis transform with the continuous Chebyshev divisor current. The identity
theorem then manufactures the regularized critical-Mellin continuation required by the existing
Xi-divisor tomography endpoint.

Consequently a uniform integer-log resolvent bound, and in particular domination of every literal
completed outgoing HG block by the pole packet, implies the Riemann hypothesis. No PNT estimate,
zero-free region, RH premise, or differentiability assumption at prime-power jumps is used.
-/

open Set MeasureTheory Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def criticalMellinChebyshevRayDensity (h : ℝ) : ℝ :=
  Real.exp h * criticalMellinNormalizedChebyshevError h

theorem measurable_criticalMellinChebyshevRayDensity :
    Measurable criticalMellinChebyshevRayDensity := by
  exact Real.measurable_exp.mul measurable_criticalMellinNormalizedChebyshevError

private theorem abs_criticalMellinChebyshevRayDensity_le_exp
    (h : ℝ) :
    |criticalMellinChebyshevRayDensity h| ≤
      (Real.log 4 + 5) * Real.exp (3 * h / 2) := by
  have hpsi0 : 0 ≤ Chebyshev.psi (Real.exp h) := Chebyshev.psi_nonneg _
  have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_pos h).le
  have herr : |Chebyshev.psi (Real.exp h) - Real.exp h| ≤
      (Real.log 4 + 5) * Real.exp h := by
    calc
      |Chebyshev.psi (Real.exp h) - Real.exp h| ≤
          |Chebyshev.psi (Real.exp h)| + |Real.exp h| := abs_sub _ _
      _ = Chebyshev.psi (Real.exp h) + Real.exp h := by
        rw [abs_of_nonneg hpsi0, abs_of_pos (Real.exp_pos h)]
      _ ≤ (Real.log 4 + 4) * Real.exp h + Real.exp h := by gcongr
      _ = (Real.log 4 + 5) * Real.exp h := by ring
  rw [criticalMellinChebyshevRayDensity,
    criticalMellinNormalizedChebyshevError_eq_apertureError,
    criticalMellinChebyshevError_eq_exp, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos h), abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp h * (|Chebyshev.psi (Real.exp h) - Real.exp h| * Real.exp (-h / 2)) ≤
        Real.exp h * (((Real.log 4 + 5) * Real.exp h) * Real.exp (-h / 2)) := by
      gcongr
    _ = (Real.log 4 + 5) *
        (Real.exp h * Real.exp h * Real.exp (-h / 2)) := by ring
    _ = (Real.log 4 + 5) * Real.exp (3 * h / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem intervalIntegrable_criticalMellinChebyshevRayDensity (a b : ℝ) :
    IntervalIntegrable criticalMellinChebyshevRayDensity volume a b := by
  have hforward : ∀ {a b : ℝ}, a ≤ b →
      IntervalIntegrable criticalMellinChebyshevRayDensity volume a b := by
    intro a b hab
    refine GaloisForLFunctions.RHTower.intervalIntegrable_of_bound_on
      measurable_criticalMellinChebyshevRayDensity (C :=
        (Real.log 4 + 5) * Real.exp (3 * b / 2)) hab ?_
    intro h hh
    calc
      |criticalMellinChebyshevRayDensity h| ≤
          (Real.log 4 + 5) * Real.exp (3 * h / 2) :=
        abs_criticalMellinChebyshevRayDensity_le_exp h
      _ ≤ (Real.log 4 + 5) * Real.exp (3 * b / 2) := by
        have hc : 0 ≤ Real.log 4 + 5 := by positivity
        gcongr
        linarith [hh.2]
  rcases le_total a b with hab | hba
  · exact hforward hab
  · exact (hforward hba).symm

theorem continuous_unitRieszChebyshevRayIntegral :
    Continuous unitRieszChebyshevRayIntegral := by
  change Continuous (fun t : ℝ => ∫ h in (0 : ℝ)..t,
    criticalMellinChebyshevRayDensity h)
  exact intervalIntegral.continuous_primitive
    intervalIntegrable_criticalMellinChebyshevRayDensity 0

def criticalMellinChebyshevResolventRayRepresentative (t : ℝ) : ℝ :=
  Real.exp (-max 0 t) *
    (unitRieszChebyshevRayIntegral (max 0 t) - 2 / 3)

theorem continuous_criticalMellinChebyshevResolventRayRepresentative :
    Continuous criticalMellinChebyshevResolventRayRepresentative := by
  unfold criticalMellinChebyshevResolventRayRepresentative
  have hm : Continuous (fun t : ℝ => max 0 t) :=
    continuous_const.max continuous_id
  have he : Continuous (fun t : ℝ => Real.exp (-max 0 t)) :=
    Real.continuous_exp.comp hm.neg
  have hi : Continuous (fun t : ℝ =>
      unitRieszChebyshevRayIntegral (max 0 t) - 2 / 3) :=
    (continuous_unitRieszChebyshevRayIntegral.comp hm).sub continuous_const
  exact he.mul hi

theorem criticalMellinChebyshevResolventRayRepresentative_eq
    {t : ℝ} (ht : 0 ≤ t) :
    criticalMellinChebyshevResolventRayRepresentative t =
      criticalMellinChebyshevResolventSource t := by
  rw [criticalMellinChebyshevResolventRayRepresentative, max_eq_right ht]
  have h := unitRieszChebyshevRayIntegral_eq_fullResolvent ht
  rw [h]
  have he : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [show Real.exp (-t) *
      (Real.exp t * criticalMellinChebyshevResolventSource t + 2 / 3 - 2 / 3) =
      (Real.exp (-t) * Real.exp t) * criticalMellinChebyshevResolventSource t by ring,
    he, one_mul]

def criticalMellinChebyshevResolventLaplace (z : ℂ) : ℂ :=
  ccmAbelLaplaceTail criticalMellinChebyshevResolventRayRepresentative 0 z

theorem criticalMellinChebyshevResolventLaplace_eq_shiftedTail (z : ℂ) :
    criticalMellinChebyshevResolventLaplace z =
      Complex.exp z * ccmAbelLaplaceTail
        (fun h => criticalMellinChebyshevResolventRayRepresentative (h - 1)) 1 z := by
  let f : ℝ → ℂ := fun h =>
    Complex.exp (-z * (h : ℂ)) *
      (criticalMellinChebyshevResolventRayRepresentative (h - 1) : ℂ)
  have htrans := integral_Ioi_translate 1 f
  rw [criticalMellinChebyshevResolventLaplace, ccmAbelLaplaceTail,
    ccmAbelLaplaceTail]
  change (∫ u in Ioi (0 : ℝ),
      Complex.exp (-z * (u : ℂ)) *
        (criticalMellinChebyshevResolventRayRepresentative u : ℂ)) = _
  change (∫ u in Ioi (0 : ℝ), f (1 + u)) = ∫ h in Ioi (1 : ℝ), f h at htrans
  have hfactor : (∫ u in Ioi (0 : ℝ), f (1 + u)) =
      Complex.exp (-z) *
        ∫ u in Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) *
          (criticalMellinChebyshevResolventRayRepresentative u : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only [f]
    have harg : -z * ((1 + u : ℝ) : ℂ) = -z + (-z * (u : ℂ)) := by
      push_cast
      ring
    rw [harg, Complex.exp_add]
    simp only [add_sub_cancel_left]
    ring
  have hexp : Complex.exp z * Complex.exp (-z) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    (∫ u in Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) *
        (criticalMellinChebyshevResolventRayRepresentative u : ℂ)) =
        Complex.exp z * (Complex.exp (-z) *
          ∫ u in Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) *
            (criticalMellinChebyshevResolventRayRepresentative u : ℂ)) := by
          rw [← mul_assoc, hexp, one_mul]
    _ = Complex.exp z * (∫ u in Ioi (0 : ℝ), f (1 + u)) := by rw [hfactor]
    _ = Complex.exp z * (∫ h in Ioi (1 : ℝ), f h) := by rw [htrans]

theorem analyticOnNhd_criticalMellinChebyshevResolventLaplace_of_bounded
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B) :
    AnalyticOnNhd ℂ criticalMellinChebyshevResolventLaplace {z : ℂ | 0 < z.re} := by
  let q : ℝ → ℝ := fun h => criticalMellinChebyshevResolventRayRepresentative (h - 1)
  have hq : Measurable q :=
    continuous_criticalMellinChebyshevResolventRayRepresentative.measurable.comp
      (by fun_prop)
  have hqB : ∀ h : ℝ, 1 < h → |q h| ≤ B := by
    intro h hh
    dsimp only [q]
    rw [criticalMellinChebyshevResolventRayRepresentative_eq (by linarith)]
    exact hB (h - 1) (by linarith)
  have htail := analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    hq (show (0 : ℝ) < 1 by norm_num) hB0 hqB
  rw [show criticalMellinChebyshevResolventLaplace =
      fun z => Complex.exp z * ccmAbelLaplaceTail q 1 z by
    funext z
    exact criticalMellinChebyshevResolventLaplace_eq_shiftedTail z]
  intro z hz
  exact analyticAt_id.cexp.mul (htail z hz)

theorem abs_unitRieszChebyshevRayIntegral_le_of_resolvent_bounded
    {B : ℝ}
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszChebyshevRayIntegral t| ≤ Real.exp t * B + 2 / 3 := by
  rw [unitRieszChebyshevRayIntegral_eq_fullResolvent ht]
  calc
    |Real.exp t * criticalMellinChebyshevResolventSource t + 2 / 3| ≤
        |Real.exp t * criticalMellinChebyshevResolventSource t| + |2 / 3| :=
      abs_add_le _ _
    _ = Real.exp t * |criticalMellinChebyshevResolventSource t| + 2 / 3 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos t)]
      norm_num
    _ ≤ Real.exp t * B + 2 / 3 := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (hB t ht) (Real.exp_pos t).le) _

theorem integrableOn_exp_mul_criticalMellinChebyshevRayDensity
    {r : ℝ} (hr : 1 / 2 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-(r + 1) * t) *
      criticalMellinChebyshevRayDensity t) (Ioi 0) := by
  let C : ℝ := Real.log 4 + 5
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hmajor : IntegrableOn
      (fun t : ℝ => C * Real.exp ((1 / 2 - r) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show 1 / 2 - r < 0 by linarith) 0).const_mul C
  refine hmajor.mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      measurable_criticalMellinChebyshevRayDensity).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(r + 1) * t) * |criticalMellinChebyshevRayDensity t| ≤
        Real.exp (-(r + 1) * t) *
          (C * Real.exp (3 * t / 2)) := by
      gcongr
      exact abs_criticalMellinChebyshevRayDensity_le_exp t
    _ = C * Real.exp ((1 / 2 - r) * t) := by
      rw [show Real.exp (-(r + 1) * t) *
          (C * Real.exp (3 * t / 2)) =
          C * (Real.exp (-(r + 1) * t) * Real.exp (3 * t / 2)) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem integrableOn_exp_mul_unitRieszChebyshevRayIntegral_of_bounded
    {B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) (Ioi 0) := by
  let M : ℝ → ℝ := fun t =>
    B * Real.exp (-r * t) + (2 / 3) * Real.exp (-(r + 1) * t)
  have hfirst : IntegrableOn (fun t : ℝ => B * Real.exp (-r * t)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show -r < 0 by linarith) 0).const_mul B
  have hsecond : IntegrableOn
      (fun t : ℝ => (2 / 3) * Real.exp (-(r + 1) * t)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0).const_mul (2 / 3)
  have hmajor : IntegrableOn M (Ioi 0) := hfirst.add hsecond
  refine hmajor.mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      continuous_unitRieszChebyshevRayIntegral.measurable).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(r + 1) * t) * |unitRieszChebyshevRayIntegral t| ≤
        Real.exp (-(r + 1) * t) * (Real.exp t * B + 2 / 3) := by
      gcongr
      exact abs_unitRieszChebyshevRayIntegral_le_of_resolvent_bounded hB ht0
    _ = M t := by
      dsimp only [M]
      rw [mul_add]
      have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
          Real.exp (-r * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-(r + 1) * t) * (Real.exp t * B) +
            Real.exp (-(r + 1) * t) * (2 / 3) =
            (Real.exp (-(r + 1) * t) * Real.exp t) * B +
              Real.exp (-(r + 1) * t) * (2 / 3) := by ring
        _ = B * Real.exp (-r * t) +
            (2 / 3) * Real.exp (-(r + 1) * t) := by rw [hcollapse]; ring

theorem tendsto_exp_mul_unitRieszChebyshevRayIntegral_atTop_of_bounded
    {B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 0 < r) :
    Tendsto (fun t : ℝ => Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) atTop (nhds 0) := by
  have hdecayR : Tendsto (fun t : ℝ => Real.exp (-r * t)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (show -r < 0 by linarith) tendsto_id)
  have hdecayA : Tendsto (fun t : ℝ => Real.exp (-(r + 1) * t)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (show -(r + 1) < 0 by linarith) tendsto_id)
  have hmajor : Tendsto (fun t : ℝ =>
      B * Real.exp (-r * t) + (2 / 3) * Real.exp (-(r + 1) * t))
      atTop (nhds 0) := by
    simpa using (hdecayR.const_mul B).add (hdecayA.const_mul (2 / 3))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(r + 1) * t) * |unitRieszChebyshevRayIntegral t| ≤
        Real.exp (-(r + 1) * t) * (Real.exp t * B + 2 / 3) := by
      gcongr
      exact abs_unitRieszChebyshevRayIntegral_le_of_resolvent_bounded hB ht
    _ = B * Real.exp (-r * t) + (2 / 3) * Real.exp (-(r + 1) * t) := by
      rw [mul_add]
      have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
          Real.exp (-r * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-(r + 1) * t) * (Real.exp t * B) +
            Real.exp (-(r + 1) * t) * (2 / 3) =
            (Real.exp (-(r + 1) * t) * Real.exp t) * B +
              Real.exp (-(r + 1) * t) * (2 / 3) := by ring
        _ = B * Real.exp (-r * t) +
            (2 / 3) * Real.exp (-(r + 1) * t) := by rw [hcollapse]; ring

theorem intervalIntegral_exp_mul_criticalMellinChebyshevRayDensity_eq
    {r T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(r + 1) * t) *
      criticalMellinChebyshevRayDensity t) =
      Real.exp (-(r + 1) * T) * unitRieszChebyshevRayIntegral T +
        (r + 1) * (∫ t in (0 : ℝ)..T,
          Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t) := by
  let E : ℝ → ℝ := fun t => Real.exp (-(r + 1) * t)
  let P : ℝ → ℝ := unitRieszChebyshevRayIntegral
  have hint : IntervalIntegrable criticalMellinChebyshevRayDensity volume 0 T :=
    intervalIntegrable_criticalMellinChebyshevRayDensity 0 T
  have hPac : AbsolutelyContinuousOnInterval P 0 T := by
    exact hint.absolutelyContinuousOnInterval_intervalIntegral
      (show (0 : ℝ) ∈ uIcc 0 T by simp [hT])
  have hEcd : ContDiff ℝ 1 E := by
    dsimp only [E]
    fun_prop
  have hEac : AbsolutelyContinuousOnInterval E 0 T :=
    hEcd.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hEac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in (0 : ℝ)..T, E t * deriv P t) =
      ∫ t in (0 : ℝ)..T,
        E t * criticalMellinChebyshevRayDensity t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hint.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (criticalMellinChebyshevRayDensity t) t := by
      exact ht (uIoc_subset_uIcc hmem) 0 (by simp [hT])
    rw [hd.deriv]
  have hright : (∫ t in (0 : ℝ)..T, deriv E t * P t) =
      ∫ t in (0 : ℝ)..T,
        (-(r + 1) * E t) * P t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hd : HasDerivAt E (-(r + 1) * E t) t := by
      dsimp only [E]
      exact (((hasDerivAt_id t).const_mul (-(r + 1))).exp).congr_deriv (by
        simp only [id_eq]
        ring)
    change deriv E t * P t = (-(r + 1) * E t) * P t
    rw [hd.deriv]
  have hP0 : P 0 = 0 := by
    simp [P, unitRieszChebyshevRayIntegral]
  rw [hleft, hright, hP0, mul_zero, sub_zero] at hibp
  dsimp only [E, P] at hibp ⊢
  rw [hibp, sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  calc
    (∫ t in (0 : ℝ)..T,
        -(-(r + 1) * Real.exp (-(r + 1) * t) *
          unitRieszChebyshevRayIntegral t)) =
      ∫ t in (0 : ℝ)..T,
        (r + 1) * (Real.exp (-(r + 1) * t) *
          unitRieszChebyshevRayIntegral t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
    _ = (r + 1) * (∫ t in (0 : ℝ)..T,
        Real.exp (-(r + 1) * t) *
          unitRieszChebyshevRayIntegral t) := by
      rw [intervalIntegral.integral_const_mul]

theorem integral_Ioi_exp_mul_criticalMellinChebyshevRayDensity_eq
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 1 / 2 < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r + 1) * t) *
      criticalMellinChebyshevRayDensity t) =
      (r + 1) * (∫ t in Ioi (0 : ℝ),
        Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t) := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hleft := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_exp_mul_criticalMellinChebyshevRayDensity hr) tendsto_id
  have hright0 := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ)
    (integrableOn_exp_mul_unitRieszChebyshevRayIntegral_of_bounded hB0 hB hr0) tendsto_id
  have hright : Tendsto (fun T : ℝ =>
      Real.exp (-(r + 1) * T) * unitRieszChebyshevRayIntegral T +
        (r + 1) * (∫ t in (0 : ℝ)..T,
          Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t))
      atTop (nhds ((r + 1) * (∫ t in Ioi (0 : ℝ),
        Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t))) := by
    have hterminal :=
      tendsto_exp_mul_unitRieszChebyshevRayIntegral_atTop_of_bounded hB0 hB hr0
    simpa only [id_eq, zero_add] using hterminal.add (hright0.const_mul (r + 1))
  have heq : (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      Real.exp (-(r + 1) * t) * criticalMellinChebyshevRayDensity t) =ᶠ[atTop]
      (fun T : ℝ =>
        Real.exp (-(r + 1) * T) * unitRieszChebyshevRayIntegral T +
          (r + 1) * (∫ t in (0 : ℝ)..T,
            Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact intervalIntegral_exp_mul_criticalMellinChebyshevRayDensity_eq hT
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem integrableOn_exp_mul_criticalMellinChebyshevResolventRayRepresentative_of_bounded
    {B r : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-r * t) *
      criticalMellinChebyshevResolventRayRepresentative t) (Ioi 0) := by
  have hmajor : IntegrableOn (fun t : ℝ => B * Real.exp (-r * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -r < 0 by linarith) 0).const_mul B
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-r * t) *
      criticalMellinChebyshevResolventRayRepresentative t)
      (volume.restrict (Ioi 0)) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      continuous_criticalMellinChebyshevResolventRayRepresentative.measurable)
      |>.aestronglyMeasurable.restrict
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-r * t) *
        |criticalMellinChebyshevResolventRayRepresentative t| =
        Real.exp (-r * t) *
          |criticalMellinChebyshevResolventSource t| := by
      rw [criticalMellinChebyshevResolventRayRepresentative_eq ht.le]
    _ ≤ Real.exp (-r * t) * B := by
      gcongr
      exact hB t ht.le
    _ = B * Real.exp (-r * t) := by ring

theorem integral_Ioi_exp_mul_unitRieszChebyshevRayIntegral_eq_resolvent
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r + 1) * t) *
      unitRieszChebyshevRayIntegral t) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinChebyshevResolventRayRepresentative t) +
        (2 / 3) / (r + 1) := by
  have hR :=
    integrableOn_exp_mul_criticalMellinChebyshevResolventRayRepresentative_of_bounded
      hB0 hB hr
  have hA : IntegrableOn (fun t : ℝ =>
      (2 / 3) * Real.exp (-(r + 1) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0).const_mul (2 / 3)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(r + 1) * t) * unitRieszChebyshevRayIntegral t =
        Real.exp (-r * t) *
          criticalMellinChebyshevResolventRayRepresentative t +
            (2 / 3) * Real.exp (-(r + 1) * t) := by
    intro t ht
    rw [unitRieszChebyshevRayIntegral_eq_fullResolvent ht.le,
      criticalMellinChebyshevResolventRayRepresentative_eq ht.le]
    have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
        Real.exp (-r * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_add]
    calc
      Real.exp (-(r + 1) * t) *
            (Real.exp t * criticalMellinChebyshevResolventSource t) +
          Real.exp (-(r + 1) * t) * (2 / 3) =
          (Real.exp (-(r + 1) * t) * Real.exp t) *
              criticalMellinChebyshevResolventSource t +
            (2 / 3) * Real.exp (-(r + 1) * t) := by ring
      _ = _ := by rw [hcollapse]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_add hR hA,
    MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (show -(r + 1) < 0 by linarith) 0]
  have hr1 : r + 1 ≠ 0 := by linarith
  rw [show Real.exp (-(r + 1) * 0) = 1 by simp]
  rw [show -(1 : ℝ) / -(r + 1) = 1 / (r + 1) by field_simp [hr1]]
  simp only [div_eq_mul_inv, one_mul]

theorem integral_Ioi_exp_mul_criticalMellinNormalizedChebyshevError_eq_resolvent
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 1 / 2 < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
      criticalMellinNormalizedChebyshevError t) =
      (r + 1) * (∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinChebyshevResolventRayRepresentative t) + 2 / 3 := by
  have hprim := integral_Ioi_exp_mul_criticalMellinChebyshevRayDensity_eq
    hB0 hB hr
  have hres := integral_Ioi_exp_mul_unitRieszChebyshevRayIntegral_eq_resolvent
    hB0 hB (lt_trans (by norm_num) hr)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(r + 1) * t) * criticalMellinChebyshevRayDensity t =
        Real.exp (-r * t) * criticalMellinNormalizedChebyshevError t := by
    intro t ht
    rw [criticalMellinChebyshevRayDensity]
    have hcollapse : Real.exp (-(r + 1) * t) * Real.exp t =
        Real.exp (-r * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show Real.exp (-(r + 1) * t) *
        (Real.exp t * criticalMellinNormalizedChebyshevError t) =
        (Real.exp (-(r + 1) * t) * Real.exp t) *
          criticalMellinNormalizedChebyshevError t by ring,
      hcollapse]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, hres] at hprim
  have hr1 : r + 1 ≠ 0 := by linarith
  field_simp [hr1] at hprim ⊢
  linarith

theorem criticalNormalizedChebyshevErrorLaplace_ofReal
    (r : ℝ) :
    criticalNormalizedChebyshevErrorLaplace (r : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinNormalizedChebyshevError t : ℝ) : ℂ) := by
  rw [criticalNormalizedChebyshevErrorLaplace]
  calc
    (∫ t in Ioi (0 : ℝ), Complex.exp (-((r : ℂ) * (t : ℂ))) *
        (criticalMellinNormalizedChebyshevError t : ℂ)) =
      ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-r * t) * criticalMellinNormalizedChebyshevError t : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have hexp : Complex.exp (-((r : ℂ) * (t : ℂ))) =
            (Real.exp (-r * t) : ℂ) := by
          calc
            Complex.exp (-((r : ℂ) * (t : ℂ))) =
                Complex.exp ((-r * t : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
            _ = (Real.exp (-r * t) : ℂ) := (ofReal_exp _).symm
        change Complex.exp (-((r : ℂ) * (t : ℂ))) *
            (criticalMellinNormalizedChebyshevError t : ℂ) =
          ((Real.exp (-r * t) * criticalMellinNormalizedChebyshevError t : ℝ) : ℂ)
        rw [hexp, ofReal_mul]
    _ = _ := integral_complex_ofReal

theorem criticalMellinChebyshevResolventLaplace_ofReal
    (r : ℝ) :
    criticalMellinChebyshevResolventLaplace (r : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-r * t) *
        criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ) := by
  rw [criticalMellinChebyshevResolventLaplace, ccmAbelLaplaceTail]
  calc
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(r : ℂ) * (t : ℂ)) *
        (criticalMellinChebyshevResolventRayRepresentative t : ℂ)) =
      ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-r * t) *
          criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have hexp : Complex.exp (-(r : ℂ) * (t : ℂ)) =
            (Real.exp (-r * t) : ℂ) := by
          calc
            Complex.exp (-(r : ℂ) * (t : ℂ)) =
                Complex.exp ((-r * t : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
            _ = (Real.exp (-r * t) : ℂ) := (ofReal_exp _).symm
        change Complex.exp (-(r : ℂ) * (t : ℂ)) *
            (criticalMellinChebyshevResolventRayRepresentative t : ℂ) =
          ((Real.exp (-r * t) *
            criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)
        rw [hexp, ofReal_mul]
    _ = _ := integral_complex_ofReal

theorem criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real_of_bounded
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 1 / 2 < r) :
    criticalNormalizedChebyshevErrorLaplace (r : ℂ) =
      ((r : ℂ) + 1) * criticalMellinChebyshevResolventLaplace (r : ℂ) + 2 / 3 := by
  rw [criticalNormalizedChebyshevErrorLaplace_ofReal,
    criticalMellinChebyshevResolventLaplace_ofReal]
  have hreal :=
    integral_Ioi_exp_mul_criticalMellinNormalizedChebyshevError_eq_resolvent
      hB0 hB hr
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat] using hc

/-- Holomorphic candidate for the regularized critical-Mellin defect manufactured from the
bounded unit-Riesz resolvent. -/
def criticalMellinChebyshevResolventDefectExtension (u : ℂ) : ℂ :=
  1 / (u + 1) - 1 -
    (u + 1) * (((u + 3 / 2) *
      criticalMellinChebyshevResolventLaplace (u + 1 / 2)) + 2 / 3)

theorem analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_bounded
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B) :
    AnalyticOnNhd ℂ criticalMellinChebyshevResolventDefectExtension
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
  have hL := analyticOnNhd_criticalMellinChebyshevResolventLaplace_of_bounded
    hB0 hB
  intro u hu
  change -1 / 2 < u.re at hu
  have hz : 0 < (u + 1 / 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) u := by fun_prop
  have hLcomp : AnalyticAt ℂ
      (fun z : ℂ => criticalMellinChebyshevResolventLaplace (z + 1 / 2)) u :=
    AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
      (hL (u + 1 / 2) hz) hshift
  have hden : u + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  change AnalyticAt ℂ (fun z : ℂ =>
    1 / (z + 1) - 1 -
      (z + 1) * (((z + 3 / 2) *
        criticalMellinChebyshevResolventLaplace (z + 1 / 2)) + 2 / 3)) u
  exact ((analyticAt_const.div (analyticAt_id.add analyticAt_const) hden).sub
      analyticAt_const).sub
    ((analyticAt_id.add analyticAt_const).mul
      (((analyticAt_id.add analyticAt_const).mul hLcomp).add analyticAt_const))

theorem criticalMellinChebyshevResolventDefectExtension_eq_regularized_on_real_of_bounded
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B)
    (hr : 0 < r) :
    criticalMellinChebyshevResolventDefectExtension (r : ℂ) =
      regularizedCriticalMellinDefect (r : ℂ) := by
  let z : ℂ := ((r + 1 / 2 : ℝ) : ℂ)
  have hz : 1 / 2 < r + 1 / 2 := by linarith
  have hLap :=
    criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real_of_bounded
      hB0 hB hz
  have hzre : 1 / 2 < z.re := by
    dsimp only [z]
    norm_num
    linarith
  have hC50 := criticalNormalizedChebyshevErrorLaplace_eq_logDeriv hzre
  have hmain :
      (((r : ℂ) + 3 / 2) *
          criticalMellinChebyshevResolventLaplace ((r : ℂ) + 1 / 2) + 2 / 3) =
        -(logDeriv zetaResidueUnit ((r : ℂ) + 1) + 1) / ((r : ℂ) + 1) := by
    rw [hLap] at hC50
    dsimp only [z] at hC50
    push_cast at hC50
    convert hC50 using 1 <;> ring
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by
    funext s
    rfl
  have hden : (r : ℂ) + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num
    linarith
  have hsolve :
      -((r : ℂ) + 1) *
          (((r : ℂ) + 3 / 2) *
            criticalMellinChebyshevResolventLaplace ((r : ℂ) + 1 / 2) + 2 / 3) - 1 =
        logDeriv zetaResidueUnit ((r : ℂ) + 1) := by
    rw [hmain]
    field_simp [hden]
    ring
  rw [criticalMellinChebyshevResolventDefectExtension,
    regularizedCriticalMellinDefect, ← hfun, ← hsolve]
  ring

theorem criticalMellinChebyshevResolventDefectExtension_eq_regularized_of_bounded
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B) :
    ∀ u : ℂ, 0 < u.re →
      criticalMellinChebyshevResolventDefectExtension u =
        regularizedCriticalMellinDefect u := by
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAfull :=
    analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_bounded hB0 hB
  have hA : AnalyticOnNhd ℂ criticalMellinChebyshevResolventDefectExtension U :=
    hAfull.mono (by
      intro u hu
      change 0 < u.re at hu
      change -1 / 2 < u.re
      linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have htwo : (2 : ℂ) ∈ U := by
    change 0 < (2 : ℂ).re
    norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ))
      (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ))
          (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      criticalMellinChebyshevResolventDefectExtension z =
        regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact criticalMellinChebyshevResolventDefectExtension_eq_regularized_on_real_of_bounded
      hB0 hB (lt_trans (by norm_num) hr)
  have heq := hA.eqOn_of_preconnected_of_frequently_eq hR
    (convex_halfSpace_re_gt 0).isPreconnected htwo hfreq
  intro u hu
  exact heq hu

/-- A globally bounded unit-Riesz / CCM Chebyshev resolvent closes the critical divisor
continuation and hence proves RH. -/
theorem riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_regularizedCriticalMellinDefect_extension
    criticalMellinChebyshevResolventDefectExtension
    (analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_bounded hB0 hB)
    (criticalMellinChebyshevResolventDefectExtension_eq_regularized_of_bounded hB0 hB)

theorem exists_global_bound_criticalMellinChebyshevResolventSource_of_log_nat_bound
    {B₀ : ℝ}
    (hlog : ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤ B₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤ B := by
  have hB₀ : 0 ≤ B₀ :=
    (abs_nonneg (criticalMellinChebyshevResolventSource (Real.log 2))).trans
      (hlog 2 (by norm_num))
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    continuous_criticalMellinChebyshevResolventRayRepresentative.norm.continuousOn
  let B : ℝ := max C (B₀ + (Real.log 4 + 5))
  refine ⟨B, ?_, ?_⟩
  · exact (add_nonneg hB₀ (by positivity)).trans (le_max_right _ _)
  · intro t ht
    by_cases hhead : t ≤ Real.log 2
    · have hcompact := hC (mem_image_of_mem
        (fun u : ℝ => ‖criticalMellinChebyshevResolventRayRepresentative u‖)
        (show t ∈ Icc (0 : ℝ) (Real.log 2) from ⟨ht, hhead⟩))
      rw [Real.norm_eq_abs,
        criticalMellinChebyshevResolventRayRepresentative_eq ht] at hcompact
      exact hcompact.trans (le_max_left _ _)
    · have htail := abs_criticalMellinChebyshevResolventSource_le_of_log_nat_bound
        hlog (le_of_not_ge hhead)
      exact htail.trans (le_max_right _ _)

/-- Uniform control at integer logarithmic apertures already forces RH; no information is lost
between consecutive integer apertures. -/
theorem riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound
    {B₀ : ℝ}
    (hlog : ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤ B₀) :
    RiemannHypothesis := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_global_bound_criticalMellinChebyshevResolventSource_of_log_nat_bound hlog
  exact riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource hB0 hB

/-- Exact CCM-HG endpoint: domination of every literal completed outgoing integer block by the
pole packet implies RH. -/
theorem riemannHypothesis_of_unitRieszCoherentCompletedOutgoingProfile_le_pole
    (hdom : ∀ N : ℕ, 2 ≤ N → ∀ u : ℝ, 0 < u →
      boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u ≤
        boundaryRelativeTrace polePacketProfile u) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound
    (B₀ := 4)
  intro N hN
  have hsquare :=
    (unitRieszCoherentCompletedOutgoingProfile_le_pole_iff hN).mp (hdom N hN)
  rw [abs_le]
  constructor <;> nlinarith

end GaloisForLFunctions.RHTower
