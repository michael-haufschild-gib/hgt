import GaloisForLFunctions.RHTower.CCMCriticalMellinVolterraHaarMode
import Mathlib.NumberTheory.Chebyshev

open Complex Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-!
# Exponential aperture averaging for the CCM critical-Mellin detector

The fixed-aperture Volterra--Haar multiplier has nontrivial phase.  Exponentially averaging the
aperture evaluates it exactly as a rational resolvent.  At unit averaging rate the cancellation is
especially sharp: the multiplier is `-1 / (w + 1)`, hence has negative real part throughout the
open right half-plane.
-/

def criticalMellinApertureAveragedMultiplier (a : ℝ) (w : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi 0,
    Complex.exp (-(a : ℂ) * (L : ℂ)) *
      criticalMellinVolterraHaarMultiplier L w

theorem criticalMellinApertureAveragedMultiplier_eq
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedMultiplier a w =
      -(2 * w + 1) / ((a : ℂ) * ((a : ℂ) + w) * ((a : ℂ) + 2 * w)) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  let c : ℂ := -(2 * w + 1) / (2 * w ^ 2)
  let q0 : ℂ := -(a : ℂ)
  let q1 : ℂ := -((a : ℂ) + w)
  let q2 : ℂ := -((a : ℂ) + 2 * w)
  have hq0 : q0.re < 0 := by
    dsimp only [q0]
    simp
    exact ha
  have hq1 : q1.re < 0 := by
    dsimp only [q1]
    simp
    linarith
  have hq2 : q2.re < 0 := by
    dsimp only [q2]
    simp
    linarith
  have hi0 : IntegrableOn (fun L : ℝ => Complex.exp (q0 * (L : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq0 0
  have hi1 : IntegrableOn (fun L : ℝ => Complex.exp (q1 * (L : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq1 0
  have hi2 : IntegrableOn (fun L : ℝ => Complex.exp (q2 * (L : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq2 0
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haw0 : (a : ℂ) + w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  have ha2w0 : (a : ℂ) + 2 * w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hfun : (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        criticalMellinVolterraHaarMultiplier L w) =
      fun L : ℝ => c *
        (Complex.exp (q0 * (L : ℂ)) -
          2 * Complex.exp (q1 * (L : ℂ)) +
          Complex.exp (q2 * (L : ℂ))) := by
    funext L
    have h1 : Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) =
        Complex.exp (q1 * (L : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp only [q0, q1]
      ring
    have h2 : Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) ^ 2 =
        Complex.exp (q2 * (L : ℂ)) := by
      rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      dsimp only [q0, q2]
      ring
    rw [criticalMellinVolterraHaarMultiplier]
    change Complex.exp (q0 * (L : ℂ)) *
      (-((2 * w + 1) * (1 - Complex.exp (-(w * L))) ^ 2) / (2 * w ^ 2)) = _
    dsimp only [c]
    calc
      Complex.exp (q0 * (L : ℂ)) *
          (-((2 * w + 1) * (1 - Complex.exp (-(w * L))) ^ 2) / (2 * w ^ 2)) =
        -(2 * w + 1) / (2 * w ^ 2) *
          (Complex.exp (q0 * (L : ℂ)) -
            2 * (Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L))) +
            Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) ^ 2) := by ring
      _ = _ := by rw [h1, h2]
  have hsplit :
      (∫ L : ℝ in Ioi 0,
        (Complex.exp (q0 * (L : ℂ)) -
          2 * Complex.exp (q1 * (L : ℂ)) +
          Complex.exp (q2 * (L : ℂ)))) =
        (∫ L : ℝ in Ioi 0, Complex.exp (q0 * (L : ℂ))) -
          2 * (∫ L : ℝ in Ioi 0, Complex.exp (q1 * (L : ℂ))) +
          ∫ L : ℝ in Ioi 0, Complex.exp (q2 * (L : ℂ)) := by
    calc
      (∫ L : ℝ in Ioi 0,
          (Complex.exp (q0 * (L : ℂ)) -
            2 * Complex.exp (q1 * (L : ℂ))) +
            Complex.exp (q2 * (L : ℂ))) =
        (∫ L : ℝ in Ioi 0,
          Complex.exp (q0 * (L : ℂ)) -
            2 * Complex.exp (q1 * (L : ℂ))) +
          ∫ L : ℝ in Ioi 0, Complex.exp (q2 * (L : ℂ)) :=
            MeasureTheory.integral_add (hi0.sub (hi1.const_mul 2)) hi2
      _ = _ := by
        rw [MeasureTheory.integral_sub hi0 (hi1.const_mul 2),
          MeasureTheory.integral_const_mul]
  rw [criticalMellinApertureAveragedMultiplier, hfun,
    MeasureTheory.integral_const_mul, hsplit]
  rw [integral_exp_mul_complex_Ioi hq0 0,
    integral_exp_mul_complex_Ioi hq1 0,
    integral_exp_mul_complex_Ioi hq2 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  dsimp only [c, q0, q1, q2]
  field_simp [hw0, ha0, haw0, ha2w0]
  ring

theorem criticalMellinApertureAveragedMultiplier_one_eq
    {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedMultiplier 1 w =
      -1 / (w + 1) := by
  rw [criticalMellinApertureAveragedMultiplier_eq (by norm_num) hw]
  have hwOne : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have htwo : 2 * w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  norm_num
  have honeW : (1 : ℂ) + w ≠ 0 := by simpa [add_comm] using hwOne
  have honeTwoW : (1 : ℂ) + 2 * w ≠ 0 := by simpa [add_comm] using htwo
  field_simp [honeW, honeTwoW, hwOne]
  ring

theorem re_criticalMellinApertureAveragedMultiplier_one_neg
    {w : ℂ} (hw : 0 < w.re) :
    (criticalMellinApertureAveragedMultiplier 1 w).re < 0 := by
  rw [criticalMellinApertureAveragedMultiplier_one_eq hw]
  simp only [Complex.neg_re, Complex.div_re, Complex.normSq_apply,
    Complex.neg_im, Complex.one_re, Complex.one_im, Complex.add_re,
    Complex.add_im]
  norm_num
  have hden : 0 < (w.re + 1) ^ 2 + w.im ^ 2 := by
    positivity
  apply div_neg_of_neg_of_pos
  · linarith
  · simpa only [pow_two] using hden

def criticalMellinApertureAveragedModeResponse
    (a x : ℝ) (w : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi 0,
    Complex.exp (-(a : ℂ) * (L : ℂ)) *
      criticalMellinVolterraModeAdjacentBlock L x w

theorem criticalMellinApertureAveragedModeResponse_eq
    {a x : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedModeResponse a x w =
      Complex.exp (w * x) *
        (-(2 * w + 1) /
          ((a : ℂ) * ((a : ℂ) + w) * ((a : ℂ) + 2 * w))) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  rw [criticalMellinApertureAveragedModeResponse]
  have hfun : (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        criticalMellinVolterraModeAdjacentBlock L x w) =
      fun L : ℝ => Complex.exp (w * x) *
        (Complex.exp (-(a : ℂ) * (L : ℂ)) *
          criticalMellinVolterraHaarMultiplier L w) := by
    funext L
    rw [criticalMellinVolterraModeAdjacentBlock_eq hw0]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    ← criticalMellinApertureAveragedMultiplier,
    criticalMellinApertureAveragedMultiplier_eq ha hw]
def criticalMellinApertureAveragedMultiplierTail
    (c : ℝ) (w : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi c,
    Complex.exp (-(L : ℂ)) * criticalMellinVolterraHaarMultiplier L w

theorem criticalMellinApertureAveragedMultiplierTail_eq
    (c : ℝ) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedMultiplierTail c w =
      (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp (-(c : ℂ)) -
          2 * Complex.exp (-(((1 : ℂ) + w) * c)) / ((1 : ℂ) + w) +
          Complex.exp (-(((1 : ℂ) + 2 * w) * c)) / ((1 : ℂ) + 2 * w)) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  let d : ℂ := -(2 * w + 1) / (2 * w ^ 2)
  let q0 : ℂ := -1
  let q1 : ℂ := -((1 : ℂ) + w)
  let q2 : ℂ := -((1 : ℂ) + 2 * w)
  have hq0 : q0.re < 0 := by dsimp only [q0]; norm_num
  have hq1 : q1.re < 0 := by
    dsimp only [q1]
    simp
    linarith
  have hq2 : q2.re < 0 := by
    dsimp only [q2]
    simp
    linarith
  have hi0 : IntegrableOn (fun L : ℝ => Complex.exp (q0 * (L : ℂ))) (Ioi c) :=
    integrableOn_exp_mul_complex_Ioi hq0 c
  have hi1 : IntegrableOn (fun L : ℝ => Complex.exp (q1 * (L : ℂ))) (Ioi c) :=
    integrableOn_exp_mul_complex_Ioi hq1 c
  have hi2 : IntegrableOn (fun L : ℝ => Complex.exp (q2 * (L : ℂ))) (Ioi c) :=
    integrableOn_exp_mul_complex_Ioi hq2 c
  have hOneW : (1 : ℂ) + w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hOneTwoW : (1 : ℂ) + 2 * w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hfun : (fun L : ℝ =>
      Complex.exp (-(L : ℂ)) * criticalMellinVolterraHaarMultiplier L w) =
      fun L : ℝ => d *
        (Complex.exp (q0 * (L : ℂ)) -
          2 * Complex.exp (q1 * (L : ℂ)) +
          Complex.exp (q2 * (L : ℂ))) := by
    funext L
    have h0 : Complex.exp (-(L : ℂ)) = Complex.exp (q0 * (L : ℂ)) := by
      congr 1
      dsimp only [q0]
      ring
    have h1 : Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) =
        Complex.exp (q1 * (L : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp only [q0, q1]
      ring
    have h2 : Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) ^ 2 =
        Complex.exp (q2 * (L : ℂ)) := by
      rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      dsimp only [q0, q2]
      ring
    rw [criticalMellinVolterraHaarMultiplier]
    rw [h0]
    change Complex.exp (q0 * (L : ℂ)) *
      (-((2 * w + 1) * (1 - Complex.exp (-(w * L))) ^ 2) / (2 * w ^ 2)) = _
    dsimp only [d]
    calc
      Complex.exp (q0 * (L : ℂ)) *
          (-((2 * w + 1) * (1 - Complex.exp (-(w * L))) ^ 2) / (2 * w ^ 2)) =
        -(2 * w + 1) / (2 * w ^ 2) *
          (Complex.exp (q0 * (L : ℂ)) -
            2 * (Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L))) +
            Complex.exp (q0 * (L : ℂ)) * Complex.exp (-(w * L)) ^ 2) := by ring
      _ = _ := by rw [h1, h2]
  have hsplit :
      (∫ L : ℝ in Ioi c,
        (Complex.exp (q0 * (L : ℂ)) -
          2 * Complex.exp (q1 * (L : ℂ)) +
          Complex.exp (q2 * (L : ℂ)))) =
        (∫ L : ℝ in Ioi c, Complex.exp (q0 * (L : ℂ))) -
          2 * (∫ L : ℝ in Ioi c, Complex.exp (q1 * (L : ℂ))) +
          ∫ L : ℝ in Ioi c, Complex.exp (q2 * (L : ℂ)) := by
    calc
      (∫ L : ℝ in Ioi c,
          (Complex.exp (q0 * (L : ℂ)) -
            2 * Complex.exp (q1 * (L : ℂ))) +
            Complex.exp (q2 * (L : ℂ))) =
        (∫ L : ℝ in Ioi c,
          Complex.exp (q0 * (L : ℂ)) -
            2 * Complex.exp (q1 * (L : ℂ))) +
          ∫ L : ℝ in Ioi c, Complex.exp (q2 * (L : ℂ)) :=
            MeasureTheory.integral_add (hi0.sub (hi1.const_mul 2)) hi2
      _ = _ := by
        rw [MeasureTheory.integral_sub hi0 (hi1.const_mul 2),
          MeasureTheory.integral_const_mul]
  rw [criticalMellinApertureAveragedMultiplierTail, hfun,
    MeasureTheory.integral_const_mul, hsplit]
  rw [integral_exp_mul_complex_Ioi hq0 c,
    integral_exp_mul_complex_Ioi hq1 c,
    integral_exp_mul_complex_Ioi hq2 c]
  dsimp only [d, q0, q1, q2]
  field_simp [hw0, hOneW, hOneTwoW]

def criticalMellinApertureAveragedModeResponseTail
    (c x : ℝ) (w : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi c,
    Complex.exp (-(L : ℂ)) *
      criticalMellinVolterraModeAdjacentBlock L x w

theorem criticalMellinApertureAveragedModeResponseTail_eq
    (c x : ℝ) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedModeResponseTail c x w =
      Complex.exp (w * x) * (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp (-(c : ℂ)) -
          2 * Complex.exp (-(((1 : ℂ) + w) * c)) / ((1 : ℂ) + w) +
          Complex.exp (-(((1 : ℂ) + 2 * w) * c)) / ((1 : ℂ) + 2 * w)) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  rw [criticalMellinApertureAveragedModeResponseTail]
  have hfun : (fun L : ℝ =>
      Complex.exp (-(L : ℂ)) *
        criticalMellinVolterraModeAdjacentBlock L x w) =
      fun L : ℝ => Complex.exp (w * x) *
        (Complex.exp (-(L : ℂ)) *
          criticalMellinVolterraHaarMultiplier L w) := by
    funext L
    rw [criticalMellinVolterraModeAdjacentBlock_eq hw0]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    ← criticalMellinApertureAveragedMultiplierTail,
    criticalMellinApertureAveragedMultiplierTail_eq c hw]
  ring

theorem criticalMellinApertureAdmissibleModeResponseTail_eq
    (x : ℝ) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinApertureAveragedModeResponseTail (x / 2) x w =
      (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp ((w - 1 / 2) * x) -
          2 * Complex.exp ((w / 2 - 1 / 2) * x) / ((1 : ℂ) + w) +
          Complex.exp (-(x : ℂ) / 2) / ((1 : ℂ) + 2 * w)) := by
  rw [criticalMellinApertureAveragedModeResponseTail_eq (x / 2) x hw]
  have hfirst :
      Complex.exp (w * x) * Complex.exp (-((x / 2 : ℝ) : ℂ)) =
        Complex.exp ((w - 1 / 2) * x) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsecond :
      Complex.exp (w * x) *
          Complex.exp (-(((1 : ℂ) + w) * ((x / 2 : ℝ) : ℂ))) =
        Complex.exp ((w / 2 - 1 / 2) * x) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hthird :
      Complex.exp (w * x) *
          Complex.exp (-(((1 : ℂ) + 2 * w) * ((x / 2 : ℝ) : ℂ))) =
        Complex.exp (-(x : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    Complex.exp (w * x) * (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp (-((x / 2 : ℝ) : ℂ)) -
          2 * Complex.exp (-(((1 : ℂ) + w) * ((x / 2 : ℝ) : ℂ))) /
            ((1 : ℂ) + w) +
          Complex.exp (-(((1 : ℂ) + 2 * w) * ((x / 2 : ℝ) : ℂ))) /
            ((1 : ℂ) + 2 * w)) =
      (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp (w * x) * Complex.exp (-((x / 2 : ℝ) : ℂ)) -
          2 * (Complex.exp (w * x) *
            Complex.exp (-(((1 : ℂ) + w) * ((x / 2 : ℝ) : ℂ)))) /
              ((1 : ℂ) + w) +
          (Complex.exp (w * x) *
            Complex.exp (-(((1 : ℂ) + 2 * w) * ((x / 2 : ℝ) : ℂ)))) /
              ((1 : ℂ) + 2 * w)) := by ring
    _ = _ := by rw [hfirst, hsecond, hthird]

private theorem tendsto_complex_exp_mul_atTop_zero
    {q : ℂ} (hq : q.re < 0) :
    Tendsto (fun x : ℝ => Complex.exp (q * x)) atTop (nhds 0) := by
  simpa [Complex.tendsto_exp_nhds_zero_iff] using
    tendsto_const_nhds.neg_mul_atTop hq tendsto_id

theorem criticalMellinApertureAdmissibleModeResponseTail_tendsto_zero
    {w : ℂ} (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    Tendsto
      (fun x : ℝ =>
        criticalMellinApertureAveragedModeResponseTail (x / 2) x w)
      atTop (nhds 0) := by
  have hq0 : (w - 1 / 2).re < 0 := by
    norm_num
    linarith
  have hq1 : (w / 2 - 1 / 2).re < 0 := by
    norm_num
    linarith
  have h0 := tendsto_complex_exp_mul_atTop_zero hq0
  have h1 := tendsto_complex_exp_mul_atTop_zero hq1
  have h2 : Tendsto (fun x : ℝ => Complex.exp (-(x : ℂ) / 2)) atTop (nhds 0) := by
    convert tendsto_complex_exp_mul_atTop_zero (q := -(1 / 2 : ℂ)) (by norm_num) using 1
    funext x
    congr 1
    ring
  have hsum :
      Tendsto
        (fun x : ℝ =>
          Complex.exp ((w - 1 / 2) * x) -
            2 * Complex.exp ((w / 2 - 1 / 2) * x) / ((1 : ℂ) + w) +
            Complex.exp (-(x : ℂ) / 2) / ((1 : ℂ) + 2 * w))
        atTop (nhds 0) := by
    simpa using
      (h0.sub ((h1.const_mul 2).div_const ((1 : ℂ) + w))).add
        (h2.div_const ((1 : ℂ) + 2 * w))
  rw [show (fun x : ℝ =>
      criticalMellinApertureAveragedModeResponseTail (x / 2) x w) =
      fun x : ℝ => (-(2 * w + 1) / (2 * w ^ 2)) *
        (Complex.exp ((w - 1 / 2) * x) -
          2 * Complex.exp ((w / 2 - 1 / 2) * x) / ((1 : ℂ) + w) +
          Complex.exp (-(x : ℂ) / 2) / ((1 : ℂ) + 2 * w)) by
    funext x
    exact criticalMellinApertureAdmissibleModeResponseTail_eq x hw0]
  simpa only [mul_zero] using
    hsum.const_mul (-(2 * w + 1) / (2 * w ^ 2))

/-- Normalized Chebyshev error on logarithmic scale. -/
def criticalMellinChebyshevError (x : ℝ) : ℝ :=
  (Chebyshev.psi (Real.exp x) - Real.exp x) *
    (Real.exp x) ^ (-(1 / 2 : ℝ))

theorem criticalMellinChebyshevError_eq_exp
    (x : ℝ) :
    criticalMellinChebyshevError x =
      (Chebyshev.psi (Real.exp x) - Real.exp x) * Real.exp (-x / 2) := by
  rw [criticalMellinChebyshevError, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  congr 1
  ring_nf

/-- Unit-rate positive causal resolvent of the normalized Chebyshev error. -/
def criticalMellinChebyshevResolventSource (x : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    Real.exp (-t) * criticalMellinChebyshevError (x - t)

/-- Exact prime-source form of the unit CCM aperture resolvent. -/
theorem criticalMellinChebyshevResolventSource_log_eq
    {X : ℝ} (hX : 0 < X) :
    criticalMellinChebyshevResolventSource (Real.log X) =
      X⁻¹ * ∫ y : ℝ in 0..X,
        (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)) := by
  let f : ℝ → ℝ := fun t => X * Real.exp (-t)
  let g : ℝ → ℝ := fun y => X⁻¹ *
    ((Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)))
  have hfderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (-f t) (Ioi 0) t := by
    intro t _ht
    have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul X
    simpa only [f, Function.comp_apply, mul_neg, mul_one] using h.hasDerivWithinAt
  have hinj : Set.InjOn f (Ioi (0 : ℝ)) := by
    intro a _ha b _hb hab
    apply neg_injective
    apply Real.exp_injective
    exact mul_left_cancel₀ hX.ne' hab
  have himage : f '' Ioi (0 : ℝ) = Ioo 0 X := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨mul_pos hX (Real.exp_pos _), ?_⟩
      calc
        X * Real.exp (-t) < X * 1 :=
          mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)) hX
        _ = X := mul_one X
    · intro hy
      refine ⟨Real.log (X / y), ?_, ?_⟩
      · exact Real.log_pos ((one_lt_div hy.1).2 hy.2)
      · dsimp only [f]
        rw [Real.exp_neg, Real.exp_log (div_pos hX hy.1)]
        field_simp
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hfderiv hinj g
  rw [himage] at hchange
  have hexp (t : ℝ) : Real.exp (Real.log X - t) = f t := by
    dsimp only [f]
    rw [Real.exp_sub, Real.exp_log hX, Real.exp_neg]
    ring
  have hfun :
      (fun t : ℝ => |(-f t)| • g (f t)) =
        fun t : ℝ =>
          Real.exp (-t) *
            criticalMellinChebyshevError (Real.log X - t) := by
    funext t
    rw [criticalMellinChebyshevError, hexp]
    dsimp only [f, g]
    rw [abs_neg, abs_of_pos (mul_pos hX (Real.exp_pos _))]
    simp only [smul_eq_mul]
    field_simp [hX.ne']
  rw [hfun] at hchange
  calc
    criticalMellinChebyshevResolventSource (Real.log X) =
        ∫ t : ℝ in Ioi 0,
          Real.exp (-t) * criticalMellinChebyshevError (Real.log X - t) := rfl
    _ = ∫ y : ℝ in Ioo 0 X, g y := hchange.symm
    _ = X⁻¹ * ∫ y : ℝ in Ioo 0 X,
        (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)) := by
      rw [show g = fun y : ℝ => X⁻¹ *
          ((Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))) from rfl,
        integral_const_mul]
    _ = X⁻¹ * ∫ y : ℝ in 0..X,
        (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_of_le hX.le, integral_Ioc_eq_integral_Ioo]


/-!
The same cancellation is visible before taking modes.  Exponential aperture averaging gives the
causal kernel `2 * exp (-t) - exp (-t / 2)`.  Adding half its Volterra primitive cancels the slow
exponential exactly and leaves the unit resolvent kernel `exp (-t)`.
-/

def criticalMellinApertureCausalKernel (t : ℝ) : ℂ :=
  2 * Complex.exp (-(t : ℂ)) - Complex.exp (-(t : ℂ) / 2)

theorem integral_criticalMellinApertureCausalKernel
    (t : ℝ) :
    (∫ s : ℝ in 0..t, criticalMellinApertureCausalKernel s) =
      2 * (Complex.exp (-(t : ℂ) / 2) - Complex.exp (-(t : ℂ))) := by
  simp_rw [criticalMellinApertureCausalKernel]
  simp_rw [show ∀ s : ℝ, -(s : ℂ) = (-1 : ℂ) * s by intro s; ring]
  have hhalf : (fun s : ℝ => Complex.exp ((-1 : ℂ) * s / 2)) =
      fun s : ℝ => Complex.exp ((-(1 / 2) : ℂ) * s) := by
    funext s
    congr 1
    ring_nf
  have hi1 : IntervalIntegrable
      (fun s : ℝ => 2 * Complex.exp ((-1 : ℂ) * s)) volume 0 t := by
    exact (by fun_prop : Continuous (fun s : ℝ =>
      2 * Complex.exp ((-1 : ℂ) * s))).intervalIntegrable 0 t
  have hihalf : IntervalIntegrable
      (fun s : ℝ => Complex.exp ((-1 : ℂ) * s / 2)) volume 0 t := by
    exact (by fun_prop : Continuous (fun s : ℝ =>
      Complex.exp ((-1 : ℂ) * s / 2))).intervalIntegrable 0 t
  rw [intervalIntegral.integral_sub hi1 hihalf,
    intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (by norm_num : (-1 : ℂ) ≠ 0),
    hhalf,
    integral_exp_mul_complex (by norm_num : (-(1 / 2) : ℂ) ≠ 0)]
  norm_num
  ring_nf

theorem criticalMellinApertureCausalKernel_volterra_collapse
    (t : ℝ) :
    criticalMellinApertureCausalKernel t +
        (1 / 2 : ℂ) * (∫ s : ℝ in 0..t, criticalMellinApertureCausalKernel s) =
      Complex.exp (-(t : ℂ)) := by
  rw [integral_criticalMellinApertureCausalKernel]
  rw [criticalMellinApertureCausalKernel]
  ring_nf

end

end RHTower
