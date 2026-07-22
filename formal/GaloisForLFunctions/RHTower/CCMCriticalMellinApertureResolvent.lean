import GaloisForLFunctions.RHTower.CCMCriticalMellinVolterraHaarMode

open Complex Set MeasureTheory

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
  convert (div_neg_of_neg_of_pos (by linarith : -(w.re + 1) < 0) hden) using 1
  all_goals ring

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
