import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional

/-!
# Prime-scale positive theta source with an off-line completed zero

An exact one-prime self-reciprocal Euler numerator with positive coefficients can
preserve positivity of the completed theta source and reflection while creating zeros
inside the critical strip away from the critical line. This is a
no-go for those broad premises as an RH producer, not a claim about the literal zeta
Euler factor. The modified factor has a negative grade-two logarithmic coefficient;
coefficient-faithful von Mangoldt positivity is not preserved.
-/

namespace RHTower.ThetaPrimeScaleNoGo

noncomputable section

def P (X : ℂ) : ℂ := 1 + (57 / 20 : ℂ) * X + 2 * X ^ 2

theorem P_factor (X : ℂ) :
    P X = (1 + (5 / 4 : ℂ) * X) * (1 + (8 / 5 : ℂ) * X) := by
  unfold P
  ring

theorem P_root_left : P (-(4 / 5 : ℂ)) = 0 := by
  rw [P_factor]
  ring

theorem P_root_right : P (-(5 / 8 : ℂ)) = 0 := by
  rw [P_factor]
  ring

theorem P_reciprocal (X : ℂ) (hX : X ≠ 0) :
    2 * X ^ 2 * P (1 / (2 * X)) = P X := by
  unfold P
  field_simp
  ring

theorem grade_two_negative :
    (1 : ℝ) - (5 / 4) ^ 2 - (8 / 5) ^ 2 = -(1249 / 400) := by
  ring

def ell : ℝ := Real.log 2

theorem ell_pos : 0 < ell := by
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

def Q (s : ℂ) : ℂ :=
  Complex.exp (s * (ell : ℂ)) + 57 / 20 +
    2 * Complex.exp (-s * (ell : ℂ))

theorem exp_ell : Complex.exp (ell : ℂ) = 2 := by
  rw [← Complex.ofReal_exp]
  exact_mod_cast (Real.exp_log (by norm_num : (0 : ℝ) < 2))

theorem Q_reflect (s : ℂ) : Q (1 - s) = Q s := by
  have h1 : (1 - s) * (ell : ℂ) = (ell : ℂ) + -(s * (ell : ℂ)) := by ring
  have h2 : -(1 - s) * (ell : ℂ) = -(ell : ℂ) + s * (ell : ℂ) := by ring
  simp only [Q, h1, h2, Complex.exp_add, Complex.exp_neg, exp_ell]
  rw [← Complex.exp_neg]
  ring

theorem Q_eq_euler (s : ℂ) :
    Q s = Complex.exp (s * (ell : ℂ)) * P (Complex.exp (-s * (ell : ℂ))) := by
  unfold Q P
  rw [show -s * (ell : ℂ) = -(s * (ell : ℂ)) by ring, Complex.exp_neg]
  have hu : Complex.exp (s * (ell : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hu]

def s0 : ℂ :=
  ((Real.log (5 / 4) / ell : ℝ) : ℂ) +
    ((Real.pi / ell : ℝ) : ℂ) * Complex.I

theorem exp_neg_s0_ell :
    Complex.exp (-s0 * (ell : ℂ)) = -(4 / 5 : ℂ) := by
  have hne : ell ≠ 0 := ne_of_gt ell_pos
  have harg : -s0 * (ell : ℂ) =
      ((-Real.log (5 / 4) : ℝ) : ℂ) + ((-Real.pi : ℝ) : ℂ) * Complex.I := by
    unfold s0
    push_cast
    field_simp [hne]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
  simp [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4),
    Real.cos_neg, Real.sin_neg]

theorem Q_s0_zero : Q s0 = 0 := by
  rw [Q_eq_euler, exp_neg_s0_ell, P_root_left]
  ring

theorem s0_re_ne_half : s0.re ≠ 1 / 2 := by
  have hlog : 2 * Real.log (5 / 4 : ℝ) < Real.log 2 := by
    rw [show 2 * Real.log (5 / 4 : ℝ) =
      Real.log ((5 / 4 : ℝ) ^ 2) by rw [Real.log_pow]; ring]
    exact Real.log_lt_log (by positivity) (by norm_num)
  have hre : s0.re = Real.log (5 / 4) / ell := by simp [s0]
  have hlt : s0.re < 1 / 2 := by
    rw [hre]
    apply (div_lt_iff₀ ell_pos).2
    dsimp [ell]
    linarith
  exact ne_of_lt hlt

open MeasureTheory HedenmalmQuantile HedenmalmThetaSource

def modifiedXi (s : ℂ) : ℂ := Q s * xi s

theorem modifiedXi_reflect (s : ℂ) : modifiedXi (1 - s) = modifiedXi s := by
  simp only [modifiedXi, Q_reflect, xi_one_sub]

theorem modifiedXi_off_line_zero :
    ∃ s : ℂ, modifiedXi s = 0 ∧ s.re ≠ 1 / 2 := by
  refine ⟨s0, ?_, s0_re_ne_half⟩
  simp [modifiedXi, Q_s0_zero]

def modifiedThetaSource (x : ℝ) : ℝ :=
  (57 / 20 : ℝ) * thetaCuspFullSource x +
    Real.exp (ell / 2) *
      (thetaCuspFullSource (x + ell) + thetaCuspFullSource (x - ell))

theorem modifiedThetaSource_pos (x : ℝ) : 0 < modifiedThetaSource x := by
  have h1 := thetaCuspFullSource_pos x
  have h2 := thetaCuspFullSource_pos (x + ell)
  have h3 := thetaCuspFullSource_pos (x - ell)
  have hs : 0 < Real.exp (ell / 2) := Real.exp_pos _
  dsimp [modifiedThetaSource]
  positivity

theorem modifiedThetaSource_even (x : ℝ) :
    modifiedThetaSource (-x) = modifiedThetaSource x := by
  unfold modifiedThetaSource
  rw [thetaCuspFullSource_neg]
  rw [show -x + ell = -(x - ell) by ring,
    show -x - ell = -(x + ell) by ring]
  rw [thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

theorem sourceChar_shift (z : ℂ) (a x : ℝ) :
    sourceChar z x =
      Complex.exp (-(Complex.I * z * (a : ℂ))) * sourceChar z (x + a) := by
  unfold sourceChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_shifted_theta_source
    {z : ℂ} (hz : |z.im| < 1) (a : ℝ) :
    Integrable (fun x : ℝ =>
      (thetaCuspFullSource (x + a) : ℂ) * sourceChar z x) := by
  have hbase : Integrable (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * sourceChar z x) := by
    simpa only [thetaSource_k] using
      (integrable_k_sourceChar (S := thetaSource) (hasShiftedTail_thetaSource hz))
  have heq : (fun x : ℝ =>
      (thetaCuspFullSource (x + a) : ℂ) * sourceChar z x) =
      fun x : ℝ => Complex.exp (-(Complex.I * z * (a : ℂ))) *
        ((thetaCuspFullSource (x + a) : ℂ) * sourceChar z (x + a)) := by
    funext x
    rw [sourceChar_shift z a x]
    ring
  rw [heq]
  exact (hbase.comp_add_right a).const_mul _

theorem integral_shifted_theta_source
    {z : ℂ} (hz : |z.im| < 1) (a : ℝ) :
    (∫ x : ℝ, (thetaCuspFullSource (x + a) : ℂ) * sourceChar z x) =
      Complex.exp (-(Complex.I * z * (a : ℂ))) * XiC z := by
  calc
    _ = ∫ x : ℝ, Complex.exp (-(Complex.I * z * (a : ℂ))) *
          ((thetaCuspFullSource (x + a) : ℂ) * sourceChar z (x + a)) := by
            congr 1
            funext x
            rw [sourceChar_shift z a x]
            ring
    _ = Complex.exp (-(Complex.I * z * (a : ℂ))) *
          ∫ x : ℝ, (thetaCuspFullSource (x + a) : ℂ) * sourceChar z (x + a) := by
            rw [integral_const_mul]
    _ = Complex.exp (-(Complex.I * z * (a : ℂ))) *
          ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * sourceChar z x := by
            rw [integral_add_right_eq_self
              (fun x : ℝ => (thetaCuspFullSource x : ℂ) * sourceChar z x) a]
    _ = _ := by
      have hxi := xiC_thetaSource hz
      change (∫ x : ℝ, (thetaCuspFullSource x : ℂ) * sourceChar z x) = XiC z at hxi
      rw [hxi]

def centeredFactor (z : ℂ) : ℂ :=
  (57 / 20 : ℂ) + (Real.exp (ell / 2) : ℂ) *
    (Complex.exp (Complex.I * z * (ell : ℂ)) +
      Complex.exp (-(Complex.I * z * (ell : ℂ))))

theorem Q_centered (z : ℂ) :
    Q (1 / 2 + Complex.I * z) = centeredFactor z := by
  have hmul : (1 / 2 + Complex.I * z) * (ell : ℂ) =
      ((ell / 2 : ℝ) : ℂ) + Complex.I * z * (ell : ℂ) := by push_cast; ring
  have hmulneg : -(1 / 2 + Complex.I * z) * (ell : ℂ) =
      -((ell / 2 : ℝ) : ℂ) + -(Complex.I * z * (ell : ℂ)) := by push_cast; ring
  have hcoeff : 2 * Complex.exp (-((ell / 2 : ℝ) : ℂ)) =
      Complex.exp (((ell / 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_neg]
    have hne : Complex.exp (((ell / 2 : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hsq : Complex.exp (((ell / 2 : ℝ) : ℂ)) ^ 2 = 2 := by
      rw [pow_two, ← Complex.exp_add]
      convert exp_ell using 1 <;> push_cast; ring
    calc
      2 * (Complex.exp (((ell / 2 : ℝ) : ℂ)))⁻¹ =
          Complex.exp (((ell / 2 : ℝ) : ℂ)) ^ 2 *
            (Complex.exp (((ell / 2 : ℝ) : ℂ)))⁻¹ := by rw [hsq]
      _ = Complex.exp (((ell / 2 : ℝ) : ℂ)) := by simp [pow_two]
  unfold Q centeredFactor
  rw [hmul, hmulneg, Complex.exp_add, Complex.exp_add]
  have hcoeffC : 2 * Complex.exp (-((ell / 2 : ℝ) : ℂ)) =
      (Real.exp (ell / 2) : ℂ) := by simpa using hcoeff
  rw [← mul_assoc, hcoeffC]
  rw [← Complex.ofReal_exp]
  ring

def modifiedSourceTransform (z : ℂ) : ℂ :=
  ∫ x : ℝ, (modifiedThetaSource x : ℂ) * sourceChar z x

theorem modifiedSourceTransform_eq
    {z : ℂ} (hz : |z.im| < 1) :
    modifiedSourceTransform z = centeredFactor z * XiC z := by
  have hbase : Integrable (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * sourceChar z x) := by
    simpa only [thetaSource_k] using
      (integrable_k_sourceChar (S := thetaSource) (hasShiftedTail_thetaSource hz))
  have hp := integrable_shifted_theta_source hz ell
  have hm := integrable_shifted_theta_source hz (-ell)
  have hpoint (x : ℝ) :
      (modifiedThetaSource x : ℂ) * sourceChar z x =
        (57 / 20 : ℂ) * ((thetaCuspFullSource x : ℂ) * sourceChar z x) +
        (Real.exp (ell / 2) : ℂ) *
          ((thetaCuspFullSource (x + ell) : ℂ) * sourceChar z x) +
        (Real.exp (ell / 2) : ℂ) *
          ((thetaCuspFullSource (x - ell) : ℂ) * sourceChar z x) := by
    simp only [modifiedThetaSource, Complex.ofReal_add, Complex.ofReal_mul]
    push_cast
    ring
  have hminus :
      (∫ x : ℝ, (thetaCuspFullSource (x - ell) : ℂ) * sourceChar z x) =
        Complex.exp (Complex.I * z * (ell : ℂ)) * XiC z := by
    calc
      _ = ∫ x : ℝ, (thetaCuspFullSource (x + -ell) : ℂ) * sourceChar z x := by
        simp only [sub_eq_add_neg]
      _ = Complex.exp (-(Complex.I * z * ((-ell : ℝ) : ℂ))) * XiC z :=
        integral_shifted_theta_source hz (-ell)
      _ = _ := by congr 2; push_cast; ring
  have hzero :
      (∫ x : ℝ, (thetaCuspFullSource x : ℂ) * sourceChar z x) = XiC z := by
    have hxi := xiC_thetaSource hz
    change (∫ x : ℝ, (thetaCuspFullSource x : ℂ) * sourceChar z x) = XiC z at hxi
    exact hxi
  unfold modifiedSourceTransform
  simp_rw [hpoint]
  have hm' : Integrable (fun x : ℝ =>
      (thetaCuspFullSource (x - ell) : ℂ) * sourceChar z x) := by
    simpa only [sub_eq_add_neg] using hm
  let f0 : ℝ → ℂ := fun x => (57 / 20 : ℂ) *
    ((thetaCuspFullSource x : ℂ) * sourceChar z x)
  let fplus : ℝ → ℂ := fun x => (Real.exp (ell / 2) : ℂ) *
    ((thetaCuspFullSource (x + ell) : ℂ) * sourceChar z x)
  let fminus : ℝ → ℂ := fun x => (Real.exp (ell / 2) : ℂ) *
    ((thetaCuspFullSource (x - ell) : ℂ) * sourceChar z x)
  have hf0 : Integrable f0 := hbase.const_mul _
  have hfplus : Integrable fplus := hp.const_mul _
  have hfminus : Integrable fminus := hm'.const_mul _
  change (∫ x : ℝ, (f0 + fplus + fminus) x) = centeredFactor z * XiC z
  calc
    _ = (∫ x : ℝ, (f0 + fplus) x) + (∫ x : ℝ, fminus x) :=
      integral_add (hf0.add hfplus) hfminus
    _ = ((∫ x : ℝ, f0 x) + (∫ x : ℝ, fplus x)) +
        (∫ x : ℝ, fminus x) := by
          congr 1
          exact integral_add hf0 hfplus
    _ = _ := by
      simp only [f0, fplus, fminus, integral_const_mul]
      rw [hzero, integral_shifted_theta_source hz ell, hminus]
      unfold centeredFactor
      ring

theorem modifiedSourceTransform_eq_modifiedXi
    {z : ℂ} (hz : |z.im| < 1) :
    modifiedSourceTransform z = modifiedXi (1 / 2 + Complex.I * z) := by
  rw [modifiedSourceTransform_eq hz, ← Q_centered]
  unfold modifiedXi XiC
  congr 1
  ring

theorem modifiedSourceTransform_off_line_zero :
    ∃ z : ℂ, |z.im| < 1 ∧ modifiedSourceTransform z = 0 ∧ z.im ≠ 0 := by
  let z : ℂ := -Complex.I * (s0 - 1 / 2)
  have hcenter : 1 / 2 + Complex.I * z = s0 := by
    dsimp [z]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hzim : z.im = 1 / 2 - s0.re := by
    dsimp [z]
    simp [Complex.mul_im]
  have hz : |z.im| < 1 := by
    rw [hzim]
    have hσ0 : 0 < s0.re := by
      simp only [s0, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      exact div_pos (Real.log_pos (by norm_num)) ell_pos
    have hσ1 : s0.re < 1 := by
      have hlog : Real.log (5 / 4 : ℝ) < Real.log 2 :=
        Real.log_lt_log (by positivity) (by norm_num)
      have hre : s0.re = Real.log (5 / 4) / ell := by simp [s0]
      rw [hre]
      exact (div_lt_one ell_pos).2 (by simpa [ell] using hlog)
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨z, hz, ?_, ?_⟩
  · rw [modifiedSourceTransform_eq hz, ← Q_centered, hcenter, Q_s0_zero]
    ring
  · rw [hzim]
    exact sub_ne_zero.mpr (Ne.symm s0_re_ne_half)

end

end RHTower.ThetaPrimeScaleNoGo
