import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import GaloisForLFunctions.RHTower.CothInfra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Suzuki Herglotz boundary states

The far-negative Suzuki boundary is more rigid than zero-Schur collapse alone suggests.  Its
normalized Herglotz transform is exactly

`mₐ(z) = coth(a) tan(a z)`.

Thus its real singular set is the half-integer clock.  As aperture tends to infinity, the
already-proved locally uniform collapse of the free Livšic carrier transports through the
Cayley inverse and gives `mₐ → i` locally uniformly on the upper half-plane.  At the opposite
ground edge, `suzukiUpperCayleyInv_lineCayley` already proves the exact boundary state `m(z)=z`.

These are two different projective data-erasure mechanisms: clock-spectrum homogenization at the
free end and linear mass at infinity at the ground edge.  The measure-level Nevanlinna
classification is recorded in the accompanying paper card; this file formalizes the exact
transform identity, clock denominator, normalization, and transform-level limit without an RH
hypothesis or numerical computation.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Herglotz transform of Suzuki's universal far-negative free Livšic carrier. -/
def suzukiFreeHerglotz (a : ℝ) (z : ℂ) : ℂ :=
  suzukiUpperCayleyInv (suzukiFreeLivsic a z)

private theorem suzuki_rcoth_eq_exp_ratio {a : ℝ} (ha : a ≠ 0) :
    RHTower.rcoth a = (1 + Real.exp (-2 * a)) / (1 - Real.exp (-2 * a)) := by
  rw [RHTower.rcoth, Real.cosh_eq, Real.sinh_eq]
  have hea : Real.exp a ≠ 0 := ne_of_gt (Real.exp_pos a)
  have hena : Real.exp (-a) ≠ 0 := ne_of_gt (Real.exp_pos (-a))
  have hden : Real.exp a - Real.exp (-a) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have heq : a = -a := Real.exp_injective h
    apply ha
    linarith
  have hprod : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]
    simp
  have hratio : Real.exp (-2 * a) = Real.exp (-a) / Real.exp a := by
    calc
      Real.exp (-2 * a) = Real.exp (-a - a) := by congr 1; ring
      _ = Real.exp (-a) / Real.exp a := Real.exp_sub (-a) a
  rw [hratio]
  field_simp

private theorem complex_tan_eq_I_mul_one_sub_exp_two_I_div_one_add {w : ℂ}
    (hcos : Complex.cos w ≠ 0) :
    Complex.tan w = I * ((1 - Complex.exp (2 * I * w)) /
      (1 + Complex.exp (2 * I * w))) := by
  have he : Complex.exp (w * I) ≠ 0 := Complex.exp_ne_zero _
  have hen : Complex.exp (-(w * I)) ≠ 0 := Complex.exp_ne_zero _
  have hprod : Complex.exp (-(w * I)) * Complex.exp (w * I) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hsq : Complex.exp (2 * I * w) = Complex.exp (w * I) * Complex.exp (w * I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsum : Complex.exp (w * I) + Complex.exp (-(w * I)) ≠ 0 := by
    intro h
    apply hcos
    rw [Complex.cos, show -w * I = -(w * I) by ring, h]
    simp
  have hquad : 1 + Complex.exp (w * I) * Complex.exp (w * I) ≠ 0 := by
    intro h
    apply hsum
    have hzero : Complex.exp (-(w * I)) *
        (1 + Complex.exp (w * I) * Complex.exp (w * I)) = 0 := by rw [h, mul_zero]
    calc
      Complex.exp (w * I) + Complex.exp (-(w * I)) =
          Complex.exp (-(w * I)) *
            (1 + Complex.exp (w * I) * Complex.exp (w * I)) := by
              calc
                _ = Complex.exp (-(w * I)) +
                    (Complex.exp (-(w * I)) * Complex.exp (w * I)) *
                      Complex.exp (w * I) := by rw [hprod]; ring
                _ = _ := by ring
      _ = 0 := hzero
  have hquad' : 1 + Complex.exp (w * I) ^ 2 ≠ 0 := by
    simpa [pow_two] using hquad
  have hfrac :
      (Complex.exp (-(w * I)) - Complex.exp (w * I)) /
          (Complex.exp (w * I) + Complex.exp (-(w * I))) =
        (1 - Complex.exp (w * I) ^ 2) / (1 + Complex.exp (w * I) ^ 2) := by
    field_simp [hsum, hquad']
    linear_combination 2 * Complex.exp (w * I) * hprod
  rw [Complex.tan_eq_sin_div_cos, Complex.sin, Complex.cos,
    div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0), hsq]
  simp only [neg_mul]
  calc
    (Complex.exp (-(w * I)) - Complex.exp (w * I)) * I /
          (Complex.exp (w * I) + Complex.exp (-(w * I))) =
        I * ((Complex.exp (-(w * I)) - Complex.exp (w * I)) /
          (Complex.exp (w * I) + Complex.exp (-(w * I)))) := by ring
    _ = I * ((1 - Complex.exp (w * I) ^ 2) /
          (1 + Complex.exp (w * I) ^ 2)) := by rw [hfrac]
    _ = I * ((1 - Complex.exp (w * I) * Complex.exp (w * I)) /
          (1 + Complex.exp (w * I) * Complex.exp (w * I))) := by rw [pow_two]

private theorem upperCayleyInv_free_algebra {q y : ℂ}
    (hqy : 1 - q * y ≠ 0) (hq : 1 - q ≠ 0) (hy : 1 + y ≠ 0) :
    suzukiUpperCayleyInv ((q - y) / (1 - q * y)) =
      I * ((1 + q) / (1 - q)) * ((1 - y) / (1 + y)) := by
  have hnum : 1 + (q - y) / (1 - q * y) =
      ((1 + q) * (1 - y)) / (1 - q * y) := by
    field_simp [hqy]
    ring
  have hden : 1 - (q - y) / (1 - q * y) =
      ((1 - q) * (1 + y)) / (1 - q * y) := by
    field_simp [hqy]
    ring
  rw [suzukiUpperCayleyInv]
  rw [hnum, hden, div_div_div_cancel_right₀ hqy]
  field_simp [hq, hy]

/-- **Exact free-clock transform.**  On the upper half-plane, Suzuki's far-negative universal
boundary is the hyperbolically normalized tangent Herglotz function. -/
theorem suzukiFreeHerglotz_eq_rcoth_mul_tan
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    suzukiFreeHerglotz a z =
      ((RHTower.rcoth a : ℝ) : ℂ) * Complex.tan ((a : ℂ) * z) := by
  let q : ℂ := (Real.exp (-2 * a) : ℝ)
  let y : ℂ := Complex.exp (2 * I * (a : ℂ) * z)
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_lt_one_iff]
    linarith
  have hynorm : ‖y‖ < 1 := by
    dsimp [y]
    rw [norm_suzukiFreeOscillator, Real.exp_lt_one_iff]
    nlinarith [mul_pos ha hz]
  have hq : 1 - q ≠ 0 := by
    intro h
    have hq1 : q = 1 := (sub_eq_zero.mp h).symm
    rw [hq1, norm_one] at hqnorm
    exact (lt_irrefl 1) hqnorm
  have hy : 1 + y ≠ 0 := by
    intro h
    have hy1 : y = -1 := by linear_combination h
    rw [hy1, norm_neg, norm_one] at hynorm
    exact (lt_irrefl 1) hynorm
  have hqynorm : ‖q * y‖ < 1 := by
    rw [norm_mul]
    calc
      ‖q‖ * ‖y‖ ≤ 1 * ‖y‖ :=
        mul_le_mul_of_nonneg_right hqnorm.le (norm_nonneg y)
      _ < 1 * 1 := by simpa using hynorm
      _ = 1 := by norm_num
  have hqy : 1 - q * y ≠ 0 := by
    intro h
    have hqy1 : q * y = 1 := (sub_eq_zero.mp h).symm
    rw [hqy1, norm_one] at hqynorm
    exact (lt_irrefl 1) hqynorm
  have hcos : Complex.cos ((a : ℂ) * z) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have him := congrArg Complex.im hk
    norm_num [Complex.mul_im] at him
    rcases him with ha0 | hz0
    · exact (ne_of_gt ha) ha0
    · exact (ne_of_gt hz) hz0
  have hcoth : ((RHTower.rcoth a : ℝ) : ℂ) = (1 + q) / (1 - q) := by
    rw [suzuki_rcoth_eq_exp_ratio (ne_of_gt ha)]
    simp only [q, ofReal_div, ofReal_add, ofReal_one, ofReal_exp, ofReal_sub]
  have htan : Complex.tan ((a : ℂ) * z) =
      I * ((1 - y) / (1 + y)) := by
    have ht := complex_tan_eq_I_mul_one_sub_exp_two_I_div_one_add hcos
    have hyexp : Complex.exp (2 * I * ((a : ℂ) * z)) = y := by
      dsimp [y]
      congr 1
      ring
    simpa only [hyexp] using ht
  rw [suzukiFreeHerglotz, suzukiFreeLivsic]
  change suzukiUpperCayleyInv ((q - y) / (1 - q * y)) = _
  rw [upperCayleyInv_free_algebra hqy hq hy, hcoth, htan]
  ring

/-- Real half-integer clock underlying the free Suzuki Herglotz state. -/
def suzukiFreeClockPoint (a : ℝ) (k : ℤ) : ℝ :=
  (((k : ℝ) + 1 / 2) * Real.pi) / a

/-- The tangent denominator in the exact free Suzuki transform vanishes precisely on the
half-integer clock. -/
theorem suzukiFreeClock_cos_eq_zero_iff {a : ℝ} (ha : 0 < a) {z : ℂ} :
    Complex.cos ((a : ℂ) * z) = 0 ↔
      ∃ k : ℤ, z = (suzukiFreeClockPoint a k : ℂ) := by
  rw [Complex.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
    apply (mul_left_cancel₀ haC)
    rw [hk]
    simp only [suzukiFreeClockPoint, ofReal_div, ofReal_mul, ofReal_add, ofReal_intCast,
      ofReal_one, ofReal_ofNat]
    field_simp [haC]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
    simp only [suzukiFreeClockPoint, ofReal_div, ofReal_mul, ofReal_add, ofReal_intCast,
      ofReal_one, ofReal_ofNat]
    field_simp [haC]

/-- Suzuki's canonical anchor survives exactly at the free Herglotz boundary. -/
@[simp] theorem suzukiFreeHerglotz_I_eq_I (a : ℝ) :
    suzukiFreeHerglotz a I = I := by
  simp [suzukiFreeHerglotz, suzukiUpperCayleyInv, suzukiFreeLivsic_I_eq_zero]

/-- **Transform-level clock homogenization.**  Free Suzuki Herglotz states converge locally
uniformly to the constant state `i` throughout the upper half-plane. -/
theorem suzukiFreeHerglotz_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (fun a : ℝ => suzukiFreeHerglotz a) (fun _ => I) atTop
      {z : ℂ | 0 < z.im} := by
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  have hconst (c : ℂ) :
      TendstoLocallyUniformlyOn (fun _a : ℝ => fun _z : ℂ => c) (fun _z => c) atTop s := by
    have hc : Tendsto (fun _a : ℝ => c) atTop (nhds c) := tendsto_const_nhds
    exact (hc.tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn
  have htheta :
      TendstoLocallyUniformlyOn (fun a : ℝ => suzukiFreeLivsic a) (fun _ => 0) atTop s :=
    suzukiFreeLivsic_tendstoLocallyUniformlyOn
  have hnum : TendstoLocallyUniformlyOn
      (fun a : ℝ => fun z : ℂ => 1 + suzukiFreeLivsic a z) (fun _ => 1) atTop s := by
    have hraw := (hconst 1).add htheta
    refine (hraw.congr ?_).congr_right ?_
    · intro a z hz
      simp
    · intro z hz
      simp
  have hden : TendstoLocallyUniformlyOn
      (fun a : ℝ => fun z : ℂ => 1 - suzukiFreeLivsic a z) (fun _ => 1) atTop s := by
    have hraw := (hconst 1).sub htheta
    refine (hraw.congr ?_).congr_right ?_
    · intro a z hz
      simp
    · intro z hz
      simp
  have hquot : TendstoLocallyUniformlyOn
      (fun a : ℝ => fun z : ℂ =>
        (1 + suzukiFreeLivsic a z) / (1 - suzukiFreeLivsic a z))
      (fun _ => 1) atTop s := by
    have hraw := hnum.div₀ hden continuousOn_const continuousOn_const (by simp)
    refine (hraw.congr ?_).congr_right ?_
    · intro a z hz
      simp
    · intro z hz
      simp
  have hmul := (hconst I).mul₀ hquot continuousOn_const continuousOn_const
  refine (hmul.congr ?_).congr_right ?_
  · intro a z hz
    simp [suzukiFreeHerglotz, suzukiUpperCayleyInv]
  · intro z hz
    simp

end GaloisForLFunctions.RHTower
