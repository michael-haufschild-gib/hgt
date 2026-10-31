import GaloisForLFunctions.HTGeometry.WienerHopfIndexTheorem
import GaloisForLFunctions.RHTower.WindingDivisor
import GaloisForLFunctions.RHTower.WindingHomotopy
import GaloisForLFunctions.ConjugateDiagonalGeometry.NewtonDifferencePolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Two-scale Zhukovsky Laurent loops and Wiener–Hopf horizontal collision index

Evaluating the Newton–Girard difference polynomial of a critical-strip zero divisor along the
two-scale Zhukovsky Laurent map

`J_n(z) = 1 / 2 + (c_n / 2) * (z + z⁻¹)`

on the circle `|z| = ρ_n > 1` traces the positively oriented ellipse centered at `1 / 2` with
horizontal semi-axis `a_n = 1 / 2 - 1 / (2 * max n 6)` and vertical semi-axis
`b_n = 1 / max n 6`.

1. **Winding dichotomy**: `θ ↦ J_n(ρ_n e^{i θ}) - d` winds `+1` when `d` lies strictly inside the
   ellipse and `0` when `d` lies strictly outside.
2. **Divisor collision count**: for any finite multiset `(Z, m)` in `{0 < Re w < 1}` separated at
   scale `n`, the squared difference polynomial `(P_Z(J_n(ρ_n u)))^2` is nonvanishing on `S¹` and
   its winding number equals the multiplicity-weighted horizontal collision count
   `∑_{z, w ∈ Z} m(z) m(w) [Im z = Im w ∧ z ≠ w]`.
3. **Wiener–Hopf lift**: unit-normalizing any continuous circle loop yields a unimodular symbol
   whose Wiener–Hopf operator on `L²(ℝ)` is unconditionally Fredholm, has even index whenever the
   loop is a square, and has Fredholm index equal to the winding number whenever the loop is
   zero-free on `S¹`.
4. **Two-scale bifurcation sharpness**: the symmetric quadratic family `(X - 1 / 2)^2 - ε` splits a
   double critical-line zero into a horizontal collision pair `1 / 2 ± √ε`; any fixed stage `n`
   assigns winding `0` for `4 √ε < 1 / max n 6` (proving no single-scale contour suffices) while
   advancing `n` past the splitting scale jumps the winding to `2`.
-/

set_option autoImplicit false

open Complex Set
open scoped BigOperators Classical Polynomial

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Two-scale Zhukovsky ellipse parameters -/

/-- Totalized Zhukovsky stage `max n 6`, guaranteeing `0 < b_n < a_n < 1 / 2` for every `n : ℕ`. -/
def zhukovskyStage (n : ℕ) : ℕ := max n 6

theorem six_le_zhukovskyStage (n : ℕ) : 6 ≤ zhukovskyStage n := le_max_right n 6

theorem le_zhukovskyStage (n : ℕ) : n ≤ zhukovskyStage n := le_max_left n 6

theorem zhukovskyStage_eq_self {n : ℕ} (hn : 6 ≤ n) : zhukovskyStage n = n := max_eq_left hn

theorem six_le_zhukovskyStage_real (n : ℕ) : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := by
  exact_mod_cast six_le_zhukovskyStage n

theorem zhukovskyStage_pos (n : ℕ) : (0 : ℝ) < (zhukovskyStage n : ℝ) := by
  linarith [six_le_zhukovskyStage_real n]

/-- Horizontal semi-axis `a_n = 1 / 2 - 1 / (2 * max n 6)`. -/
def zhukovskyMajorAxis (n : ℕ) : ℝ :=
  1 / 2 - 1 / (2 * (zhukovskyStage n : ℝ))

/-- Vertical semi-axis `b_n = 1 / max n 6`. -/
def zhukovskyMinorAxis (n : ℕ) : ℝ :=
  1 / (zhukovskyStage n : ℝ)

theorem zhukovskyMinorAxis_pos (n : ℕ) : 0 < zhukovskyMinorAxis n :=
  one_div_pos.mpr (zhukovskyStage_pos n)

theorem zhukovskyMinorAxis_le_sixth (n : ℕ) : zhukovskyMinorAxis n ≤ 1 / 6 := by
  unfold zhukovskyMinorAxis
  exact one_div_le_one_div_of_le (by norm_num) (six_le_zhukovskyStage_real n)

theorem five_twelfths_le_zhukovskyMajorAxis (n : ℕ) : 5 / 12 ≤ zhukovskyMajorAxis n := by
  unfold zhukovskyMajorAxis
  have h : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 12 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    linarith [six_le_zhukovskyStage_real n]
  linarith

theorem zhukovskyMinorAxis_lt_majorAxis (n : ℕ) :
    zhukovskyMinorAxis n < zhukovskyMajorAxis n := by
  linarith [zhukovskyMinorAxis_le_sixth n, five_twelfths_le_zhukovskyMajorAxis n]

theorem zhukovskyMajorAxis_pos (n : ℕ) : 0 < zhukovskyMajorAxis n :=
  (zhukovskyMinorAxis_pos n).trans (zhukovskyMinorAxis_lt_majorAxis n)

theorem zhukovskyMajorAxis_lt_half (n : ℕ) : zhukovskyMajorAxis n < 1 / 2 := by
  unfold zhukovskyMajorAxis
  have h : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) :=
    one_div_pos.mpr (mul_pos (by norm_num) (zhukovskyStage_pos n))
  linarith

theorem zhukovskyAxis_sq_sub_pos (n : ℕ) :
    0 < zhukovskyMajorAxis n ^ 2 - zhukovskyMinorAxis n ^ 2 := by
  have ha := zhukovskyMajorAxis_pos n
  have hb := zhukovskyMinorAxis_pos n
  have hab := zhukovskyMinorAxis_lt_majorAxis n
  nlinarith

/-- Focal semi-distance `c_n = √(a_n² - b_n²)`. -/
def zhukovskyFocal (n : ℕ) : ℝ :=
  Real.sqrt (zhukovskyMajorAxis n ^ 2 - zhukovskyMinorAxis n ^ 2)

theorem zhukovskyFocal_pos (n : ℕ) : 0 < zhukovskyFocal n :=
  Real.sqrt_pos.mpr (zhukovskyAxis_sq_sub_pos n)

theorem zhukovskyFocal_sq (n : ℕ) :
    zhukovskyFocal n ^ 2 = zhukovskyMajorAxis n ^ 2 - zhukovskyMinorAxis n ^ 2 :=
  Real.sq_sqrt (zhukovskyAxis_sq_sub_pos n).le

/-- Conformal Laurent radius `ρ_n = (a_n + b_n) / c_n > 1`. -/
def zhukovskyRadius (n : ℕ) : ℝ :=
  (zhukovskyMajorAxis n + zhukovskyMinorAxis n) / zhukovskyFocal n

theorem zhukovskyRadius_pos (n : ℕ) : 0 < zhukovskyRadius n :=
  div_pos (add_pos (zhukovskyMajorAxis_pos n) (zhukovskyMinorAxis_pos n)) (zhukovskyFocal_pos n)

theorem one_lt_zhukovskyRadius (n : ℕ) : 1 < zhukovskyRadius n := by
  rw [zhukovskyRadius, one_lt_div (zhukovskyFocal_pos n)]
  have hc := zhukovskyFocal_sq n
  have hc0 := (zhukovskyFocal_pos n).le
  have ha := zhukovskyMajorAxis_pos n
  have hb := zhukovskyMinorAxis_pos n
  nlinarith

theorem zhukovskyFocal_mul_radius (n : ℕ) :
    zhukovskyFocal n * zhukovskyRadius n = zhukovskyMajorAxis n + zhukovskyMinorAxis n :=
  mul_div_cancel₀ _ (zhukovskyFocal_pos n).ne'

theorem zhukovskyFocal_mul_inv_radius (n : ℕ) :
    zhukovskyFocal n * (zhukovskyRadius n)⁻¹ = zhukovskyMajorAxis n - zhukovskyMinorAxis n := by
  have hsum : zhukovskyMajorAxis n + zhukovskyMinorAxis n ≠ 0 :=
    (add_pos (zhukovskyMajorAxis_pos n) (zhukovskyMinorAxis_pos n)).ne'
  have hc : zhukovskyFocal n ≠ 0 := (zhukovskyFocal_pos n).ne'
  rw [zhukovskyRadius, inv_div]
  calc zhukovskyFocal n * (zhukovskyFocal n / (zhukovskyMajorAxis n + zhukovskyMinorAxis n))
      = zhukovskyFocal n ^ 2 / (zhukovskyMajorAxis n + zhukovskyMinorAxis n) := by ring
    _ = (zhukovskyMajorAxis n ^ 2 - zhukovskyMinorAxis n ^ 2) /
          (zhukovskyMajorAxis n + zhukovskyMinorAxis n) := by rw [zhukovskyFocal_sq]
    _ = zhukovskyMajorAxis n - zhukovskyMinorAxis n := by
        field_simp [hsum]
        ring

theorem zhukovskyAxis_major_identity (n : ℕ) :
    (zhukovskyFocal n / 2) * (zhukovskyRadius n + (zhukovskyRadius n)⁻¹) =
      zhukovskyMajorAxis n := by
  have h1 := zhukovskyFocal_mul_radius n
  have h2 := zhukovskyFocal_mul_inv_radius n
  linarith

theorem zhukovskyAxis_minor_identity (n : ℕ) :
    (zhukovskyFocal n / 2) * (zhukovskyRadius n - (zhukovskyRadius n)⁻¹) =
      zhukovskyMinorAxis n := by
  have h1 := zhukovskyFocal_mul_radius n
  have h2 := zhukovskyFocal_mul_inv_radius n
  linarith

/-! ## §2 The Zhukovsky Laurent map and ellipse loop -/

/-- The centered Zhukovsky Laurent map `z ↦ 1 / 2 + (c_n / 2) * (z + z⁻¹)`. -/
def zhukovskyMap (n : ℕ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + ((zhukovskyFocal n : ℂ) / 2) * (z + z⁻¹)

/-- Restriction of the Zhukovsky Laurent map to `|z| = ρ_n`, viewed in `C(UnitCircle, ℂ)`. -/
def zhukovskyLoop (n : ℕ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := zhukovskyMap n ((zhukovskyRadius n : ℂ) * (u : ℂ))
  continuous_toFun := by
    have hr : ((zhukovskyRadius n : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
    have hmul : Continuous (fun u : HTGeometry.UnitCircle => (zhukovskyRadius n : ℂ) * (u : ℂ)) :=
      continuous_const.mul continuous_subtype_val
    have hne : ∀ u : HTGeometry.UnitCircle, (zhukovskyRadius n : ℂ) * (u : ℂ) ≠ 0 := by
      intro u
      refine mul_ne_zero hr ?_
      intro hu
      have hnorm := HTGeometry.norm_coe_unitCircle u
      rw [hu, norm_zero] at hnorm
      exact zero_ne_one hnorm
    unfold zhukovskyMap
    exact continuous_const.add (continuous_const.mul (hmul.add (hmul.inv₀ hne)))

/-- Normalized quadratic form `(Re w - 1 / 2)² / a_n² + (Im w)² / b_n²` of the `n`-th ellipse. -/
def zhukovskyEllipseForm (n : ℕ) (w : ℂ) : ℝ :=
  (w.re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 + w.im ^ 2 / zhukovskyMinorAxis n ^ 2

theorem zhukovskyLoop_circleExp (n : ℕ) (θ : ℝ) :
    zhukovskyLoop n (HTGeometry.circleExp θ) =
      (1 / 2 : ℂ) + ((zhukovskyMajorAxis n * Real.cos θ : ℝ) : ℂ) +
        ((zhukovskyMinorAxis n * Real.sin θ : ℝ) : ℂ) * I := by
  change zhukovskyMap n ((zhukovskyRadius n : ℂ) * Complex.exp ((θ : ℂ) * I)) = _
  unfold zhukovskyMap
  have hinv : ((zhukovskyRadius n : ℂ) * Complex.exp ((θ : ℂ) * I))⁻¹ =
      ((zhukovskyRadius n : ℂ))⁻¹ * Complex.exp ((-(θ : ℂ)) * I) := by
    rw [mul_inv, ← Complex.exp_neg]
    congr 2
    ring
  rw [hinv, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hmaj : (((zhukovskyFocal n / 2) *
      (zhukovskyRadius n + (zhukovskyRadius n)⁻¹) : ℝ) : ℂ) = (zhukovskyMajorAxis n : ℂ) := by
    exact_mod_cast zhukovskyAxis_major_identity n
  have hmin : (((zhukovskyFocal n / 2) *
      (zhukovskyRadius n - (zhukovskyRadius n)⁻¹) : ℝ) : ℂ) = (zhukovskyMinorAxis n : ℂ) := by
    exact_mod_cast zhukovskyAxis_minor_identity n
  push_cast at hmaj hmin
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  linear_combination (Real.cos θ : ℂ) * hmaj + (Real.sin θ : ℂ) * I * hmin

theorem zhukovskyLoop_circleExp_re (n : ℕ) (θ : ℝ) :
    (zhukovskyLoop n (HTGeometry.circleExp θ)).re =
      1 / 2 + zhukovskyMajorAxis n * Real.cos θ := by
  have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  rw [zhukovskyLoop_circleExp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, h12]
  ring

theorem zhukovskyLoop_circleExp_im (n : ℕ) (θ : ℝ) :
    (zhukovskyLoop n (HTGeometry.circleExp θ)).im =
      zhukovskyMinorAxis n * Real.sin θ := by
  have h12 : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [zhukovskyLoop_circleExp]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, h12]
  ring

/-- Every point of `zhukovskyLoop n` lies on the level curve `zhukovskyEllipseForm n = 1`. -/
theorem zhukovskyEllipseForm_loop (n : ℕ) (u : HTGeometry.UnitCircle) :
    zhukovskyEllipseForm n (zhukovskyLoop n u) = 1 := by
  rw [← HTGeometry.circleExp_arg u]
  set θ := Complex.arg (u : ℂ)
  unfold zhukovskyEllipseForm
  rw [zhukovskyLoop_circleExp_re, zhukovskyLoop_circleExp_im]
  have ha : zhukovskyMajorAxis n ≠ 0 := (zhukovskyMajorAxis_pos n).ne'
  have hb : zhukovskyMinorAxis n ≠ 0 := (zhukovskyMinorAxis_pos n).ne'
  have hcs := Real.cos_sq_add_sin_sq θ
  field_simp [ha, hb]
  nlinarith

theorem zhukovskyLoop_sub_ne_zero {n : ℕ} {d : ℂ} (hd : zhukovskyEllipseForm n d ≠ 1)
    (u : HTGeometry.UnitCircle) :
    zhukovskyLoop n u - d ≠ 0 := by
  intro h
  exact hd (by rw [← sub_eq_zero.mp h, zhukovskyEllipseForm_loop])

theorem isLoop_zhukovsky_sub {n : ℕ} {d : ℂ} (hd : zhukovskyEllipseForm n d ≠ 1) :
    _root_.RHTower.IsLoop (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - d)
      0 (2 * Real.pi) where
  continuous := ((zhukovskyLoop n).continuous.comp HTGeometry.continuous_circleExp).sub
    continuous_const
  nonzero θ := zhukovskyLoop_sub_ne_zero hd _
  closed := by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]

theorem norm_zhukovskyLoop_sub_half_le (n : ℕ) (u : HTGeometry.UnitCircle) :
    ‖zhukovskyLoop n u - (1 / 2 : ℂ)‖ ≤ zhukovskyMajorAxis n + zhukovskyMinorAxis n := by
  rw [← HTGeometry.circleExp_arg u]
  set θ := Complex.arg (u : ℂ)
  have hsub : zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ) =
      ((zhukovskyMajorAxis n * Real.cos θ : ℝ) : ℂ) +
        ((zhukovskyMinorAxis n * Real.sin θ : ℝ) : ℂ) * I := by
    rw [zhukovskyLoop_circleExp]; ring
  rw [hsub]
  calc ‖((zhukovskyMajorAxis n * Real.cos θ : ℝ) : ℂ) +
          ((zhukovskyMinorAxis n * Real.sin θ : ℝ) : ℂ) * I‖
      ≤ ‖((zhukovskyMajorAxis n * Real.cos θ : ℝ) : ℂ)‖ +
          ‖((zhukovskyMinorAxis n * Real.sin θ : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = |zhukovskyMajorAxis n * Real.cos θ| + |zhukovskyMinorAxis n * Real.sin θ| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ zhukovskyMajorAxis n * 1 + zhukovskyMinorAxis n * 1 := by
        rw [abs_mul, abs_mul, abs_of_pos (zhukovskyMajorAxis_pos n),
          abs_of_pos (zhukovskyMinorAxis_pos n)]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (zhukovskyMajorAxis_pos n).le)
          (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (zhukovskyMinorAxis_pos n).le)
    _ = zhukovskyMajorAxis n + zhukovskyMinorAxis n := by ring

/-! ## §3 Winding dichotomy for the Zhukovsky ellipse -/

private def clampUnit (σ : ℝ) : ℝ := max 0 (min 1 σ)

private lemma continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma clampUnit_nonneg (σ : ℝ) : 0 ≤ clampUnit σ := le_max_left 0 _

private lemma clampUnit_le_one (σ : ℝ) : clampUnit σ ≤ 1 :=
  max_le (by norm_num) (min_le_left 1 σ)

private lemma clampUnit_zero : clampUnit 0 = 0 := by simp [clampUnit]

private lemma clampUnit_one : clampUnit 1 = 1 := by simp [clampUnit]

private lemma zhukovskyEllipseForm_scale_center (n : ℕ) (d : ℂ) (t : ℝ) :
    zhukovskyEllipseForm n ((1 / 2 : ℂ) + (t : ℂ) * (d - (1 / 2 : ℂ))) =
      t ^ 2 * zhukovskyEllipseForm n d := by
  unfold zhukovskyEllipseForm
  have hre : ((1 / 2 : ℂ) + (t : ℂ) * (d - (1 / 2 : ℂ))).re - 1 / 2 = t * (d.re - 1 / 2) := by
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
  have him : ((1 / 2 : ℂ) + (t : ℂ) * (d - (1 / 2 : ℂ))).im = t * d.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
  rw [hre, him]
  ring

/-- At the center `d = 1 / 2`, the Zhukovsky loop winds once. -/
theorem windingNumber_zhukovsky_center (n : ℕ) :
    _root_.RHTower.windingNumber
      (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ)) 0 (2 * Real.pi) = 1 := by
  set a := zhukovskyMajorAxis n
  set b := zhukovskyMinorAxis n
  have ha : 0 < a := zhukovskyMajorAxis_pos n
  have hb : 0 < b := zhukovskyMinorAxis_pos n
  let A : ℝ → ℝ := fun σ => (1 - clampUnit σ) * a + clampUnit σ
  let B : ℝ → ℝ := fun σ => (1 - clampUnit σ) * b + clampUnit σ
  have hApos : ∀ σ, 0 < A σ := fun σ => by
    have h0 := clampUnit_nonneg σ
    have h1 := clampUnit_le_one σ
    dsimp only [A]
    rcases eq_or_lt_of_le h0 with hc0 | hcpos
    · rw [← hc0]; linarith
    · linarith [mul_nonneg (sub_nonneg.mpr h1) ha.le]
  have hBpos : ∀ σ, 0 < B σ := fun σ => by
    have h0 := clampUnit_nonneg σ
    have h1 := clampUnit_le_one σ
    dsimp only [B]
    rcases eq_or_lt_of_le h0 with hc0 | hcpos
    · rw [← hc0]; linarith
    · linarith [mul_nonneg (sub_nonneg.mpr h1) hb.le]
  let H : ℝ → ℝ → ℂ := fun σ θ =>
    ((A σ * Real.cos θ : ℝ) : ℂ) + ((B σ * Real.sin θ : ℝ) : ℂ) * I
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    have hAc : Continuous A := ((continuous_const.sub continuous_clampUnit).mul continuous_const).add
      continuous_clampUnit
    have hBc : Continuous B := ((continuous_const.sub continuous_clampUnit).mul continuous_const).add
      continuous_clampUnit
    exact (Complex.continuous_ofReal.comp ((hAc.comp continuous_fst).mul
      (Real.continuous_cos.comp continuous_snd))).add
      ((Complex.continuous_ofReal.comp ((hBc.comp continuous_fst).mul
        (Real.continuous_sin.comp continuous_snd))).mul continuous_const)
  have hH0 : ∀ σ θ, H σ θ ≠ 0 := by
    intro σ θ hzero
    have hre : A σ * Real.cos θ = 0 := by
      have h := congrArg Complex.re hzero
      simp only [H, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, Complex.zero_re] at h
      linarith
    have him : B σ * Real.sin θ = 0 := by
      have h := congrArg Complex.im hzero
      simp only [H, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.I_im, Complex.zero_im] at h
      linarith
    have hcos : Real.cos θ = 0 := (mul_eq_zero.mp hre).resolve_left (hApos σ).ne'
    have hsin : Real.sin θ = 0 := (mul_eq_zero.mp him).resolve_left (hBpos σ).ne'
    have hcs := Real.cos_sq_add_sin_sq θ
    rw [hcos, hsin] at hcs
    norm_num at hcs
  have hHloop : ∀ σ, H σ 0 = H σ (2 * Real.pi) := by
    intro σ
    dsimp only [H]
    rw [Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
  have h0 : ∀ θ, H 0 θ = zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ) := by
    intro θ
    rw [zhukovskyLoop_circleExp]
    dsimp only [H, A, B, a, b]
    rw [clampUnit_zero]
    simp only [sub_zero, one_mul, add_zero]
    ring
  have h1 : ∀ θ, H 1 θ = ↑(1 : ℝ) * Complex.exp (I * (θ : ℂ)) := by
    intro θ
    rw [mul_comm I (θ : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp only [H, A, B]
    rw [clampUnit_one]
    simp only [sub_self, zero_mul, zero_add, one_mul, Complex.ofReal_one]
  rw [_root_.RHTower.windingNumber_of_homotopic H hHc hH0 hHloop h0 h1]
  exact _root_.RHTower.windingNumber_scaled_circle zero_lt_one

/-- **Interior winding law.** Every point strictly inside the `n`-th Zhukovsky ellipse winds `+1`. -/
theorem windingNumber_zhukovsky_of_lt_one {n : ℕ} {d : ℂ}
    (hd : zhukovskyEllipseForm n d < 1) :
    _root_.RHTower.windingNumber
      (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - d) 0 (2 * Real.pi) = 1 := by
  let H : ℝ → ℝ → ℂ := fun σ θ =>
    zhukovskyLoop n (HTGeometry.circleExp θ) -
      ((1 / 2 : ℂ) + (clampUnit σ : ℂ) * (d - (1 / 2 : ℂ)))
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) :=
    ((zhukovskyLoop n).continuous.comp (HTGeometry.continuous_circleExp.comp continuous_snd)).sub
      (continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_clampUnit.comp continuous_fst)).mul
          continuous_const))
  have hH0 : ∀ σ θ, H σ θ ≠ 0 := by
    intro σ θ
    apply zhukovskyLoop_sub_ne_zero
    rw [zhukovskyEllipseForm_scale_center]
    have hsq : clampUnit σ ^ 2 ≤ 1 := by
      have h0 := clampUnit_nonneg σ
      have h1 := clampUnit_le_one σ
      nlinarith
    have hform_nn : 0 ≤ zhukovskyEllipseForm n d := by
      unfold zhukovskyEllipseForm
      positivity
    have hlt : clampUnit σ ^ 2 * zhukovskyEllipseForm n d < 1 := by
      rcases eq_or_lt_of_le hform_nn with h0' | hpos'
      · rw [← h0', mul_zero]; norm_num
      · exact (mul_le_of_le_one_left hpos'.le hsq).trans_lt hd
    exact hlt.ne
  have hHloop : ∀ σ, H σ 0 = H σ (2 * Real.pi) := by
    intro σ
    simp only [H, ← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have h0 : ∀ θ, H 0 θ = zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ) := by
    intro θ
    simp [H, clampUnit_zero]
  have h1 : ∀ θ, H 1 θ = zhukovskyLoop n (HTGeometry.circleExp θ) - d := by
    intro θ
    simp [H, clampUnit_one]
  rw [← _root_.RHTower.windingNumber_of_homotopic H hHc hH0 hHloop h0 h1]
  exact windingNumber_zhukovsky_center n

/-- **Exterior winding law.** Every point strictly outside the `n`-th Zhukovsky ellipse winds `0`. -/
theorem windingNumber_zhukovsky_of_gt_one {n : ℕ} {d : ℂ}
    (hd : 1 < zhukovskyEllipseForm n d) :
    _root_.RHTower.windingNumber
      (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - d) 0 (2 * Real.pi) = 0 := by
  have hd_ne : d - (1 / 2 : ℂ) ≠ 0 := by
    intro h0
    have hd_eq : d = (1 / 2 : ℂ) := sub_eq_zero.mp h0
    rw [hd_eq] at hd
    unfold zhukovskyEllipseForm at hd
    norm_num at hd
  have hnorm_pos : 0 < ‖d - (1 / 2 : ℂ)‖ := norm_pos_iff.mpr hd_ne
  set S : ℝ := (zhukovskyMajorAxis n + zhukovskyMinorAxis n + 1) / ‖d - (1 / 2 : ℂ)‖
  have hS_pos : 0 < S := div_pos
    (by linarith [zhukovskyMajorAxis_pos n, zhukovskyMinorAxis_pos n]) hnorm_pos
  let ray : ℝ → ℝ := fun σ => 1 + clampUnit σ * S
  let dFar : ℂ := (1 / 2 : ℂ) + ((1 + S : ℝ) : ℂ) * (d - (1 / 2 : ℂ))
  let H : ℝ → ℝ → ℂ := fun σ θ =>
    zhukovskyLoop n (HTGeometry.circleExp θ) -
      ((1 / 2 : ℂ) + (ray σ : ℂ) * (d - (1 / 2 : ℂ)))
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    have hray : Continuous ray := continuous_const.add (continuous_clampUnit.mul continuous_const)
    exact ((zhukovskyLoop n).continuous.comp
      (HTGeometry.continuous_circleExp.comp continuous_snd)).sub
      (continuous_const.add
        ((Complex.continuous_ofReal.comp (hray.comp continuous_fst)).mul continuous_const))
  have hH0 : ∀ σ θ, H σ θ ≠ 0 := by
    intro σ θ
    apply zhukovskyLoop_sub_ne_zero
    rw [zhukovskyEllipseForm_scale_center]
    have hray1 : 1 ≤ ray σ := by
      dsimp [ray]
      nlinarith [clampUnit_nonneg σ, hS_pos]
    have hsq : 1 ≤ ray σ ^ 2 := by nlinarith
    have hgt : 1 < ray σ ^ 2 * zhukovskyEllipseForm n d := by nlinarith
    exact hgt.ne'
  have hHloop : ∀ σ, H σ 0 = H σ (2 * Real.pi) := by
    intro σ
    simp only [H, ← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have h0 : ∀ θ, H 0 θ = zhukovskyLoop n (HTGeometry.circleExp θ) - d := by
    intro θ
    simp [H, ray, clampUnit_zero]
  have h1 : ∀ θ, H 1 θ = zhukovskyLoop n (HTGeometry.circleExp θ) - dFar := by
    intro θ
    simp [H, dFar, ray, clampUnit_one]
  rw [_root_.RHTower.windingNumber_of_homotopic H hHc hH0 hHloop h0 h1]
  -- At `dFar`, `‖dFar - 1 / 2‖ > a_n + b_n ≥ ‖zhukovskyLoop n u - 1 / 2‖`.
  have hfar_norm : zhukovskyMajorAxis n + zhukovskyMinorAxis n < ‖(1 / 2 : ℂ) - dFar‖ := by
    have heq : (1 / 2 : ℂ) - dFar = -(((1 + S : ℝ) : ℂ) * (d - (1 / 2 : ℂ))) := by
      dsimp [dFar]; ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hS_pos])]
    have hmul : (1 + S) * ‖d - (1 / 2 : ℂ)‖ =
        ‖d - (1 / 2 : ℂ)‖ + (zhukovskyMajorAxis n + zhukovskyMinorAxis n + 1) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hnorm_pos.ne']
    linarith [hnorm_pos]
  have hfar_ne : (1 / 2 : ℂ) - dFar ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hfar_norm
    linarith [zhukovskyMajorAxis_pos n, zhukovskyMinorAxis_pos n]
  let q : ℝ → ℂ := fun θ =>
    1 + (zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ)) / ((1 / 2 : ℂ) - dFar)
  have hqc : Continuous q :=
    continuous_const.add
      ((((zhukovskyLoop n).continuous.comp HTGeometry.continuous_circleExp).sub
        continuous_const).div_const _)
  have hqclosed : q 0 = q (2 * Real.pi) := by
    simp only [q, ← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have hqball : ∀ θ, ‖q θ - 1‖ < 1 := by
    intro θ
    have hsub : q θ - 1 =
        (zhukovskyLoop n (HTGeometry.circleExp θ) - (1 / 2 : ℂ)) / ((1 / 2 : ℂ) - dFar) := by
      dsimp [q]; ring
    rw [hsub, norm_div, div_lt_one (norm_pos_iff.mpr hfar_ne)]
    exact (norm_zhukovskyLoop_sub_half_le n _).trans_lt hfar_norm
  have hq_nz : ∀ θ, q θ ≠ 0 := by
    intro θ hzero
    have := hqball θ
    rw [hzero, zero_sub, norm_neg, norm_one] at this
    exact lt_irrefl 1 this
  have hfact : (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - dFar) =
      fun θ => ((1 / 2 : ℂ) - dFar) * q θ := by
    funext θ
    dsimp only [q]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hfar_ne]
    ring
  rw [hfact, _root_.RHTower.windingNumber_mul
    ⟨continuous_const, fun _ => hfar_ne, rfl⟩ ⟨hqc, hq_nz, hqclosed⟩,
    _root_.RHTower.windingNumber_const hfar_ne,
    _root_.RHTower.windingNumber_eq_zero_of_ball1 hqc hqclosed hqball, add_zero]

/-! ## §4 Divisor horizontal-collision winding formula -/

/-- Exact winding count of a critical-strip zero difference `(z - w)` along `zhukovskyLoop n`. -/
theorem windingNumber_zhukovsky_pair_diff {n : ℕ} {z w : ℂ}
    (hw_re : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ w.re) (hz_re : z.re < 1)
    (hre : w.re < z.re → 1 / (2 * (zhukovskyStage n : ℝ)) < z.re - w.re)
    (him : z.im ≠ w.im → 1 / (zhukovskyStage n : ℝ) < |z.im - w.im|) :
    zhukovskyEllipseForm n (z - w) ≠ 1 ∧
      _root_.RHTower.windingNumber
        (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) 0 (2 * Real.pi) =
        if z.im = w.im ∧ w.re < z.re then 1 else 0 := by
  by_cases h_im : z.im = w.im
  · by_cases h_lt : w.re < z.re
    · -- Inside the ellipse: `1 / (2 s) < z.re - w.re < 1 - 1 / (2 s)` and `Im (z - w) = 0`.
      have hlow : 1 / (2 * (zhukovskyStage n : ℝ)) < z.re - w.re := hre h_lt
      have hhigh : z.re - w.re < 1 - 1 / (2 * (zhukovskyStage n : ℝ)) := by linarith
      have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
      have hmid1 : -zhukovskyMajorAxis n < (z - w).re - 1 / 2 := by
        rw [Complex.sub_re]; unfold zhukovskyMajorAxis; linarith
      have hmid2 : (z - w).re - 1 / 2 < zhukovskyMajorAxis n := by
        rw [Complex.sub_re]; unfold zhukovskyMajorAxis; linarith
      have hsq : ((z - w).re - 1 / 2) ^ 2 < zhukovskyMajorAxis n ^ 2 := by nlinarith
      have him0 : (z - w).im = 0 := by rw [Complex.sub_im, h_im, sub_self]
      have hform : zhukovskyEllipseForm n (z - w) < 1 := by
        unfold zhukovskyEllipseForm
        rw [him0]
        have : (0 : ℝ) ^ 2 / zhukovskyMinorAxis n ^ 2 = 0 := by simp
        rw [this, add_zero, div_lt_one (sq_pos_of_pos ha_pos)]
        exact hsq
      exact ⟨hform.ne, by rw [if_pos ⟨h_im, h_lt⟩, windingNumber_zhukovsky_of_lt_one hform]⟩
    · -- `z.re ≤ w.re`: `(z - w).re ≤ 0`, so `((z - w).re - 1/2)^2 ≥ 1/4 > a_n^2`.
      have hle : (z - w).re ≤ 0 := by rw [Complex.sub_re]; linarith
      have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
      have ha_half : zhukovskyMajorAxis n < 1 / 2 := zhukovskyMajorAxis_lt_half n
      have hsq : zhukovskyMajorAxis n ^ 2 < ((z - w).re - 1 / 2) ^ 2 := by nlinarith
      have hform : 1 < zhukovskyEllipseForm n (z - w) := by
        unfold zhukovskyEllipseForm
        have hdiv : 1 < ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
          (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq
        have hnn : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
        linarith
      exact ⟨hform.ne', by
        rw [if_neg (fun h => h_lt h.2), windingNumber_zhukovsky_of_gt_one hform]⟩
  · -- `z.im ≠ w.im`: `|(z - w).im| > b_n`, so `zhukovskyEllipseForm n (z - w) > 1`.
    have hv : zhukovskyMinorAxis n < |z.im - w.im| := him h_im
    have hb_pos : 0 < zhukovskyMinorAxis n := zhukovskyMinorAxis_pos n
    have hsq : zhukovskyMinorAxis n ^ 2 < (z - w).im ^ 2 := by
      have habs : |(z - w).im| = |z.im - w.im| := by rw [Complex.sub_im]
      have h1 : zhukovskyMinorAxis n ^ 2 < |z.im - w.im| ^ 2 :=
        pow_lt_pow_left₀ hv hb_pos.le (by norm_num)
      rwa [← habs, sq_abs] at h1
    have hform : 1 < zhukovskyEllipseForm n (z - w) := by
      unfold zhukovskyEllipseForm
      have hdiv : 1 < (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 :=
        (one_lt_div (sq_pos_of_pos hb_pos)).mpr hsq
      have hnn : 0 ≤ ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 := by positivity
      linarith
    exact ⟨hform.ne', by
      rw [if_neg (fun h => h_im h.1), windingNumber_zhukovsky_of_gt_one hform]⟩

/-- Twice the ordered half-space collision sum equals the full horizontal collision sum. -/
private theorem two_mul_ordered_horizontal_sum_eq (Z : Finset ℂ) (m : ℂ → ℕ) :
    2 * (∑ z ∈ Z, ∑ w ∈ Z,
        (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ w.re < z.re then 1 else 0)) =
      ∑ z ∈ Z, ∑ w ∈ Z,
        (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ z ≠ w then 1 else 0) := by
  have hswap :
      (∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ w.re < z.re then 1 else 0)) =
        ∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ z.re < w.re then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    have him_eq : (w.im = z.im ∧ z.re < w.re) ↔ (z.im = w.im ∧ z.re < w.re) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩
    by_cases h : w.im = z.im ∧ z.re < w.re
    · rw [if_pos h, if_pos (him_eq.mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (him_eq.mpr h'))]; ring
  have htwo :
      2 * (∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ w.re < z.re then 1 else 0)) =
        (∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ w.re < z.re then 1 else 0)) +
        (∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ z.re < w.re then 1 else 0)) := by
    linarith [hswap]
  rw [htwo, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases him : z.im = w.im
  · by_cases hlt : w.re < z.re
    · have hgt : ¬ (z.re < w.re) := not_lt_of_gt hlt
      have hne : z ≠ w := fun h => hlt.ne (congrArg Complex.re h).symm
      rw [if_pos ⟨him, hlt⟩, if_neg (fun h => hgt h.2), if_pos ⟨him, hne⟩]
      ring
    · by_cases hgt : z.re < w.re
      · have hne : z ≠ w := fun h => hgt.ne (congrArg Complex.re h)
        rw [if_neg (fun h => hlt h.2), if_pos ⟨him, hgt⟩, if_pos ⟨him, hne⟩]
        ring
      · have hre_eq : z.re = w.re := le_antisymm (not_lt.mp hlt) (not_lt.mp hgt)
        have heq : z = w := Complex.ext hre_eq him
        rw [if_neg (fun h => hlt h.2), if_neg (fun h => hgt h.2),
          if_neg (fun h => h.2 heq)]
        ring
  · rw [if_neg (fun h => him h.1), if_neg (fun h => him h.1), if_neg (fun h => him h.1)]
    ring

/-- **Divisor collision winding theorem.** For any finite multiset `(Z, m)` in the critical strip
separated at scale `n`, the squared Newton–Girard difference polynomial evaluated on
`zhukovskyLoop n` is everywhere nonvanishing on `UnitCircle` and has winding number equal to the
multiplicity-weighted horizontal collision count. -/
theorem windingNumber_zhukovsky_pairDiffPoly_sq (Z : Finset ℂ) (m : ℂ → ℕ) (n : ℕ)
    (hstrip : ∀ w ∈ Z, 1 / (2 * (zhukovskyStage n : ℝ)) ≤ w.re ∧ w.re < 1)
    (hre : ∀ z ∈ Z, ∀ w ∈ Z, w.re < z.re → 1 / (2 * (zhukovskyStage n : ℝ)) < z.re - w.re)
    (him : ∀ z ∈ Z, ∀ w ∈ Z, z.im ≠ w.im → 1 / (zhukovskyStage n : ℝ) < |z.im - w.im|) :
    let Q := pairDiffPoly (∑ w ∈ Z, m w) (fun r => ∑ w ∈ Z, (m w : ℂ) * w ^ r)
    (∀ u : HTGeometry.UnitCircle, Q.eval (zhukovskyLoop n u) ≠ 0) ∧
      _root_.RHTower.windingNumber
        (fun θ => (Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
        ∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ z ≠ w then 1 else 0) := by
  intro Q
  have heval : ∀ x : ℂ, Q.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (m z * m w) :=
    fun x => eval_pairDiffPoly_eq_finset_prod Z id m rfl (fun _ _ _ => rfl) x
  have hpair : ∀ z ∈ Z, ∀ w ∈ Z,
      zhukovskyEllipseForm n (z - w) ≠ 1 ∧
        _root_.RHTower.windingNumber
          (fun θ => zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) 0 (2 * Real.pi) =
          if z.im = w.im ∧ w.re < z.re then 1 else 0 := by
    intro z hz w hw
    exact windingNumber_zhukovsky_pair_diff (hstrip w hw).1 (hstrip z hz).2
      (hre z hz w hw) (him z hz w hw)
  have hQ_nz : ∀ u : HTGeometry.UnitCircle, Q.eval (zhukovskyLoop n u) ≠ 0 := by
    intro u
    rw [heval]
    refine Finset.prod_ne_zero_iff.mpr fun z hz => Finset.prod_ne_zero_iff.mpr fun w hw => ?_
    exact pow_ne_zero _ (zhukovskyLoop_sub_ne_zero (hpair z hz w hw).1 u)
  refine ⟨hQ_nz, ?_⟩
  have hQ_loop : _root_.RHTower.IsLoop
      (fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) 0 (2 * Real.pi) :=
    ⟨(Q.continuous.comp (zhukovskyLoop n).continuous).comp HTGeometry.continuous_circleExp,
      fun _ => hQ_nz _,
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  rw [_root_.RHTower.windingNumber_pow hQ_loop 2]
  have hfun : (fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) =
      fun θ => ∏ z ∈ Z, ∏ w ∈ Z,
        (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w) := by
    funext θ; exact heval _
  have hinner_loop : ∀ z ∈ Z, ∀ w ∈ Z,
      _root_.RHTower.IsLoop
        (fun θ => (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz w hw
    have hl := isLoop_zhukovsky_sub (hpair z hz w hw).1
    exact ⟨hl.continuous.pow _, fun θ => pow_ne_zero _ (hl.nonzero θ), by simp only [hl.closed]⟩
  have houter_loop : ∀ z ∈ Z,
      _root_.RHTower.IsLoop
        (fun θ => ∏ w ∈ Z, (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz
    refine ⟨continuous_finsetProd Z (fun w hw => (hinner_loop z hz w hw).continuous),
      fun θ => Finset.prod_ne_zero_iff.mpr (fun w hw => (hinner_loop z hz w hw).nonzero θ),
      Finset.prod_congr rfl (fun w hw => (hinner_loop z hz w hw).closed)⟩
  rw [hfun, _root_.RHTower.windingNumber_prod Z _ houter_loop]
  have hsum_eq :
      (∑ z ∈ Z, _root_.RHTower.windingNumber
          (fun θ => ∏ w ∈ Z, (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
          0 (2 * Real.pi)) =
        ∑ z ∈ Z, ∑ w ∈ Z,
          (m z : ℤ) * (m w : ℤ) * (if z.im = w.im ∧ w.re < z.re then 1 else 0) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [_root_.RHTower.windingNumber_prod Z _ (hinner_loop z hz)]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [_root_.RHTower.windingNumber_pow (isLoop_zhukovsky_sub (hpair z hz w hw).1) (m z * m w),
      (hpair z hz w hw).2]
    push_cast
    ring
  rw [hsum_eq]
  simpa using two_mul_ordered_horizontal_sum_eq Z m

/-! ## §5 Rouché polynomial perturbation on the Zhukovsky loop -/

/-- Uniform approximation `< inf |Q|` on `zhukovskyLoop n` preserves nonvanishing and winding. -/
theorem windingNumber_zhukovsky_poly_sq_of_approx (n : ℕ) (P Q : Polynomial ℂ)
    (hQ_nz : ∀ u : HTGeometry.UnitCircle, Q.eval (zhukovskyLoop n u) ≠ 0)
    (happrox : ∀ u : HTGeometry.UnitCircle,
      ‖P.eval (zhukovskyLoop n u) - Q.eval (zhukovskyLoop n u)‖ <
        ‖Q.eval (zhukovskyLoop n u)‖) :
    (∀ u : HTGeometry.UnitCircle, (P.eval (zhukovskyLoop n u)) ^ 2 ≠ 0) ∧
      _root_.RHTower.windingNumber
        (fun θ => (P.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) =
      _root_.RHTower.windingNumber
        (fun θ => (Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) := by
  have hP_nz : ∀ u : HTGeometry.UnitCircle, P.eval (zhukovskyLoop n u) ≠ 0 := by
    intro u h0
    have h := happrox u
    rw [h0, zero_sub, norm_neg] at h
    exact lt_irrefl _ h
  refine ⟨fun u => pow_ne_zero 2 (hP_nz u), ?_⟩
  have hP_loop : _root_.RHTower.IsLoop
      (fun θ => P.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) 0 (2 * Real.pi) :=
    ⟨(P.continuous.comp (zhukovskyLoop n).continuous).comp HTGeometry.continuous_circleExp,
      fun _ => hP_nz _,
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  have hQ_loop : _root_.RHTower.IsLoop
      (fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) 0 (2 * Real.pi) :=
    ⟨(Q.continuous.comp (zhukovskyLoop n).continuous).comp HTGeometry.continuous_circleExp,
      fun _ => hQ_nz _,
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  rw [_root_.RHTower.windingNumber_pow hP_loop 2, _root_.RHTower.windingNumber_pow hQ_loop 2]
  congr 1
  let q : ℝ → ℂ := fun θ =>
    P.eval (zhukovskyLoop n (HTGeometry.circleExp θ)) /
      Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))
  have hqc : Continuous q := hP_loop.continuous.div hQ_loop.continuous hQ_loop.nonzero
  have hqclosed : q 0 = q (2 * Real.pi) := by
    simp only [q, ← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have hqball : ∀ θ, ‖q θ - 1‖ < 1 := by
    intro θ
    have hsub : q θ - 1 =
        (P.eval (zhukovskyLoop n (HTGeometry.circleExp θ)) -
          Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) /
        Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ)) := by
      dsimp [q]
      field_simp [hQ_loop.nonzero θ]
    rw [hsub, norm_div, div_lt_one (norm_pos_iff.mpr (hQ_loop.nonzero θ))]
    exact happrox _
  have hq_loop : _root_.RHTower.IsLoop q 0 (2 * Real.pi) :=
    ⟨hqc, fun θ => div_ne_zero (hP_loop.nonzero θ) (hQ_loop.nonzero θ), hqclosed⟩
  have hfact : (fun θ => P.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) =
      fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ)) * q θ := by
    funext θ
    dsimp [q]
    exact (mul_div_cancel₀ _ (hQ_loop.nonzero θ)).symm
  rw [hfact, _root_.RHTower.windingNumber_mul hQ_loop hq_loop,
    _root_.RHTower.windingNumber_eq_zero_of_ball1 hqc hqclosed hqball, add_zero]

/-! ## §6 Unimodular normalization and Wiener–Hopf Fredholm index -/

/-- Canonical unimodular normalization of a circle loop: `Λ / |Λ|` when zero-free on `S¹`, and `1`
on the singular locus where `Λ` vanishes on `S¹`. -/
def unitNormalizeSymbol (Λ : C(HTGeometry.UnitCircle, ℂ)) : C(HTGeometry.UnitCircle, ℂ) :=
  if h : ∀ u : HTGeometry.UnitCircle, Λ u ≠ 0 then
    ⟨fun u => Λ u / (‖Λ u‖ : ℂ),
      Λ.continuous.div (Complex.continuous_ofReal.comp Λ.continuous.norm)
        (fun u => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (h u)))⟩
  else 1

theorem unitNormalizeSymbol_apply_of_ne_zero {Λ : C(HTGeometry.UnitCircle, ℂ)}
    (h : ∀ u : HTGeometry.UnitCircle, Λ u ≠ 0) (u : HTGeometry.UnitCircle) :
    unitNormalizeSymbol Λ u = Λ u / (‖Λ u‖ : ℂ) := by
  rw [unitNormalizeSymbol, dif_pos h]
  rfl

theorem norm_unitNormalizeSymbol (Λ : C(HTGeometry.UnitCircle, ℂ)) (u : HTGeometry.UnitCircle) :
    ‖unitNormalizeSymbol Λ u‖ = 1 := by
  unfold unitNormalizeSymbol
  split_ifs with h
  · change ‖Λ u / (‖Λ u‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr (h u))]
  · exact norm_one

theorem star_mul_self_unitNormalizeSymbol (Λ : C(HTGeometry.UnitCircle, ℂ)) :
    star (unitNormalizeSymbol Λ) * unitNormalizeSymbol Λ = 1 :=
  (HTGeometry.star_mul_self_eq_one_iff _).mpr (norm_unitNormalizeSymbol Λ)

/-- Every Wiener–Hopf operator attached to `unitNormalizeSymbol Λ` is unconditionally Fredholm. -/
theorem isFredholmOp_wienerHopfLift_unitNormalizeSymbol (Λ : C(HTGeometry.UnitCircle, ℂ)) :
    HTGeometry.IsFredholmOp (HTGeometry.wienerHopfLift (unitNormalizeSymbol Λ)) :=
  (HTGeometry.fredholmIndex_wienerHopfLift_eq_circleWinding
    (star_mul_self_unitNormalizeSymbol Λ)).1

/-- Its Fredholm index unconditionally equals the circle winding of `unitNormalizeSymbol Λ`. -/
theorem fredholmIndex_wienerHopfLift_unitNormalizeSymbol (Λ : C(HTGeometry.UnitCircle, ℂ)) :
    HTGeometry.fredholmIndex (HTGeometry.wienerHopfLift (unitNormalizeSymbol Λ)) =
      HTGeometry.circleWinding (unitNormalizeSymbol Λ) :=
  (HTGeometry.fredholmIndex_wienerHopfLift_eq_circleWinding
    (star_mul_self_unitNormalizeSymbol Λ)).2

/-- When `Λ` is zero-free on `S¹`, `unitNormalizeSymbol Λ` has the same winding number as `Λ`. -/
theorem circleWinding_unitNormalizeSymbol_of_ne_zero {Λ : C(HTGeometry.UnitCircle, ℂ)}
    (h : ∀ u : HTGeometry.UnitCircle, Λ u ≠ 0) :
    HTGeometry.circleWinding (unitNormalizeSymbol Λ) =
      _root_.RHTower.windingNumber (fun θ => Λ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) := by
  unfold HTGeometry.circleWinding
  let r : ℝ → ℂ := fun θ => (‖Λ (HTGeometry.circleExp θ)‖ : ℂ)
  have hr_pos : ∀ θ, 0 < ‖Λ (HTGeometry.circleExp θ)‖ :=
    fun θ => norm_pos_iff.mpr (h _)
  have hr_loop : _root_.RHTower.IsLoop r 0 (2 * Real.pi) :=
    ⟨Complex.continuous_ofReal.comp
        (Λ.continuous.comp HTGeometry.continuous_circleExp).norm,
      fun θ => Complex.ofReal_ne_zero.mpr (hr_pos θ).ne',
      by simp only [r, ← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  have hr_wind : _root_.RHTower.windingNumber r 0 (2 * Real.pi) = 0 := by
    let L : ℝ → ℂ := fun θ => (Real.log ‖Λ (HTGeometry.circleExp θ)‖ : ℂ)
    have hLc : Continuous L := Complex.continuous_ofReal.comp
      ((Λ.continuous.comp HTGeometry.continuous_circleExp).norm.log fun θ => (hr_pos θ).ne')
    have hLe : ∀ θ, Complex.exp (L θ) = r θ := by
      intro θ
      dsimp [L, r]
      rw [← Complex.ofReal_exp, Real.exp_log (hr_pos θ)]
    rw [_root_.RHTower.windingNumber_eq_zero_iff hr_loop hLc hLe]
    simp only [L, ← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have hu_loop : _root_.RHTower.IsLoop
      (fun θ => unitNormalizeSymbol Λ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) :=
    HTGeometry.isLoop_circleSymbol fun u h0 => by
      have := norm_unitNormalizeSymbol Λ u
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  have hfact : (fun θ => Λ (HTGeometry.circleExp θ)) =
      fun θ => r θ * unitNormalizeSymbol Λ (HTGeometry.circleExp θ) := by
    funext θ
    rw [unitNormalizeSymbol_apply_of_ne_zero h]
    dsimp [r]
    exact (mul_div_cancel₀ _ (hr_loop.nonzero θ)).symm
  rw [hfact, _root_.RHTower.windingNumber_mul hr_loop hu_loop, hr_wind, zero_add]

/-- Every squared continuous loop yields an unconditionally even Wiener–Hopf Fredholm index. -/
theorem even_fredholmIndex_unitNormalizeSymbol_sq (Φ : C(HTGeometry.UnitCircle, ℂ)) :
    2 ∣ HTGeometry.fredholmIndex (HTGeometry.wienerHopfLift (unitNormalizeSymbol (Φ ^ 2))) := by
  rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol]
  by_cases h : ∀ u : HTGeometry.UnitCircle, (Φ ^ 2) u ≠ 0
  · rw [circleWinding_unitNormalizeSymbol_of_ne_zero h]
    have hΦ : ∀ u : HTGeometry.UnitCircle, Φ u ≠ 0 := by
      intro u hu
      apply h u
      rw [ContinuousMap.coe_pow, Pi.pow_apply, hu, zero_pow two_ne_zero]
    have hloop : _root_.RHTower.IsLoop (fun θ => Φ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) :=
      HTGeometry.isLoop_circleSymbol hΦ
    have hsq : (fun θ => (Φ ^ 2) (HTGeometry.circleExp θ)) =
        fun θ => (Φ (HTGeometry.circleExp θ)) ^ 2 := by
      funext θ
      rw [ContinuousMap.coe_pow, Pi.pow_apply]
    rw [hsq, _root_.RHTower.windingNumber_pow hloop 2]
    exact dvd_mul_right 2 _
  · unfold HTGeometry.circleWinding
    have hu1 : unitNormalizeSymbol (Φ ^ 2) = 1 := dif_neg h
    rw [hu1]
    change 2 ∣ _root_.RHTower.windingNumber (fun _ => (1 : ℂ)) 0 (2 * Real.pi)
    rw [_root_.RHTower.windingNumber_const one_ne_zero]
    exact dvd_zero 2

/-- Norm-continuity of the Wiener–Hopf operator along any nonvanishing homotopy of loops. -/
theorem fredholmIndex_unitNormalizeSymbol_homotopy_invariant
    (H : C(ℝ × HTGeometry.UnitCircle, ℂ))
    (hH : ∀ (σ : ℝ) (u : HTGeometry.UnitCircle), H (σ, u) ≠ 0) (σ₀ σ₁ : ℝ) :
    HTGeometry.fredholmIndex
        (HTGeometry.wienerHopfLift (unitNormalizeSymbol (H.curry σ₀))) =
      HTGeometry.fredholmIndex
        (HTGeometry.wienerHopfLift (unitNormalizeSymbol (H.curry σ₁))) := by
  let U : C(ℝ × HTGeometry.UnitCircle, ℂ) :=
    ⟨fun p => H p / (‖H p‖ : ℂ),
      H.continuous.div (Complex.continuous_ofReal.comp H.continuous.norm)
        (fun p => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hH p.1 p.2)))⟩
  have hU_eq : ∀ σ : ℝ, U.curry σ = unitNormalizeSymbol (H.curry σ) := by
    intro σ
    ext u
    have hσ : ∀ v : HTGeometry.UnitCircle, H.curry σ v ≠ 0 := fun v => hH σ v
    rw [unitNormalizeSymbol_apply_of_ne_zero hσ]
    rfl
  have hpath : Continuous (fun σ : ℝ => HTGeometry.wienerHopfLift (U.curry σ)) :=
    HTGeometry.continuous_wienerHopfLift.comp U.curry.continuous
  have hfred : ∀ σ : ℝ, HTGeometry.IsFredholmOp (HTGeometry.wienerHopfLift (U.curry σ)) := by
    intro σ
    rw [hU_eq σ]
    exact isFredholmOp_wienerHopfLift_unitNormalizeSymbol _
  have hind := HTGeometry.fredholmIndex_eq_of_continuous hpath hfred σ₀ σ₁
  rwa [hU_eq σ₀, hU_eq σ₁] at hind

/-! ## §7 Multiple-zero bifurcation sharpness of the two-scale Zhukovsky contour -/

/-- Symmetric real-coeff quadratic family `(X - 1 / 2)^2 - ε` modeling bifurcation of a double
critical-line zero at `1 / 2` into an off-line horizontal pair `1 / 2 ± √ε`. -/
def bifurcationPoly (ε : ℝ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C (1 / 2 : ℂ)) ^ 2 - Polynomial.C (ε : ℂ)

theorem bifurcationPoly_functional_symm (ε : ℝ) (z : ℂ) :
    (bifurcationPoly ε).eval (1 - z) = (bifurcationPoly ε).eval z := by
  simp only [bifurcationPoly, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem bifurcationPoly_zero_roots (z : ℂ) :
    (bifurcationPoly 0).eval z = 0 ↔ z = (1 / 2 : ℂ) := by
  simp only [bifurcationPoly, Complex.ofReal_zero, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_zero, sq_eq_zero_iff, sub_eq_zero]

/-- If every pairwise difference `z - w` (`z, w ∈ Z`) lies strictly outside the `n`-th Zhukovsky
ellipse, then the squared Newton–Girard difference polynomial is nonvanishing on `zhukovskyLoop n`
and has winding number `0`. -/
theorem windingNumber_zhukovsky_pairDiffPoly_sq_eq_zero_of_gt_one
    (Z : Finset ℂ) (m : ℂ → ℕ) (n : ℕ)
    (hext : ∀ z ∈ Z, ∀ w ∈ Z, 1 < zhukovskyEllipseForm n (z - w)) :
    let Q := pairDiffPoly (∑ w ∈ Z, m w) (fun r => ∑ w ∈ Z, (m w : ℂ) * w ^ r)
    (∀ u : HTGeometry.UnitCircle, Q.eval (zhukovskyLoop n u) ≠ 0) ∧
      _root_.RHTower.windingNumber
        (fun θ => (Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) = 0 := by
  intro Q
  have heval : ∀ x : ℂ, Q.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (m z * m w) :=
    fun x => eval_pairDiffPoly_eq_finset_prod Z id m rfl (fun _ _ _ => rfl) x
  have hQ_nz : ∀ u : HTGeometry.UnitCircle, Q.eval (zhukovskyLoop n u) ≠ 0 := by
    intro u
    rw [heval]
    refine Finset.prod_ne_zero_iff.mpr fun z hz => Finset.prod_ne_zero_iff.mpr fun w hw => ?_
    exact pow_ne_zero _ (zhukovskyLoop_sub_ne_zero (hext z hz w hw).ne' u)
  refine ⟨hQ_nz, ?_⟩
  have hQ_loop : _root_.RHTower.IsLoop
      (fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) 0 (2 * Real.pi) :=
    ⟨(Q.continuous.comp (zhukovskyLoop n).continuous).comp HTGeometry.continuous_circleExp,
      fun _ => hQ_nz _,
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  rw [_root_.RHTower.windingNumber_pow hQ_loop 2]
  have hfun : (fun θ => Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) =
      fun θ => ∏ z ∈ Z, ∏ w ∈ Z,
        (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w) := by
    funext θ; exact heval _
  have hinner_loop : ∀ z ∈ Z, ∀ w ∈ Z,
      _root_.RHTower.IsLoop
        (fun θ => (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz w hw
    have hl := isLoop_zhukovsky_sub (hext z hz w hw).ne'
    exact ⟨hl.continuous.pow _, fun θ => pow_ne_zero _ (hl.nonzero θ), by simp only [hl.closed]⟩
  have houter_loop : ∀ z ∈ Z,
      _root_.RHTower.IsLoop
        (fun θ => ∏ w ∈ Z, (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
        0 (2 * Real.pi) := by
    intro z hz
    refine ⟨continuous_finsetProd Z (fun w hw => (hinner_loop z hz w hw).continuous),
      fun θ => Finset.prod_ne_zero_iff.mpr (fun w hw => (hinner_loop z hz w hw).nonzero θ),
      Finset.prod_congr rfl (fun w hw => (hinner_loop z hz w hw).closed)⟩
  rw [hfun, _root_.RHTower.windingNumber_prod Z _ houter_loop]
  have hzero_sum : (∑ z ∈ Z, _root_.RHTower.windingNumber
      (fun θ => ∏ w ∈ Z, (zhukovskyLoop n (HTGeometry.circleExp θ) - (z - w)) ^ (m z * m w))
      0 (2 * Real.pi)) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [_root_.RHTower.windingNumber_prod Z _ (hinner_loop z hz)]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [_root_.RHTower.windingNumber_pow (isLoop_zhukovsky_sub (hext z hz w hw).ne') (m z * m w),
      windingNumber_zhukovsky_of_gt_one (hext z hz w hw), mul_zero]
  rw [hzero_sum, mul_zero]

/-- **Two-scale bifurcation sharpness.** For `0 < ε < 1 / 4`, `bifurcationPoly ε` has two distinct
roots `z₊ = 1 / 2 + √ε` and `z₋ = 1 / 2 - √ε` in `(0, 1)` at the same ordinate `0`:
1. If `2 √ε < 1 / (2 * zhukovskyStage n)` (splitting smaller than a fixed stage `n`), then every
   root difference lies strictly outside the `n`-th Zhukovsky ellipse and the squared difference
   polynomial has winding `0` (so no single fixed scale `n` detects all horizontal splittings).
2. Conversely, once `1 / (2 * zhukovskyStage n) < 2 √ε` and
   `1 / (2 * zhukovskyStage n) ≤ 1 / 2 - √ε`, the squared difference polynomial has exact winding
   `2`, recovering the horizontal collision count of `{z₋, z₊}`. -/
theorem twoScale_bifurcation_sharpness (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    let zPlus : ℂ := (1 / 2 : ℂ) + (Real.sqrt ε : ℂ)
    let zMinus : ℂ := (1 / 2 : ℂ) - (Real.sqrt ε : ℂ)
    let Z : Finset ℂ := {zMinus, zPlus}
    let Q := pairDiffPoly (∑ _w ∈ Z, 1) (fun r => ∑ w ∈ Z, (1 : ℂ) * w ^ r)
    (bifurcationPoly ε).eval zPlus = 0 ∧
    (bifurcationPoly ε).eval zMinus = 0 ∧
    zPlus ≠ zMinus ∧ zPlus.im = zMinus.im ∧
    (2 * Real.sqrt ε < 1 / (2 * (zhukovskyStage n : ℝ)) →
      _root_.RHTower.windingNumber
        (fun θ => (Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2)
        0 (2 * Real.pi) = 0) ∧
    (1 / (2 * (zhukovskyStage n : ℝ)) < 2 * Real.sqrt ε →
      1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 2 - Real.sqrt ε →
      _root_.RHTower.windingNumber
        (fun θ => (Q.eval (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2)
        0 (2 * Real.pi) = 2) := by
  obtain ⟨zPlus, hzPlus⟩ : ∃ zPlus : ℂ, zPlus = (1 / 2 : ℂ) + (Real.sqrt ε : ℂ) := ⟨_, rfl⟩
  obtain ⟨zMinus, hzMinus⟩ : ∃ zMinus : ℂ, zMinus = (1 / 2 : ℂ) - (Real.sqrt ε : ℂ) := ⟨_, rfl⟩
  dsimp only
  rw [← hzPlus, ← hzMinus]
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℂ, Z = {zMinus, zPlus} := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨m, hm⟩ : ∃ m : ℂ → ℕ, m = fun _ => 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ,
      Q = pairDiffPoly (∑ _w ∈ Z, 1) (fun r => ∑ w ∈ Z, (1 : ℂ) * w ^ r) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ_m : Q = pairDiffPoly (∑ w ∈ Z, m w) (fun r => ∑ w ∈ Z, (m w : ℂ) * w ^ r) := by
    rw [hQ, hm]
    congr 1
    funext r
    simp only [Nat.cast_one]
  have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
  have hsqrt_sq : (Real.sqrt ε : ℂ) ^ 2 = (ε : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hε0.le]
  have hsqrt_half : Real.sqrt ε < 1 / 2 := by
    have h1 : Real.sqrt ε < Real.sqrt (1 / 4) := Real.sqrt_lt_sqrt hε0.le hε1
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hzPlus_root : (bifurcationPoly ε).eval zPlus = 0 := by
    rw [hzPlus]
    simp only [bifurcationPoly, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, add_sub_cancel_left, hsqrt_sq, sub_self]
  have hzMinus_root : (bifurcationPoly ε).eval zMinus = 0 := by
    rw [hzMinus]
    simp only [bifurcationPoly, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    have hsub : (1 / 2 : ℂ) - (Real.sqrt ε : ℂ) - (1 / 2 : ℂ) = -(Real.sqrt ε : ℂ) := by ring
    rw [hsub, neg_sq, hsqrt_sq, sub_self]
  have hne : zPlus ≠ zMinus := by
    intro h
    have hre := congrArg Complex.re h
    rw [hzPlus, hzMinus] at hre
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, h12] at hre
    linarith
  have him_eq : zPlus.im = zMinus.im := by
    rw [hzPlus, hzMinus]
    simp
  refine ⟨hzPlus_root, hzMinus_root, hne, him_eq, ?_, ?_⟩
  · -- Sub-resolution regime: `2 √ε < 1 / (2 s)` implies every difference is outside `E_n`.
    intro hsmall
    have hext : ∀ z ∈ Z, ∀ w ∈ Z, 1 < zhukovskyEllipseForm n (z - w) := by
      intro z hz w hw
      rw [hZ] at hz hw
      have hre_le : (z - w).re ≤ 2 * Real.sqrt ε := by
        rcases Finset.mem_insert.mp hz with rfl | hz' <;>
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · simp; linarith
        · rw [Finset.mem_singleton.mp hw', hzMinus, hzPlus]
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, h12]
          linarith
        · rw [Finset.mem_singleton.mp hz', hzMinus, hzPlus]
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, h12]
          linarith
        · rw [Finset.mem_singleton.mp hz', Finset.mem_singleton.mp hw']
          simp; linarith
      have ha_pos : 0 < zhukovskyMajorAxis n := zhukovskyMajorAxis_pos n
      have hsub_lt : (z - w).re - 1 / 2 < -zhukovskyMajorAxis n := by
        unfold zhukovskyMajorAxis; linarith
      have hsq : zhukovskyMajorAxis n ^ 2 < ((z - w).re - 1 / 2) ^ 2 := by nlinarith
      unfold zhukovskyEllipseForm
      have hdiv : 1 < ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
        (one_lt_div (sq_pos_of_pos ha_pos)).mpr hsq
      have hnn : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
      linarith
    rw [hQ_m]
    exact (windingNumber_zhukovsky_pairDiffPoly_sq_eq_zero_of_gt_one Z m n hext).2
  · -- Resolved regime: `1 / (2 s) < 2 √ε` and `1 / (2 s) ≤ 1 / 2 - √ε` gives winding `2`.
    intro hres hmargin
    have hstrip : ∀ w ∈ Z, 1 / (2 * (zhukovskyStage n : ℝ)) ≤ w.re ∧ w.re < 1 := by
      intro w hw
      rw [hZ] at hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · rw [hzMinus]
        simp only [Complex.sub_re, Complex.ofReal_re, h12]
        exact ⟨hmargin, by linarith⟩
      · rw [Finset.mem_singleton.mp hw', hzPlus]
        simp only [Complex.add_re, Complex.ofReal_re, h12]
        exact ⟨by linarith, by linarith⟩
    have hre : ∀ z ∈ Z, ∀ w ∈ Z, w.re < z.re →
        1 / (2 * (zhukovskyStage n : ℝ)) < z.re - w.re := by
      intro z hz w hw hlt
      rw [hZ] at hz hw
      rcases Finset.mem_insert.mp hz with rfl | hz' <;>
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact absurd hlt (lt_irrefl _)
      · rw [Finset.mem_singleton.mp hw', hzMinus, hzPlus] at hlt
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, h12] at hlt
        linarith
      · rw [Finset.mem_singleton.mp hz', hzMinus, hzPlus]
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, h12]
        linarith
      · rw [Finset.mem_singleton.mp hz', Finset.mem_singleton.mp hw'] at hlt
        exact absurd hlt (lt_irrefl _)
    have him : ∀ z ∈ Z, ∀ w ∈ Z, z.im ≠ w.im →
        1 / (zhukovskyStage n : ℝ) < |z.im - w.im| := by
      intro z hz w hw hne_im
      exfalso
      apply hne_im
      rw [hZ] at hz hw
      rcases Finset.mem_insert.mp hz with rfl | hz' <;>
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · rfl
      · rw [Finset.mem_singleton.mp hw']; exact him_eq.symm
      · rw [Finset.mem_singleton.mp hz']; exact him_eq
      · rw [Finset.mem_singleton.mp hz', Finset.mem_singleton.mp hw']
    have hwind := (windingNumber_zhukovsky_pairDiffPoly_sq Z m n hstrip hre him).2
    rw [hQ_m, hwind, hZ, hm]
    have hne_mp : zMinus ≠ zPlus := hne.symm
    simp only [Finset.sum_pair hne_mp]
    simp [hne, hne_mp, him_eq]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.windingNumber_zhukovsky_of_lt_one
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.windingNumber_zhukovsky_of_gt_one
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.windingNumber_zhukovsky_pairDiffPoly_sq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.isFredholmOp_wienerHopfLift_unitNormalizeSymbol
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.fredholmIndex_wienerHopfLift_unitNormalizeSymbol
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.circleWinding_unitNormalizeSymbol_of_ne_zero
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.even_fredholmIndex_unitNormalizeSymbol_sq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.twoScale_bifurcation_sharpness
