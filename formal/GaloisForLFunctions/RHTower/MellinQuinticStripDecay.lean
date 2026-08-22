import GaloisForLFunctions.RHTower.MellinQuadraticStripDecay

/-!
# Uniform quintic Mellin decay on a bounded strip

The quadratic strip estimate is enough for vertical integrability but not for
horizontal contours carrying a cubic `L`-function envelope.  This module
constructs the fifth weighted derivative explicitly and supplies its one
integrable majorant on `0 ≤ Re(s) ≤ 3`.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped FourierTransform Topology

namespace RHTower

noncomputable section

/-- A certified abscissa in the strip used by the quintic Mellin bound. -/
structure DeningerMeyerQuinticStripAbscissa where
  value : ℝ
  nonneg : 0 ≤ value
  le_three : value ≤ 3

instance : Coe DeningerMeyerQuinticStripAbscissa ℝ where
  coe sigma := sigma.value

/-- Fifth binomial expansion of the weighted Euler derivative. -/
theorem deningerMeyerWeightedEulerIterate_five
    (g : DeningerMeyerStrongLogTarget) (sigma t : ℝ) :
    deningerMeyerWeightedEulerIterate sigma 5 (g : ℝ → ℂ) t =
      (sigma : ℂ) ^ 5 * (g : ℝ → ℂ) t +
        5 * (sigma : ℂ) ^ 4 * iteratedDeriv 1 (g : ℝ → ℂ) t +
          10 * (sigma : ℂ) ^ 3 * iteratedDeriv 2 (g : ℝ → ℂ) t +
            10 * (sigma : ℂ) ^ 2 * iteratedDeriv 3 (g : ℝ → ℂ) t +
              5 * (sigma : ℂ) * iteratedDeriv 4 (g : ℝ → ℂ) t +
                iteratedDeriv 5 (g : ℝ → ℂ) t := by
  let f : ℝ → ℂ := g
  let F1 : ℝ → ℂ := fun x => (sigma : ℂ) * f x + iteratedDeriv 1 f x
  let F2 : ℝ → ℂ := fun x =>
    (sigma : ℂ) ^ 2 * f x + 2 * (sigma : ℂ) * iteratedDeriv 1 f x + iteratedDeriv 2 f x
  let F3 : ℝ → ℂ := fun x =>
    (sigma : ℂ) ^ 3 * f x + 3 * (sigma : ℂ) ^ 2 * iteratedDeriv 1 f x +
      3 * (sigma : ℂ) * iteratedDeriv 2 f x + iteratedDeriv 3 f x
  let F4 : ℝ → ℂ := fun x =>
    (sigma : ℂ) ^ 4 * f x + 4 * (sigma : ℂ) ^ 3 * iteratedDeriv 1 f x +
      6 * (sigma : ℂ) ^ 2 * iteratedDeriv 2 f x +
        4 * (sigma : ℂ) * iteratedDeriv 3 f x + iteratedDeriv 4 f x
  let F5 : ℝ → ℂ := fun x =>
    (sigma : ℂ) ^ 5 * f x + 5 * (sigma : ℂ) ^ 4 * iteratedDeriv 1 f x +
      10 * (sigma : ℂ) ^ 3 * iteratedDeriv 2 f x +
        10 * (sigma : ℂ) ^ 2 * iteratedDeriv 3 f x +
          5 * (sigma : ℂ) * iteratedDeriv 4 f x + iteratedDeriv 5 f x
  have hd (j : ℕ) : Differentiable ℝ (iteratedDeriv j f) := by
    dsimp [f]
    exact g.property.smooth.differentiable_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top j))
  have hjet (j : ℕ) (x : ℝ) : HasDerivAt (iteratedDeriv j f)
      (iteratedDeriv (j + 1) f x) x := by
    simpa only [iteratedDeriv_succ] using (hd j x).hasDerivAt
  have hterm (c : ℂ) (j : ℕ) (x : ℝ) :
      HasDerivAt (fun y => c * iteratedDeriv j f y)
        (c * iteratedDeriv (j + 1) f x) x :=
    (hjet j x).const_mul c
  have hterm0 (c : ℂ) (x : ℝ) :
      HasDerivAt (fun y => c * f y) (c * iteratedDeriv 1 f x) x := by
    simpa only [iteratedDeriv_zero] using hterm c 0 x
  have hderivF1 (x : ℝ) : deriv F1 x =
      (sigma : ℂ) * iteratedDeriv 1 f x + iteratedDeriv 2 f x := by
    have hsum := (hterm0 (sigma : ℂ) x).add (hterm 1 1 x)
    change deriv ((fun y => (sigma : ℂ) * f y) + fun y => iteratedDeriv 1 f y) x = _
    simpa only [one_mul] using hsum.deriv
  have hderivF2 (x : ℝ) : deriv F2 x =
      (sigma : ℂ) ^ 2 * iteratedDeriv 1 f x +
        2 * (sigma : ℂ) * iteratedDeriv 2 f x + iteratedDeriv 3 f x := by
    have hsum := ((hterm0 ((sigma : ℂ) ^ 2) x).add
      (hterm (2 * (sigma : ℂ)) 1 x)).add (hterm 1 2 x)
    change deriv ((fun y => (sigma : ℂ) ^ 2 * f y) +
      (fun y => 2 * (sigma : ℂ) * iteratedDeriv 1 f y) + fun y => iteratedDeriv 2 f y) x = _
    simpa only [one_mul, add_assoc] using hsum.deriv
  have hderivF3 (x : ℝ) : deriv F3 x =
      (sigma : ℂ) ^ 3 * iteratedDeriv 1 f x +
        3 * (sigma : ℂ) ^ 2 * iteratedDeriv 2 f x +
          3 * (sigma : ℂ) * iteratedDeriv 3 f x + iteratedDeriv 4 f x := by
    have hsum := (((hterm0 ((sigma : ℂ) ^ 3) x).add
      (hterm (3 * (sigma : ℂ) ^ 2) 1 x)).add
        (hterm (3 * (sigma : ℂ)) 2 x)).add (hterm 1 3 x)
    change deriv ((fun y => (sigma : ℂ) ^ 3 * f y) +
      (fun y => 3 * (sigma : ℂ) ^ 2 * iteratedDeriv 1 f y) +
        (fun y => 3 * (sigma : ℂ) * iteratedDeriv 2 f y) + fun y => iteratedDeriv 3 f y) x = _
    simpa only [one_mul, add_assoc] using hsum.deriv
  have hderivF4 (x : ℝ) : deriv F4 x =
      (sigma : ℂ) ^ 4 * iteratedDeriv 1 f x +
        4 * (sigma : ℂ) ^ 3 * iteratedDeriv 2 f x +
          6 * (sigma : ℂ) ^ 2 * iteratedDeriv 3 f x +
            4 * (sigma : ℂ) * iteratedDeriv 4 f x + iteratedDeriv 5 f x := by
    have hsum := ((((hterm0 ((sigma : ℂ) ^ 4) x).add
      (hterm (4 * (sigma : ℂ) ^ 3) 1 x)).add
        (hterm (6 * (sigma : ℂ) ^ 2) 2 x)).add
          (hterm (4 * (sigma : ℂ)) 3 x)).add (hterm 1 4 x)
    change deriv ((fun y => (sigma : ℂ) ^ 4 * f y) +
      (fun y => 4 * (sigma : ℂ) ^ 3 * iteratedDeriv 1 f y) +
        (fun y => 6 * (sigma : ℂ) ^ 2 * iteratedDeriv 2 f y) +
          (fun y => 4 * (sigma : ℂ) * iteratedDeriv 3 f y) + fun y => iteratedDeriv 4 f y) x = _
    simpa only [one_mul, add_assoc] using hsum.deriv
  have hF1 : deningerMeyerWeightedEulerIterate sigma 1 f = F1 := by
    funext x
    simp [deningerMeyerWeightedEulerIterate, deningerMeyerWeightedEuler, F1, iteratedDeriv_one]
  have hF2 : deningerMeyerWeightedEulerIterate sigma 2 f = F2 := by
    rw [show deningerMeyerWeightedEulerIterate sigma 2 f =
      deningerMeyerWeightedEuler sigma (deningerMeyerWeightedEulerIterate sigma 1 f) by rfl, hF1]
    funext x
    simp only [deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hderivF1]
    dsimp [F1, F2]
    ring
  have hF3 : deningerMeyerWeightedEulerIterate sigma 3 f = F3 := by
    rw [show deningerMeyerWeightedEulerIterate sigma 3 f =
      deningerMeyerWeightedEuler sigma (deningerMeyerWeightedEulerIterate sigma 2 f) by rfl, hF2]
    funext x
    simp only [deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hderivF2]
    dsimp [F2, F3]
    ring
  have hF4 : deningerMeyerWeightedEulerIterate sigma 4 f = F4 := by
    rw [show deningerMeyerWeightedEulerIterate sigma 4 f =
      deningerMeyerWeightedEuler sigma (deningerMeyerWeightedEulerIterate sigma 3 f) by rfl, hF3]
    funext x
    simp only [deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hderivF3]
    dsimp [F3, F4]
    ring
  have hF5 : deningerMeyerWeightedEulerIterate sigma 5 f = F5 := by
    rw [show deningerMeyerWeightedEulerIterate sigma 5 f =
      deningerMeyerWeightedEuler sigma (deningerMeyerWeightedEulerIterate sigma 4 f) by rfl, hF4]
    funext x
    simp only [deningerMeyerWeightedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hderivF4]
    dsimp [F4, F5]
    ring
  rw [show (g : ℝ → ℂ) = f by rfl, hF5]

/-- One integrable majorant for all fifth weighted derivatives in the strip. -/
def deningerMeyerQuinticStripMajorant (g : DeningerMeyerStrongLogTarget) (t : ℝ) : ℝ :=
  Real.exp (3 * |t|) *
    (3 ^ 5 * ‖(g : ℝ → ℂ) t‖ + 5 * 3 ^ 4 * ‖iteratedDeriv 1 (g : ℝ → ℂ) t‖ +
      10 * 3 ^ 3 * ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖ +
        10 * 3 ^ 2 * ‖iteratedDeriv 3 (g : ℝ → ℂ) t‖ +
          5 * 3 * ‖iteratedDeriv 4 (g : ℝ → ℂ) t‖ + ‖iteratedDeriv 5 (g : ℝ → ℂ) t‖)

theorem integrable_deningerMeyerQuinticStripMajorant (g : DeningerMeyerStrongLogTarget) :
    Integrable (deningerMeyerQuinticStripMajorant g) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖(g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property 0 3 using 1
    funext t; simp
  have h1 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖iteratedDeriv 1 (g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property.deriv 0 3 using 1
    funext t; simp [iteratedDeriv_one]
  have h2 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property.deriv.deriv 0 3 using 1
    funext t; simp [iteratedDeriv_succ]
  have h3 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖iteratedDeriv 3 (g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property.deriv.deriv.deriv 0 3 using 1
    funext t; simp [iteratedDeriv_succ]
  have h4 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖iteratedDeriv 4 (g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property.deriv.deriv.deriv.deriv 0 3 using 1
    funext t; simp [iteratedDeriv_succ]
  have h5 : Integrable (fun t : ℝ => Real.exp (3 * |t|) * ‖iteratedDeriv 5 (g : ℝ → ℂ) t‖) := by
    convert integrable_deningerMeyerStrongLogAbsMoment g.property.deriv.deriv.deriv.deriv.deriv 0 3 using 1
    funext t; simp [iteratedDeriv_succ]
  apply (h0.const_mul (3 ^ 5)).add ((h1.const_mul (5 * 3 ^ 4)).add
    ((h2.const_mul (10 * 3 ^ 3)).add ((h3.const_mul (10 * 3 ^ 2)).add
      ((h4.const_mul (5 * 3)).add h5)))) |>.congr
  filter_upwards with t
  simp only [deningerMeyerQuinticStripMajorant, Pi.add_apply]
  ring

private theorem norm_iteratedDeriv_five_weightedProfile_le
    (g : DeningerMeyerStrongLogTarget) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma) (hsigma3 : sigma ≤ 3) (t : ℝ) :
    ‖iteratedDeriv 5 (deningerMeyerWeightedLogProfile sigma g) t‖ ≤
      deningerMeyerQuinticStripMajorant g t := by
  rw [iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma 5]
  simp only [deningerMeyerWeightedLogProfile]
  rw [deningerMeyerWeightedEulerIterate_five g sigma t]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hst : sigma * t ≤ 3 * |t| := by
    calc sigma * t ≤ |sigma * t| := le_abs_self _
      _ = sigma * |t| := by rw [abs_mul, abs_of_nonneg hsigma0]
      _ ≤ 3 * |t| := mul_le_mul_of_nonneg_right hsigma3 (abs_nonneg t)
  have hexp : Real.exp (sigma * t) ≤ Real.exp (3 * |t|) := Real.exp_le_exp.mpr hst
  let A : ℂ := (sigma : ℂ)^5 * (g : ℝ → ℂ) t
  let B : ℂ := 5 * (sigma : ℂ)^4 * iteratedDeriv 1 (g : ℝ → ℂ) t
  let C : ℂ := 10 * (sigma : ℂ)^3 * iteratedDeriv 2 (g : ℝ → ℂ) t
  let D : ℂ := 10 * (sigma : ℂ)^2 * iteratedDeriv 3 (g : ℝ → ℂ) t
  let E : ℂ := 5 * (sigma : ℂ) * iteratedDeriv 4 (g : ℝ → ℂ) t
  let F : ℂ := iteratedDeriv 5 (g : ℝ → ℂ) t
  have htri : ‖A + B + C + D + E + F‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖F‖ := by
    calc
      _ ≤ ‖A + B + C + D + E‖ + ‖F‖ := norm_add_le _ _
      _ ≤ (‖A + B + C + D‖ + ‖E‖) + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖A + B + C‖ + ‖D‖) + ‖E‖) + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((‖A + B‖ + ‖C‖) + ‖D‖) + ‖E‖) + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖) + ‖E‖) + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by ring
  have hsum :
      ‖(sigma : ℂ)^5 * (g : ℝ → ℂ) t + 5 * (sigma : ℂ)^4 * iteratedDeriv 1 (g : ℝ → ℂ) t +
        10 * (sigma : ℂ)^3 * iteratedDeriv 2 (g : ℝ → ℂ) t + 10 * (sigma : ℂ)^2 * iteratedDeriv 3 (g : ℝ → ℂ) t +
          5 * (sigma : ℂ) * iteratedDeriv 4 (g : ℝ → ℂ) t + iteratedDeriv 5 (g : ℝ → ℂ) t‖ ≤
      sigma^5 * ‖(g : ℝ → ℂ) t‖ + 5 * sigma^4 * ‖iteratedDeriv 1 (g : ℝ → ℂ) t‖ +
        10 * sigma^3 * ‖iteratedDeriv 2 (g : ℝ → ℂ) t‖ + 10 * sigma^2 * ‖iteratedDeriv 3 (g : ℝ → ℂ) t‖ +
          5 * sigma * ‖iteratedDeriv 4 (g : ℝ → ℂ) t‖ + ‖iteratedDeriv 5 (g : ℝ → ℂ) t‖ := by
    calc
      _ = ‖A + B + C + D + E + F‖ := by rfl
      _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖F‖ := htri
      _ = _ := by
        dsimp [A, B, C, D, E, F]
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hsigma0, norm_ofNat]
  rw [deningerMeyerQuinticStripMajorant]
  calc
    Real.exp (sigma*t) * _ ≤ Real.exp (sigma*t) *
        (sigma^5 * ‖(g : ℝ → ℂ) t‖ + 5*sigma^4*‖iteratedDeriv 1 (g : ℝ → ℂ) t‖ +
          10*sigma^3*‖iteratedDeriv 2 (g : ℝ → ℂ) t‖ + 10*sigma^2*‖iteratedDeriv 3 (g : ℝ → ℂ) t‖ +
            5*sigma*‖iteratedDeriv 4 (g : ℝ → ℂ) t‖ + ‖iteratedDeriv 5 (g : ℝ → ℂ) t‖) := by gcongr
    _ ≤ _ := by
      apply mul_le_mul hexp
      · gcongr
      · positivity
      · positivity

/-- Closed fifth-order uniform strip budget. -/
theorem abs_im_pow_five_mul_norm_deningerMeyerStrongLogMellin_le
    (g : DeningerMeyerStrongLogTarget) (sigma : DeningerMeyerQuinticStripAbscissa) (tau : ℝ) :
    |tau|^5 * ‖deningerMeyerStrongLogMellin g ((sigma.value : ℂ) + (tau : ℂ)*I)‖ ≤
      ∫ t : ℝ, deningerMeyerQuinticStripMajorant g t := by
  have hfive := abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le g 5 sigma.value tau
  have hint := integrable_iteratedDeriv_deningerMeyerWeightedLogProfile g.property sigma.value 5 |>.norm
  exact hfive.trans (integral_mono hint (integrable_deningerMeyerQuinticStripMajorant g) fun t =>
    norm_iteratedDeriv_five_weightedProfile_le g sigma.nonneg sigma.le_three t)

end

end RHTower
