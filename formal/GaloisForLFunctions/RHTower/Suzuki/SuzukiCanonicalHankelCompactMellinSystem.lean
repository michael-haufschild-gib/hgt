import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelCompactMellinDerivative

/-!
# Mellin transform of Suzuki's strong Fredholm differential system

The physical Euler field is integrated by parts against the exact Mellin character.  The proof
works across the countable arithmetic cusp set and uses the reciprocal support gap to remove the
singular endpoint.  Combining this transform identity with the strong `L¹` equation (4.13) yields
the compact-transform differential system at every aperture `a > 1`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Unclamped Mellin density `x^(-1/2+iz)` on the positive half-line. -/
def suzukiMellinDensity (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((-(1 / 2 : ℂ) + I * z) * (Real.log x : ℂ))

/-- Its integration-by-parts primitive weight `x^(1/2+iz)`. -/
def suzukiMellinPrimitiveWeight (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((1 / 2 + I * z) * (Real.log x : ℂ))

theorem suzukiMellinPrimitiveWeight_eq_mul_density
    (z : ℂ) {x : ℝ} (hx : 0 < x) :
    suzukiMellinPrimitiveWeight z x = (x : ℂ) * suzukiMellinDensity z x := by
  rw [suzukiMellinPrimitiveWeight, suzukiMellinDensity,
    show (x : ℂ) = Complex.exp (Real.log x : ℂ) by
      rw [← Complex.ofReal_exp, Real.exp_log hx],
    ← Complex.exp_add]
  congr 1
  ring

theorem hasDerivAt_suzukiMellinPrimitiveWeight
    (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (suzukiMellinPrimitiveWeight z)
      ((1 / 2 + I * z) * suzukiMellinDensity z x) x := by
  have hlogR := Real.hasDerivAt_log hx.ne'
  have hlogC : HasDerivAt (fun y : ℝ => (Real.log y : ℂ))
      ((x⁻¹ : ℝ) : ℂ) x := hlogR.ofReal_comp
  have h := (hlogC.const_mul (1 / 2 + I * z)).cexp
  unfold suzukiMellinPrimitiveWeight
  convert h using 1
  rw [show Complex.exp ((1 / 2 + I * z) * (Real.log x : ℂ)) =
      (x : ℂ) * suzukiMellinDensity z x by
    rw [suzukiMellinDensity,
      show (x : ℂ) = Complex.exp (Real.log x : ℂ) by
        rw [← Complex.ofReal_exp, Real.exp_log hx],
      ← Complex.exp_add]
    congr 1
    ring]
  push_cast
  field_simp [hx.ne']

theorem continuousOn_suzukiMellinDensity_Ici
    (z : ℂ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (suzukiMellinDensity z) (Ici c) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (hc.trans_le hx)
  have hlog : ContinuousAt (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0)
  unfold suzukiMellinDensity
  exact (Complex.continuous_exp.continuousAt.comp
    (continuousAt_const.mul hlog)).continuousWithinAt

theorem continuousOn_suzukiMellinPrimitiveWeight_Ici
    (z : ℂ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (suzukiMellinPrimitiveWeight z) (Ici c) := by
  intro x hx
  exact (hasDerivAt_suzukiMellinPrimitiveWeight z (hc.trans_le hx)).continuousAt.continuousWithinAt

/-- Inside the reciprocal support gap, the spatial Euler field is genuinely zero, not merely
zero almost everywhere. -/
theorem suzukiHankelEulerPhi_eq_zero_of_pos_lt_reciprocal
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx0 : 0 < x) (hxa : x < 1 / a) :
    suzukiHankelEulerPhi epsilon omega a homega ha x = 0 := by
  let P := suzukiHankelPhiGlobal epsilon omega a homega ha
  have hev : P =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hx0 hxa] with y hy
    exact suzukiHankelPhiGlobal_eq_zero_below_reciprocal
      epsilon homega ha hy.1.le hy.2.le
  have hderiv : HasDerivAt P 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev
  rw [suzukiHankelEulerPhi, hderiv.deriv]
  change (x : ℂ) * 0 + (1 / 2 : ℂ) * P x = 0
  rw [show P x = 0 by
    exact suzukiHankelPhiGlobal_eq_zero_below_reciprocal
      epsilon homega ha hx0.le hxa.le]
  ring

/-- Exact Mellin integration by parts for Suzuki's spatial Euler field.  The countable cusp set
`x=n/a` is admitted explicitly, while the reciprocal support gap removes the singular origin. -/
theorem suzukiHankelEulerPhi_compactMellin_integrationByParts
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (haB : a < B) (z : ℂ) :
    (∫ x in (0 : ℝ)..a,
        suzukiClampedMellinWeightValue (1 / B) z x *
          suzukiHankelEulerPhi epsilon omega a homega ha x) =
      (a : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha a *
          suzukiClampedMellinWeightValue (1 / B) z a -
        I * z * suzukiHankelCompactMellin epsilon omega a homega ha z := by
  let c : ℝ := 1 / a
  let P : ℝ → ℂ := suzukiHankelPhiGlobal epsilon omega a homega ha
  let E : ℝ → ℂ := suzukiHankelEulerPhi epsilon omega a homega ha
  let w : ℝ → ℂ := suzukiMellinDensity z
  let v : ℝ → ℂ := suzukiMellinPrimitiveWeight z
  let W : ℝ → ℂ := suzukiClampedMellinWeightValue (1 / B) z
  have hc : 0 < c := by dsimp only [c]; positivity
  have hca : c < a := by
    dsimp only [c]
    have hrecip : 1 / a < 1 := by
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) ha
    linarith
  have hBa : 1 / B < c := by
    dsimp only [c]
    exact one_div_lt_one_div_of_lt (by linarith) haB
  have hPcont : ContinuousOn P (Icc c a) := by
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
      (fun x hx => (hc.le.trans hx.1))
  have hwcont : ContinuousOn w (Icc c a) :=
    (continuousOn_suzukiMellinDensity_Ici z hc).mono (fun _ hx => hx.1)
  have hvcont : ContinuousOn v (Icc c a) :=
    (continuousOn_suzukiMellinPrimitiveWeight_Ici z hc).mono (fun _ hx => hx.1)
  have hPcontU : ContinuousOn P (uIcc c a) := by
    rwa [uIcc_of_le hca.le]
  have hwcontU : ContinuousOn w (uIcc c a) := by
    rwa [uIcc_of_le hca.le]
  have hvcontU : ContinuousOn v (uIcc c a) := by
    rwa [uIcc_of_le hca.le]
  let s : Set ℝ := Set.range fun n : ℕ => (n : ℝ) / a
  have hs : s.Countable := Set.countable_range _
  have hdu : ∀ x ∈ Ioo (min c a) (max c a) \ s,
      HasDerivAt P (deriv P x) x := by
    intro x hx
    have hxIoo : x ∈ Ioo c a := by
      simpa [min_eq_left hca.le, max_eq_right hca.le] using hx.1
    have hxreg : x ∈ SuzukiHankelRegularX a := by
      refine ⟨hc.trans hxIoo.1, ?_⟩
      intro n hxn
      apply hx.2
      exact ⟨n, hxn.symm⟩
    exact ((contDiffAt_one_suzukiHankelPhiGlobal_of_regular
      epsilon homega ha hxreg).differentiableAt (by norm_num)).hasDerivAt
  have hdv : ∀ x ∈ Ioo (min c a) (max c a) \ (∅ : Set ℝ),
      HasDerivAt v ((1 / 2 + I * z) * w x) x := by
    intro x hx
    have hxIoo : x ∈ Ioo c a := by
      simpa [min_eq_left hca.le, max_eq_right hca.le] using hx.1
    exact hasDerivAt_suzukiMellinPrimitiveWeight z (hc.trans hxIoo.1)
  have hE0a : IntervalIntegrable E volume 0 a :=
    intervalIntegrable_suzukiHankelEulerPhi epsilon homega ha
  have hEca : IntervalIntegrable E volume c a := by
    rw [intervalIntegrable_iff] at hE0a ⊢
    exact hE0a.mono_set (by
      rw [uIoc_of_le hca.le, uIoc_of_le (by linarith : 0 ≤ a)]
      intro x hx
      exact ⟨hc.trans hx.1, hx.2⟩)
  have hPint : IntervalIntegrable P volume c a := by
    exact hPcontU.intervalIntegrable
  have hderivPart : IntervalIntegrable
      (fun x => (x : ℂ) * deriv P x) volume c a := by
    have h := hEca.sub (hPint.const_mul (1 / 2 : ℂ))
    apply h.congr
    intro x _
    dsimp only [E, suzukiHankelEulerPhi]
    ring
  have hintUV : IntervalIntegrable (fun x => deriv P x * v x) volume c a := by
    have h := hderivPart.mul_continuousOn hwcontU
    apply h.congr
    intro x hx
    have hxpos : 0 < x := hc.trans_le (by
      rw [uIoc_of_le hca.le] at hx
      exact hx.1.le)
    dsimp only [w, v]
    rw [suzukiMellinPrimitiveWeight_eq_mul_density z hxpos]
    ring
  have hintVU : IntervalIntegrable
      (fun x => P x * ((1 / 2 + I * z) * w x)) volume c a := by
    exact (hPcontU.mul (continuousOn_const.mul hwcontU)).intervalIntegrable
  have hibp := intervalIntegral_integral_mul_deriv_eq_deriv_mul_off_countable
    hs Set.countable_empty hPcontU hvcontU hdu hdv hintUV hintVU
  have hPc : P c = 0 := by
    dsimp only [P, c]
    exact suzukiHankelPhiGlobal_eq_zero_below_reciprocal
      epsilon homega ha (by positivity) le_rfl
  have hcore :
      (∫ x in c..a, w x * E x) =
        (a : ℂ) * P a * w a - I * z * (∫ x in c..a, w x * P x) := by
    have hvA : v a = (a : ℂ) * w a :=
      suzukiMellinPrimitiveWeight_eq_mul_density z (by linarith)
    have hvC : v c = (c : ℂ) * w c :=
      suzukiMellinPrimitiveWeight_eq_mul_density z hc
    rw [hvA, hvC, hPc] at hibp
    change
      (∫ x in c..a, w x * ((x : ℂ) * deriv P x + (1 / 2 : ℂ) * P x)) =
        (a : ℂ) * P a * w a - I * z * (∫ x in c..a, w x * P x)
    calc
      (∫ x in c..a, w x * ((x : ℂ) * deriv P x + (1 / 2 : ℂ) * P x)) =
          (∫ x in c..a, deriv P x * v x) +
            (1 / 2 : ℂ) * (∫ x in c..a, w x * P x) := by
        calc
          (∫ x in c..a,
              w x * ((x : ℂ) * deriv P x + (1 / 2 : ℂ) * P x)) =
              ∫ x in c..a,
                deriv P x * v x + (1 / 2 : ℂ) * (w x * P x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hxpos : 0 < x := by
              rw [uIcc_of_le hca.le] at hx
              exact hc.trans_le hx.1
            change w x * ((x : ℂ) * deriv P x + (1 / 2 : ℂ) * P x) =
              deriv P x * v x + (1 / 2 : ℂ) * (w x * P x)
            rw [show v x = (x : ℂ) * w x by
              exact suzukiMellinPrimitiveWeight_eq_mul_density z hxpos]
            ring
          _ = (∫ x in c..a, deriv P x * v x) +
              (∫ x in c..a, (1 / 2 : ℂ) * (w x * P x)) := by
            exact intervalIntegral.integral_add hintUV
              ((hwcontU.mul hPcontU).intervalIntegrable.const_mul (1 / 2 : ℂ))
          _ = (∫ x in c..a, deriv P x * v x) +
              (1 / 2 : ℂ) * (∫ x in c..a, w x * P x) := by
            rw [intervalIntegral.integral_const_mul]

      _ = (a : ℂ) * P a * w a -
          (∫ x in c..a, P x * ((1 / 2 + I * z) * w x)) +
          (1 / 2 : ℂ) * (∫ x in c..a, w x * P x) := by
        rw [hibp]
        ring
      _ = (a : ℂ) * P a * w a -
          I * z * (∫ x in c..a, w x * P x) := by
        have hscalar :
            (∫ x in c..a, P x * ((1 / 2 + I * z) * w x)) =
              (1 / 2 + I * z) * (∫ x in c..a, w x * P x) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _
          ring
        rw [hscalar]
        ring
  have hB0 : 0 < B := by linarith
  have hWcont : Continuous W := by
    have hmax : Continuous (fun x : ℝ => max (1 / B) x) :=
      continuous_const.max continuous_id
    have hlog : Continuous (fun x : ℝ => Real.log (max (1 / B) x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hcomp := ContinuousAt.comp
        (f := fun y : ℝ => max (1 / B) y)
        (g := Real.log)
        (Real.continuousAt_log
          (ne_of_gt (lt_of_lt_of_le (one_div_pos.mpr hB0)
            (le_max_left (1 / B) x))))
        hmax.continuousAt
      change ContinuousAt (Real.log ∘ fun y : ℝ => max (1 / B) y) x
      exact hcomp
    dsimp only [W, suzukiClampedMellinWeightValue]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlog))
  have hW_eq_density {x : ℝ} (hx : c ≤ x) : W x = w x := by
    dsimp only [W, w, suzukiClampedMellinWeightValue, suzukiMellinDensity]
    rw [max_eq_right (hBa.le.trans hx)]
  have hE0c : IntervalIntegrable E volume 0 c := by
    apply hE0a.mono_set
    rw [uIcc_of_le hc.le, uIcc_of_le (by linarith : 0 ≤ a)]
    intro x hx
    exact ⟨hx.1, hx.2.trans hca.le⟩
  have hWE0c : IntervalIntegrable (fun x => W x * E x) volume 0 c :=
    hE0c.continuousOn_mul hWcont.continuousOn
  have hWEca : IntervalIntegrable (fun x => W x * E x) volume c a :=
    hEca.continuousOn_mul hWcont.continuousOn
  have hP0cU : ContinuousOn P (uIcc 0 c) := by
    rw [uIcc_of_le hc.le]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
      (fun _ hx => hx.1)
  have hWP0c : IntervalIntegrable (fun x => W x * P x) volume 0 c :=
    (hWcont.continuousOn.mul hP0cU).intervalIntegrable
  have hWPca : IntervalIntegrable (fun x => W x * P x) volume c a :=
    (hWcont.continuousOn.mul hPcontU).intervalIntegrable
  have hae_ne_c : ∀ᵐ x : ℝ ∂volume, x ≠ c := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬ x ≠ c} = {c} := by
      ext x
      simp
    rw [hset]
    exact measure_singleton c
  have hWEzero : (∫ x in (0 : ℝ)..c, W x * E x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..c, W x * E x) =
          ∫ _x in (0 : ℝ)..c, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hae_ne_c] with x hxc
        intro hx
        rw [uIoc_of_le hc.le] at hx
        have hxc' : x < c := lt_of_le_of_ne hx.2 hxc
        change W x * suzukiHankelEulerPhi epsilon omega a homega ha x = 0
        rw [suzukiHankelEulerPhi_eq_zero_of_pos_lt_reciprocal
          epsilon homega ha hx.1 (by simpa only [c] using hxc'), mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hWPzero : (∫ x in (0 : ℝ)..c, W x * P x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..c, W x * P x) =
          ∫ _x in (0 : ℝ)..c, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hc.le] at hx
        change W x * P x = 0
        rw [show P x = 0 by
          exact suzukiHankelPhiGlobal_eq_zero_below_reciprocal
            epsilon homega ha hx.1 (by simpa only [c] using hx.2), mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hWEfull :
      (∫ x in (0 : ℝ)..a, W x * E x) = ∫ x in c..a, W x * E x := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hWE0c hWEca
    rw [hWEzero, zero_add] at hsplit
    exact hsplit.symm
  have hWPfull :
      (∫ x in (0 : ℝ)..a, W x * P x) = ∫ x in c..a, W x * P x := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hWP0c hWPca
    rw [hWPzero, zero_add] at hsplit
    exact hsplit.symm
  have hWEca_eq :
      (∫ x in c..a, W x * E x) = ∫ x in c..a, w x * E x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hca.le] at hx
    change W x * E x = w x * E x
    rw [hW_eq_density hx.1]
  have hWPca_eq :
      (∫ x in c..a, W x * P x) = ∫ x in c..a, w x * P x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hca.le] at hx
    change W x * P x = w x * P x
    rw [hW_eq_density hx.1]
  have hWa : W a = w a := hW_eq_density hca.le
  have hcompact := suzukiHankelCompactMellin_eq_fixedClamp
    epsilon homega ha haB z
  change (∫ x in (0 : ℝ)..a, W x * E x) =
    (a : ℂ) * P a * W a -
      I * z * suzukiHankelCompactMellin epsilon omega a homega ha z
  rw [hWEfull, hWEca_eq, hWa, hcompact, hWPfull, hWPca_eq]
  exact hcore

end RHTower
