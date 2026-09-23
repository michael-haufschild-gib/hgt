import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati

/-!
# Cofinal Ward convexity after complete theta-shell summation

Individual tilted Ward shells have a ground-shell curvature defect.  This file sums every
positive theta shell before reading curvature.  The cofinal Ward density is identified both with
the convergent Gibbs-atom sum and with an exact first-order combination of the raw theta tail.
Its source-forced ODE then shows that the completed logarithmic-source decay cancels the
ground-shell defect: every tilt `0 ≤ a ≤ 1/4` is strictly convex on the positive half-line.

No Fourier-current sign or Riemann-hypothesis conclusion is asserted here.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete positive Ward density after summing every positive theta shell. -/
def thetaCuspCofinalWardDensity (x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * thetaCuspTailDerivative 0 x -
      thetaCuspTailDerivative 1 x) / (2 * Real.pi)

/-- Aperture tilt of the complete Ward density. -/
def thetaCuspCofinalTiltedWardDensity (a x : ℝ) : ℝ :=
  Real.exp (a * x) * thetaCuspCofinalWardDensity x

/-- Source-forced first derivative of the complete tilted Ward density. -/
def thetaCuspCofinalTiltedWardDerivative (a x : ℝ) : ℝ :=
  (a - 1 / 2) * thetaCuspCofinalTiltedWardDensity a x -
    Real.exp (a * x) * thetaCuspFullSource x / (2 * Real.pi)

/-- Logarithmic-source normal form of the second derivative of the complete tilted Ward
density. -/
def thetaCuspCofinalTiltedWardSecondDerivative (a x : ℝ) : ℝ :=
  (a - 1 / 2) ^ (2 : ℕ) * thetaCuspCofinalTiltedWardDensity a x +
    (1 / 2 - 2 * a - iteratedDeriv 1 thetaCuspLogSource x) *
      (Real.exp (a * x) * thetaCuspFullSource x / (2 * Real.pi))

theorem hasDerivAt_thetaCuspCofinalWardDensity (x : ℝ) :
    HasDerivAt thetaCuspCofinalWardDensity
      (((1 / 2 : ℝ) * thetaCuspTailDerivative 1 x -
          thetaCuspTailDerivative 2 x) / (2 * Real.pi)) x := by
  unfold thetaCuspCofinalWardDensity
  convert (((hasDerivAt_thetaCuspTailDerivative 0 x).const_mul (1 / 2 : ℝ)).sub
    (hasDerivAt_thetaCuspTailDerivative 1 x)).div_const (2 * Real.pi) using 1
  all_goals rfl

/-- Exact cofinal Ward equation
`W' + W/2 = -thetaCuspFullSource/(2*pi)`. -/
theorem thetaCuspCofinalWard_ode (x : ℝ) :
    ((1 / 2 : ℝ) * thetaCuspTailDerivative 1 x -
          thetaCuspTailDerivative 2 x) / (2 * Real.pi) +
        (1 / 2 : ℝ) * thetaCuspCofinalWardDensity x =
      -thetaCuspFullSource x / (2 * Real.pi) := by
  rw [thetaCuspFullSource_eq_tail_second_sub]
  unfold thetaCuspCofinalWardDensity
  ring

theorem hasDerivAt_thetaCuspCofinalTiltedWardDensity (a x : ℝ) :
    HasDerivAt (thetaCuspCofinalTiltedWardDensity a)
      (thetaCuspCofinalTiltedWardDerivative a x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    all_goals first | rfl | ring
  have hW := hasDerivAt_thetaCuspCofinalWardDensity x
  convert he.mul hW using 1
  any_goals rfl
  have hode := thetaCuspCofinalWard_ode x
  have hderivative :
      ((1 / 2 : ℝ) * thetaCuspTailDerivative 1 x -
          thetaCuspTailDerivative 2 x) / (2 * Real.pi) =
        -thetaCuspFullSource x / (2 * Real.pi) -
          (1 / 2 : ℝ) * thetaCuspCofinalWardDensity x := by
    linarith
  rw [hderivative]
  simp only [thetaCuspCofinalTiltedWardDensity,
    thetaCuspCofinalTiltedWardDerivative]
  ring

theorem hasDerivAt_thetaCuspCofinalTiltedWardDerivative (a x : ℝ) :
    HasDerivAt (thetaCuspCofinalTiltedWardDerivative a)
      (thetaCuspCofinalTiltedWardSecondDerivative a x) x := by
  let R : ℝ → ℝ := fun y =>
    Real.exp (a * y) * thetaCuspFullSource y / (2 * Real.pi)
  have he : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    all_goals first | rfl | ring
  have hR : HasDerivAt R
      ((a * Real.exp (a * x) * thetaCuspFullSource x +
          Real.exp (a * x) * iteratedDeriv 1 thetaCuspFullSource x) /
        (2 * Real.pi)) x := by
    dsimp only [R]
    convert (he.mul (hasDerivAt_thetaCuspFullSource_iterate_zero x)).div_const
      (2 * Real.pi) using 1
    all_goals rfl
  have hF := hasDerivAt_thetaCuspCofinalTiltedWardDensity a x
  have hraw := (hF.const_mul (a - 1 / 2 : ℝ)).sub hR
  convert hraw using 1
  any_goals rfl
  unfold thetaCuspCofinalTiltedWardSecondDerivative
    thetaCuspCofinalTiltedWardDerivative
  have hlog := (hasDerivAt_thetaCuspLogSource x).deriv
  simp only [iteratedDeriv_one] at hlog ⊢
  have hsource := thetaCuspFullSource_pos_all x
  field_simp [hsource.ne'] at hlog
  rw [← hlog]
  ring

/-- Absolute summability of the complete positive Ward packet at each logarithmic point. -/
theorem summable_thetaCuspCofinalWardGibbsAtom (x : ℝ) :
    Summable (fun n : ℕ => thetaCuspWardGibbsAtom (n + 1) x) := by
  have h0 :=
    (summable_thetaCuspTailDerivative 0 x).mul_left (1 / 2 : ℝ)
  have h1 := summable_thetaCuspTailDerivative 1 x
  have h := (h0.sub h1).mul_left ((2 * Real.pi)⁻¹)
  apply h.congr
  intro n
  simp [thetaCuspWardGibbsAtom, thetaCuspTailDerivativePolynomial,
    thetaCuspLogDerivativeStep, thetaCuspPolynomialAtom]
  field_simp [Real.pi_ne_zero]
  ring

/-- Complete shell summation equals the tail-derivative Ward density. -/
theorem tsum_thetaCuspCofinalWardGibbsAtom_eq (x : ℝ) :
    (∑' n : ℕ, thetaCuspWardGibbsAtom (n + 1) x) =
      thetaCuspCofinalWardDensity x := by
  have h0 := summable_thetaCuspTailDerivative 0 x
  have h1 := summable_thetaCuspTailDerivative 1 x
  calc
    (∑' n : ℕ, thetaCuspWardGibbsAtom (n + 1) x) =
        ∑' n : ℕ, (2 * Real.pi)⁻¹ *
          ((1 / 2 : ℝ) *
              thetaCuspPolynomialAtom
                (thetaCuspTailDerivativePolynomial 0) (n + 1) x -
            thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 1) (n + 1) x) := by
      apply tsum_congr
      intro n
      simp [thetaCuspWardGibbsAtom, thetaCuspTailDerivativePolynomial,
        thetaCuspLogDerivativeStep, thetaCuspPolynomialAtom]
      field_simp [Real.pi_ne_zero]
      ring
    _ = (2 * Real.pi)⁻¹ *
        (∑' n : ℕ,
          ((1 / 2 : ℝ) *
              thetaCuspPolynomialAtom
                (thetaCuspTailDerivativePolynomial 0) (n + 1) x -
            thetaCuspPolynomialAtom
              (thetaCuspTailDerivativePolynomial 1) (n + 1) x)) := by
      rw [tsum_mul_left]
    _ = thetaCuspCofinalWardDensity x := by
      have hsum :
          (∑' n : ℕ,
            ((1 / 2 : ℝ) *
                thetaCuspPolynomialAtom
                  (thetaCuspTailDerivativePolynomial 0) (n + 1) x -
              thetaCuspPolynomialAtom
                (thetaCuspTailDerivativePolynomial 1) (n + 1) x)) =
            (1 / 2 : ℝ) *
                (∑' n : ℕ,
                  thetaCuspPolynomialAtom
                    (thetaCuspTailDerivativePolynomial 0) (n + 1) x) -
              ∑' n : ℕ,
                thetaCuspPolynomialAtom
                  (thetaCuspTailDerivativePolynomial 1) (n + 1) x := by
        simpa only [tsum_mul_left] using
          (h0.mul_left (1 / 2 : ℝ)).tsum_sub h1
      rw [hsum]
      unfold thetaCuspCofinalWardDensity thetaCuspTailDerivative
      ring

theorem thetaCuspCofinalWardDensity_pos (x : ℝ) :
    0 < thetaCuspCofinalWardDensity x := by
  rw [← tsum_thetaCuspCofinalWardGibbsAtom_eq]
  have hs := summable_thetaCuspCofinalWardGibbsAtom x
  have hnonneg : ∀ n : ℕ, 0 ≤ thetaCuspWardGibbsAtom (n + 1) x := by
    intro n
    rw [thetaCuspWardGibbsAtom_apply]
    positivity
  have hfirst : 0 < thetaCuspWardGibbsAtom 1 x := by
    rw [thetaCuspWardGibbsAtom_apply]
    positivity
  exact lt_of_lt_of_le hfirst (hs.le_tsum 0 (fun j _hj => hnonneg j))

/-- **Cofinal curvature cancellation.**  Although the ground Ward shell has a compact curvature
defect, the sum of all shells has strictly positive tilted curvature throughout
`0 ≤ a ≤ 1/4`, `x > 0`. -/
theorem thetaCuspCofinalTiltedWardSecondDerivative_pos
    {a x : ℝ} (_ha0 : 0 ≤ a) (haQuarter : a ≤ 1 / 4) (hx : 0 < x) :
    0 < thetaCuspCofinalTiltedWardSecondDerivative a x := by
  have hF : 0 < thetaCuspCofinalTiltedWardDensity a x := by
    unfold thetaCuspCofinalTiltedWardDensity
    exact mul_pos (Real.exp_pos _) (thetaCuspCofinalWardDensity_pos x)
  have hR :
      0 < Real.exp (a * x) * thetaCuspFullSource x / (2 * Real.pi) := by
    positivity [thetaCuspFullSource_pos_all x, Real.pi_pos]
  have hq := neg_iteratedDeriv_one_thetaCuspLogSource_pos hx
  have hc : 0 < 1 / 2 - 2 * a -
      iteratedDeriv 1 thetaCuspLogSource x := by
    linarith
  unfold thetaCuspCofinalTiltedWardSecondDerivative
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sq_nonneg _) hF.le) (mul_pos hc hR)

private theorem integrableOn_exp_mul_of_abs_le_exp_neg
    (g : ℝ → ℝ) (hg : Continuous g) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ {x : ℝ}, 0 ≤ x → |g x| ≤ C * Real.exp (-x))
    {a : ℝ} (ha : a < 1) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x) * g x) (Ioi 0) := by
  have hdom :
      IntegrableOn (fun x : ℝ => C * Real.exp ((a - 1) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (sub_neg.mpr ha) 0).const_mul C
  apply Integrable.mono hdom
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := hbound hx.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    calc
      Real.exp (a * x) * |g x| ≤
          Real.exp (a * x) * (C * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp ((a - 1) * x) := by
        calc
          Real.exp (a * x) * (C * Real.exp (-x)) =
              C * (Real.exp (a * x) * Real.exp (-x)) := by ring
          _ = C * Real.exp ((a - 1) * x) := by
            rw [← Real.exp_add]
            congr 2
            ring

private theorem tendsto_exp_mul_of_abs_le_exp_neg
    (g : ℝ → ℝ) (C : ℝ)
    (hbound : ∀ {x : ℝ}, 0 ≤ x → |g x| ≤ C * Real.exp (-x))
    {a : ℝ} (ha : a < 1) :
    Tendsto (fun x : ℝ => Real.exp (a * x) * g x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖Real.exp (a * x) * g x‖ ≤
        C * Real.exp ((a - 1) * x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (a * x) * |g x| ≤
          Real.exp (a * x) * (C * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (hbound hx) (Real.exp_pos _).le
      _ = C * Real.exp ((a - 1) * x) := by
        calc
          Real.exp (a * x) * (C * Real.exp (-x)) =
              C * (Real.exp (a * x) * Real.exp (-x)) := by ring
          _ = C * Real.exp ((a - 1) * x) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hexp :
      Tendsto (fun x : ℝ => Real.exp ((a - 1) * x)) atTop (𝓝 0) := by
    rw [Real.tendsto_exp_comp_nhds_zero]
    exact (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
      |>.const_mul_atTop_of_neg (sub_neg.mpr ha)
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle
    (by simpa using hexp.const_mul C)

private theorem integrableOn_exp_mul_thetaCuspTailDerivative_of_lt_one
    (m : ℕ) {a : ℝ} (ha : a < 1) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (a * x) * thetaCuspTailDerivative m x) (Ioi 0) :=
  integrableOn_exp_mul_of_abs_le_exp_neg
    (thetaCuspTailDerivative m)
    (differentiable_thetaCuspTailDerivative m).continuous
    (thetaCuspTailDerivativeExpConstant m)
    (thetaCuspTailDerivativeExpConstant_nonneg m)
    (fun hx => abs_thetaCuspTailDerivative_le_exp_neg m hx) ha

private theorem tendsto_exp_mul_thetaCuspTailDerivative_atTop_zero_of_lt_one
    (m : ℕ) {a : ℝ} (ha : a < 1) :
    Tendsto (fun x : ℝ =>
      Real.exp (a * x) * thetaCuspTailDerivative m x) atTop (𝓝 0) :=
  tendsto_exp_mul_of_abs_le_exp_neg
    (thetaCuspTailDerivative m)
    (thetaCuspTailDerivativeExpConstant m)
    (fun hx => abs_thetaCuspTailDerivative_le_exp_neg m hx) ha

private theorem continuous_iteratedDeriv_thetaCuspFullSource (m : ℕ) :
    Continuous (iteratedDeriv m thetaCuspFullSource) := by
  rw [iteratedDeriv_thetaCuspFullSource]
  exact continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaCuspFullDerivative m x).continuousAt

private theorem integrableOn_exp_mul_iteratedDeriv_thetaCuspFullSource_of_lt_one
    (m : ℕ) {a : ℝ} (ha : a < 1) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) (Ioi 0) :=
  integrableOn_exp_mul_of_abs_le_exp_neg
    (iteratedDeriv m thetaCuspFullSource)
    (continuous_iteratedDeriv_thetaCuspFullSource m)
    (thetaCuspDerivativeExpConstant m)
    (thetaCuspDerivativeExpConstant_nonneg m)
    (fun hx => abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg m hx) ha

private theorem tendsto_exp_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero_of_lt_one
    (m : ℕ) {a : ℝ} (ha : a < 1) :
    Tendsto (fun x : ℝ =>
      Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) atTop (𝓝 0) :=
  tendsto_exp_mul_of_abs_le_exp_neg
    (iteratedDeriv m thetaCuspFullSource)
    (thetaCuspDerivativeExpConstant m)
    (fun hx => abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg m hx) ha

theorem integrableOn_thetaCuspCofinalTiltedWardDensity
    {a : ℝ} (ha : a < 1) :
    IntegrableOn (thetaCuspCofinalTiltedWardDensity a) (Ioi 0) := by
  have h0 :=
    integrableOn_exp_mul_thetaCuspTailDerivative_of_lt_one 0 ha
  have h1 :=
    integrableOn_exp_mul_thetaCuspTailDerivative_of_lt_one 1 ha
  rw [show thetaCuspCofinalTiltedWardDensity a =
      fun x : ℝ => (2 * Real.pi)⁻¹ *
        ((1 / 2 : ℝ) *
            (Real.exp (a * x) * thetaCuspTailDerivative 0 x) -
          Real.exp (a * x) * thetaCuspTailDerivative 1 x) by
    funext x
    unfold thetaCuspCofinalTiltedWardDensity thetaCuspCofinalWardDensity
    ring]
  exact ((h0.const_mul (1 / 2 : ℝ)).sub h1).const_mul _

theorem integrableOn_thetaCuspCofinalTiltedWardDerivative
    {a : ℝ} (ha : a < 1) :
    IntegrableOn (thetaCuspCofinalTiltedWardDerivative a) (Ioi 0) := by
  have hF := integrableOn_thetaCuspCofinalTiltedWardDensity ha
  have hsource :=
    integrableOn_exp_mul_iteratedDeriv_thetaCuspFullSource_of_lt_one 0 ha
  unfold thetaCuspCofinalTiltedWardDerivative
  have hraw := (hF.const_mul (a - 1 / 2 : ℝ)).sub
    (hsource.const_mul ((2 * Real.pi)⁻¹))
  apply hraw.congr
  filter_upwards with x
  simp only [Pi.sub_apply, iteratedDeriv_zero]
  ring

theorem integrableOn_thetaCuspCofinalTiltedWardSecondDerivative
    {a : ℝ} (ha : a < 1) :
    IntegrableOn (thetaCuspCofinalTiltedWardSecondDerivative a) (Ioi 0) := by
  have hF := integrableOn_thetaCuspCofinalTiltedWardDensity ha
  have hsource0 :=
    integrableOn_exp_mul_iteratedDeriv_thetaCuspFullSource_of_lt_one 0 ha
  have hsource1 :=
    integrableOn_exp_mul_iteratedDeriv_thetaCuspFullSource_of_lt_one 1 ha
  rw [show thetaCuspCofinalTiltedWardSecondDerivative a =
      fun x : ℝ =>
        (a - 1 / 2) ^ (2 : ℕ) * thetaCuspCofinalTiltedWardDensity a x +
          (1 / 2 - 2 * a) *
            (Real.exp (a * x) * thetaCuspFullSource x / (2 * Real.pi)) -
          Real.exp (a * x) *
            iteratedDeriv 1 thetaCuspFullSource x / (2 * Real.pi) by
    funext x
    have hlog := (hasDerivAt_thetaCuspLogSource x).deriv
    unfold thetaCuspCofinalTiltedWardSecondDerivative
    simp only [iteratedDeriv_one] at hlog ⊢
    have hsource := thetaCuspFullSource_pos_all x
    field_simp [hsource.ne'] at hlog
    rw [← hlog]
    ring]
  have hraw := ((hF.const_mul ((a - 1 / 2) ^ (2 : ℕ))).add
    (hsource0.const_mul
      ((1 / 2 - 2 * a) * (2 * Real.pi)⁻¹))).sub
    (hsource1.const_mul ((2 * Real.pi)⁻¹))
  apply hraw.congr
  filter_upwards with x
  simp only [Pi.add_apply, Pi.sub_apply, iteratedDeriv_zero]
  ring

theorem thetaCuspCofinalTiltedWardDensity_tendsto_atTop_zero
    {a : ℝ} (ha : a < 1) :
    Tendsto (thetaCuspCofinalTiltedWardDensity a) atTop (𝓝 0) := by
  have h0 :=
    tendsto_exp_mul_thetaCuspTailDerivative_atTop_zero_of_lt_one 0 ha
  have h1 :=
    tendsto_exp_mul_thetaCuspTailDerivative_atTop_zero_of_lt_one 1 ha
  convert ((h0.const_mul (1 / 2 : ℝ)).sub h1).const_mul
    ((2 * Real.pi)⁻¹) using 1
  · funext x
    unfold thetaCuspCofinalTiltedWardDensity thetaCuspCofinalWardDensity
    ring
  · ring

theorem thetaCuspCofinalTiltedWardDerivative_tendsto_atTop_zero
    {a : ℝ} (ha : a < 1) :
    Tendsto (thetaCuspCofinalTiltedWardDerivative a) atTop (𝓝 0) := by
  have hF := thetaCuspCofinalTiltedWardDensity_tendsto_atTop_zero ha
  have hsource :=
    tendsto_exp_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero_of_lt_one 0 ha
  convert (hF.const_mul (a - 1 / 2 : ℝ)).sub
    (hsource.const_mul ((2 * Real.pi)⁻¹)) using 1
  · funext x
    unfold thetaCuspCofinalTiltedWardDerivative
    simp only [iteratedDeriv_zero]
    ring
  · ring

end

end RHTower
