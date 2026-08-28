import GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredAtomicLaplaceNoGo
import Mathlib.Analysis.Calculus.MeanValue

/-!
# No global log-convex normalized flux for the reflected theta source

Put `P_u(x) = thetaCuspReflectedSourceProduct u (sqrt x)` and normalize its positive decay
flux by the square-root displacement.  The exact chain rule is

`P_u'(x) = -thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x / 2`.

If the logarithm of this normalized flux were convex on the whole positive squared-displacement
ray, its secant through `1` and `2` would give an exponential lower minorant on the terminal ray.
The mean-value theorem would transfer that minorant to `P_u`.  This contradicts the completed
theta product's already-proved decay faster than every exponential in squared displacement.

Thus pointwise normalized-flux log-convexity cannot prove the global C5 wall.  Any surviving
argument must retain cumulative earlier flux and permit a negative terminal local residual.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Reflected completed-source product in squared displacement. -/
def thetaCuspReflectedSourceSquaredProduct (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u (Real.sqrt x)

/-- Positive source decay flux divided by displacement, in the squared coordinate. -/
def thetaCuspReflectedSourceSquaredNormalizedDecayFlux (u x : ℝ) : ℝ :=
  thetaCuspReflectedSourceDecayFlux u (Real.sqrt x) / Real.sqrt x

theorem thetaCuspReflectedSourceSquaredNormalizedDecayFlux_pos
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x := by
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFlux
  exact div_pos
    (thetaCuspReflectedSourceDecayFlux_pos u (Real.sqrt_pos.2 hx))
    (Real.sqrt_pos.2 hx)

/-- The normalized squared-variable flux is exactly minus twice the product derivative. -/
theorem hasDerivAt_thetaCuspReflectedSourceSquaredProduct
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspReflectedSourceSquaredProduct u)
      (-thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x / 2) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hp :=
    (hasDerivAt_thetaCuspReflectedSourceProduct u (Real.sqrt x)).comp x hs
  have hp' : HasDerivAt (thetaCuspReflectedSourceSquaredProduct u)
      (-thetaCuspReflectedSourceDecayFlux u (Real.sqrt x) *
        (1 / (2 * Real.sqrt x))) x := by
    exact hp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  unfold thetaCuspReflectedSourceSquaredNormalizedDecayFlux
  convert hp' using 1
  have hsqrt := (Real.sqrt_pos.2 hx).ne'
  field_simp [hsqrt]

/-- A convex logarithm lies above the terminal affine secant through squared scales `1` and `2`. -/
private theorem log_thetaCuspReflectedSourceSquaredNormalizedDecayFlux_secant_lower
    (u : ℝ)
    (hconv : ConvexOn ℝ (Ioi 0)
      (fun x => Real.log
        (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x)))
    {y : ℝ} (hy : 2 < y) :
    Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2) +
        (y - 2) *
          (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2) -
            Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1)) ≤
      Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u y) := by
  have hsec := hconv.secant_mono_aux1
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show y ∈ Ioi 0 by exact lt_trans (by norm_num) hy)
    (show (1 : ℝ) < 2 by norm_num) hy
  norm_num at hsec ⊢
  linarith

/-- On every positive unit interval, one interior normalized flux equals twice the product drop. -/
private theorem exists_thetaCuspReflectedSourceSquaredProduct_drop_eq_flux
    (u : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ c ∈ Ioo x (x + 1),
      thetaCuspReflectedSourceSquaredProduct u x -
          thetaCuspReflectedSourceSquaredProduct u (x + 1) =
        thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c / 2 := by
  have hlt : x < x + 1 := by linarith
  have hcont : ContinuousOn
      (thetaCuspReflectedSourceSquaredProduct u) (Icc x (x + 1)) := by
    intro y hy
    exact (hasDerivAt_thetaCuspReflectedSourceSquaredProduct u
      (by linarith [hy.1] : 0 < y)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (thetaCuspReflectedSourceSquaredProduct u) (Ioo x (x + 1)) := by
    intro y hy
    exact (hasDerivAt_thetaCuspReflectedSourceSquaredProduct u
      (by linarith [hy.1] : 0 < y)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope
    (thetaCuspReflectedSourceSquaredProduct u) hlt hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [(hasDerivAt_thetaCuspReflectedSourceSquaredProduct u
    (by linarith [hc.1] : 0 < c)).deriv] at hder
  norm_num at hder
  linarith

/-- **Normalized-flux no-go.**  At every center, the logarithm of the positive normalized decay
flux fails to be globally convex in squared displacement. -/
theorem not_convexOn_log_thetaCuspReflectedSourceSquaredNormalizedDecayFlux
    (u : ℝ) :
    ¬ ConvexOn ℝ (Ioi 0)
      (fun x => Real.log
        (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u x)) := by
  intro hconv
  let m := Real.log
      (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2) -
    Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1)
  by_cases hm : 0 ≤ m
  · have hlim :=
      tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero
        u (a := 0) (by norm_num)
    have hconst :
        0 < Real.exp
          (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2)) / 2 := by
      positivity
    have hevent : ∀ᶠ x : ℝ in atTop,
        Real.exp (0 * x) * thetaCuspReflectedSourceSquaredProduct u x <
          Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2)) / 2 := by
      simpa only [thetaCuspReflectedSourceSquaredProduct] using
        hlim.eventually (Iio_mem_nhds hconst)
    obtain ⟨x, hxevent, hx2⟩ :=
      (hevent.and (eventually_gt_atTop (2 : ℝ))).exists
    obtain ⟨c, hc, hdrop⟩ :=
      exists_thetaCuspReflectedSourceSquaredProduct_drop_eq_flux u
        (by linarith : 0 < x)
    have hlog :=
      log_thetaCuspReflectedSourceSquaredNormalizedDecayFlux_secant_lower
        u hconv (by linarith [hc.1] : 2 < c)
    have hlog2 :
        Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2) ≤
          Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c) := by
      dsimp [m] at hm
      nlinarith [mul_nonneg (by linarith [hc.1] : 0 ≤ c - 2) hm]
    have hflux :
        Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2)) ≤
          thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c := by
      calc
        Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 2)) ≤
            Real.exp
              (Real.log
                (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c)) :=
          Real.exp_le_exp.mpr hlog2
        _ = thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c :=
          Real.exp_log
            (thetaCuspReflectedSourceSquaredNormalizedDecayFlux_pos u
              (by linarith [hc.1]))
    have hnext :
        0 < thetaCuspReflectedSourceSquaredProduct u (x + 1) := by
      unfold thetaCuspReflectedSourceSquaredProduct thetaCuspReflectedSourceProduct
      exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
    norm_num at hxevent
    nlinarith
  · have hmneg : m < 0 := lt_of_not_ge hm
    let a := -m
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hlim :=
      tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero u ha
    have hconst :
        0 < Real.exp
          (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1)) / 2 := by
      positivity
    have hevent : ∀ᶠ x : ℝ in atTop,
        Real.exp (a * x) * thetaCuspReflectedSourceSquaredProduct u x <
          Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1)) / 2 := by
      simpa only [thetaCuspReflectedSourceSquaredProduct] using
        hlim.eventually (Iio_mem_nhds hconst)
    obtain ⟨x, hxevent, hx2⟩ :=
      (hevent.and (eventually_gt_atTop (2 : ℝ))).exists
    obtain ⟨c, hc, hdrop⟩ :=
      exists_thetaCuspReflectedSourceSquaredProduct_drop_eq_flux u
        (by linarith : 0 < x)
    have hlog :=
      log_thetaCuspReflectedSourceSquaredNormalizedDecayFlux_secant_lower
        u hconv (by linarith [hc.1] : 2 < c)
    have hlog1 :
        Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1) + m * x ≤
          Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c) := by
      have hcmul : (c - 2) * m ≥ (x - 1) * m := by
        exact mul_le_mul_of_nonpos_right (by linarith [hc.2]) hmneg.le
      dsimp [m] at hlog ⊢
      linarith
    have hflux :
        Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1) +
              m * x) ≤
          thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c := by
      calc
        Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1) +
              m * x) ≤
            Real.exp
              (Real.log
                (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c)) :=
          Real.exp_le_exp.mpr hlog1
        _ = thetaCuspReflectedSourceSquaredNormalizedDecayFlux u c :=
          Real.exp_log
            (thetaCuspReflectedSourceSquaredNormalizedDecayFlux_pos u
              (by linarith [hc.1]))
    have hscale :
        Real.exp (a * x) *
            Real.exp
              (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1) +
                m * x) =
          Real.exp
            (Real.log (thetaCuspReflectedSourceSquaredNormalizedDecayFlux u 1)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    have hnext :
        0 < thetaCuspReflectedSourceSquaredProduct u (x + 1) := by
      unfold thetaCuspReflectedSourceSquaredProduct thetaCuspReflectedSourceProduct
      exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
    have hexpa : 0 < Real.exp (a * x) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left hflux hexpa.le]

end

end RHTower
