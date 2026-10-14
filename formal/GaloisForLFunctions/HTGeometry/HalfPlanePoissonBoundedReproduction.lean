import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyVanishing
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.HTGeometry.DslopeLocalFactor

/-!
# Poisson reproduction of bounded holomorphic functions on the upper half-plane

A function holomorphic and bounded on the closed upper half-plane is reproduced at `i` by its
Poisson average along the real line:

```text
∫ P₁(x) F(x) dx = F(i),        P₁(x) = 1 / (π (1 + x²)).
```

On the real line `P₁(x) (F(x) − F(i)) = dslope F i x / (π (x + i))`.  The right side is holomorphic
on the closed upper half-plane, because the singularity at `i` is removable and the pole `−i` lies
below the axis.  It decays like `|z|⁻²` there, so its line integral vanishes by
`integral_eq_zero_of_upperHalfPlane_decay`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

/-- The holomorphic quotient whose line integral is the Poisson reproduction defect. -/
def poissonReproductionDefect (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope F I z / ((Real.pi : ℂ) * (z + I))

private theorem ofReal_ne_I (x : ℝ) : (x : ℂ) ≠ I := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
  linarith

/-- On the real line the defect is the Poisson kernel times the deviation from `F(i)`. -/
theorem poissonReproductionDefect_ofReal (F : ℂ → ℂ) (x : ℝ) :
    poissonReproductionDefect F x = (halfPlanePoisson 1 x : ℂ) * (F x - F I) := by
  rw [poissonReproductionDefect, dslope_of_ne _ (ofReal_ne_I x), slope_def_field,
    halfPlanePoisson, div_div]
  have hkey : ((x : ℂ) - I) * ((Real.pi : ℂ) * ((x : ℂ) + I)) =
      (Real.pi : ℂ) * (1 + (x : ℂ) ^ (2 : ℕ)) := by
    linear_combination (-(Real.pi : ℂ)) * Complex.I_sq
  have h1x : (1 + (x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    have : ((1 + x ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 1 + x ^ 2).ne'
    simpa using this
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hkey]
  push_cast
  field_simp

/-- `‖z + i‖² ≥ 1 + ‖z‖²` on the closed upper half-plane. -/
private theorem one_add_normSq_le_norm_add_I_sq {z : ℂ} (hz : 0 ≤ z.im) :
    1 + ‖z‖ ^ (2 : ℕ) ≤ ‖z + I‖ ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
  nlinarith

/-- Away from `i`, `25 ‖z − i‖² ≥ 1 + ‖z‖²`. -/
private theorem one_add_normSq_le_norm_sub_I_sq {z : ℂ} (hz : 1 / 2 ≤ ‖z - I‖) :
    1 + ‖z‖ ^ (2 : ℕ) ≤ 25 * ‖z - I‖ ^ (2 : ℕ) := by
  have htri : ‖z‖ - 1 ≤ ‖z - I‖ := by
    have := norm_sub_norm_le z I
    rw [Complex.norm_I] at this
    exact this
  have hn := norm_nonneg z
  rcases le_or_gt ‖z‖ (3 / 2) with hs | hs
  · nlinarith
  · nlinarith

/-- The decay of the reproduction defect on the closed upper half-plane. -/
theorem exists_norm_poissonReproductionDefect_le {F : ℂ → ℂ} {M : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z)
    (hbd : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ M) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      ‖poissonReproductionDefect F z‖ ≤ C / (1 + ‖z‖ ^ (2 : ℕ)) := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbd I (by simp))
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the divided slope is continuous on the closed ball of radius ½ about `i`
  have hball_im : ∀ z ∈ closedBall I (1 / 2 : ℝ), 1 / 2 ≤ z.im := by
    intro z hz
    have hz' : ‖z - I‖ ≤ 1 / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hz
    have h := (Complex.abs_im_le_norm (z - I)).trans hz'
    simp only [Complex.sub_im, Complex.I_im] at h
    have := (abs_le.mp h).1
    linarith
  have hcont : ContinuousOn (dslope F I) (closedBall I (1 / 2 : ℝ)) := by
    intro z hz
    have hzim := hball_im z hz
    by_cases hzI : z = I
    · subst hzI
      refine (differentiableAt_dslope_of_eventually_differentiableAt ?_).continuousAt
        |>.continuousWithinAt
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds (show (0 : ℝ) < I.im by simp)] with w hw
      exact hdiff w (le_of_lt hw)
    · exact ((differentiableAt_dslope_of_ne hzI).mpr
        (hdiff z (by linarith))).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall I (1 / 2 : ℝ)).exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB I (mem_closedBall_self (by norm_num)))
  refine ⟨(10 * M + 4 * B) / Real.pi, fun z hz => ?_⟩
  have hzI_ne : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg hz
  have hplus := one_add_normSq_le_norm_add_I_sq hz
  have hpos : 0 < 1 + ‖z‖ ^ (2 : ℕ) := by positivity
  have hplus1 : 1 ≤ ‖z + I‖ := by
    have h1 : (1 : ℝ) ≤ ‖z + I‖ ^ (2 : ℕ) := le_trans (by nlinarith [sq_nonneg ‖z‖]) hplus
    nlinarith [norm_nonneg (z + I)]
  rw [poissonReproductionDefect, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpi, le_div_iff₀ hpos]
  rcases lt_or_ge ‖z - I‖ (1 / 2) with hnear | hfar
  · -- near `i`: the compact bound
    have hzb : z ∈ closedBall I (1 / 2 : ℝ) := mem_closedBall.mpr (by rw [dist_eq_norm]; linarith)
    have hd := hB z hzb
    have hsmall : ‖z‖ ≤ 3 / 2 := by
      have := norm_le_norm_add_norm_sub' z I
      rw [Complex.norm_I] at this
      linarith
    have hden : Real.pi * 1 ≤ Real.pi * ‖z + I‖ := mul_le_mul_of_nonneg_left hplus1 hpi.le
    have hq : ‖dslope F I z‖ / (Real.pi * ‖z + I‖) ≤ B / Real.pi := by
      rw [div_le_div_iff₀ (by positivity) hpi]
      nlinarith [norm_nonneg (dslope F I z)]
    have h13 : 1 + ‖z‖ ^ (2 : ℕ) ≤ 4 := by nlinarith [norm_nonneg z]
    have hBpi0 : 0 ≤ B / Real.pi := by positivity
    calc ‖dslope F I z‖ / (Real.pi * ‖z + I‖) * (1 + ‖z‖ ^ (2 : ℕ))
        ≤ B / Real.pi * 4 := mul_le_mul hq h13 hpos.le hBpi0
      _ ≤ (10 * M + 4 * B) / Real.pi := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]
          linarith
  · -- away from `i`: the divided slope is the honest slope
    have hzI : z ≠ I := by
      intro h
      rw [h, sub_self, norm_zero] at hfar
      norm_num at hfar
    have hslope : ‖dslope F I z‖ ≤ 2 * M / ‖z - I‖ := by
      rw [dslope_of_ne _ hzI, slope_def_field, norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      calc ‖F z - F I‖ ≤ ‖F z‖ + ‖F I‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbd z hz) (hbd I (by simp))
        _ = 2 * M := by ring
    have hminus := one_add_normSq_le_norm_sub_I_sq hfar
    have hdpos : 0 < ‖z - I‖ := by linarith
    -- (‖z−i‖‖z+i‖)² ≥ (1+‖z‖²)²/25
    have hprod : (1 + ‖z‖ ^ (2 : ℕ)) ≤ 5 * (‖z - I‖ * ‖z + I‖) := by
      have hsq : (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (5 * (‖z - I‖ * ‖z + I‖)) ^ (2 : ℕ) := by
        have := mul_le_mul hminus hplus hpos.le (by positivity)
        nlinarith
      have h0 : 0 ≤ 5 * (‖z - I‖ * ‖z + I‖) := by positivity
      nlinarith [sq_nonneg (1 + ‖z‖ ^ (2 : ℕ) - 5 * (‖z - I‖ * ‖z + I‖)),
        sq_nonneg (1 + ‖z‖ ^ (2 : ℕ) + 5 * (‖z - I‖ * ‖z + I‖))]
    have hzIpos : 0 < ‖z + I‖ := by linarith
    calc ‖dslope F I z‖ / (Real.pi * ‖z + I‖) * (1 + ‖z‖ ^ (2 : ℕ))
        ≤ (2 * M / ‖z - I‖) / (Real.pi * ‖z + I‖) * (5 * (‖z - I‖ * ‖z + I‖)) := by
          apply mul_le_mul _ hprod hpos.le (by positivity)
          exact div_le_div_of_nonneg_right hslope (by positivity)
      _ = 10 * M / Real.pi := by
          field_simp
          ring
      _ ≤ (10 * M + 4 * B) / Real.pi := by
          apply div_le_div_of_nonneg_right _ hpi.le
          linarith

/-- The defect is holomorphic on the closed upper half-plane. -/
theorem differentiableAt_poissonReproductionDefect {F : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (poissonReproductionDefect F) z := by
  have hslope : DifferentiableAt ℂ (dslope F I) z := by
    by_cases hzI : z = I
    · subst hzI
      refine differentiableAt_dslope_of_eventually_differentiableAt ?_
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds (show (0 : ℝ) < I.im by simp)] with w hw
      exact hdiff w (le_of_lt hw)
    · exact (differentiableAt_dslope_of_ne hzI).mpr (hdiff z hz)
  have hden : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) * (w + I)) z := by fun_prop
  have hne : (Real.pi : ℂ) * (z + I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (add_I_ne_zero_of_im_nonneg hz)
  exact hslope.div hden hne

/-- **Poisson reproduction.**  A function holomorphic and bounded on the closed upper half-plane
equals its Poisson average at `i`. -/
theorem integral_halfPlanePoisson_one_mul_eq_apply_I {F : ℂ → ℂ} {M : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z)
    (hbd : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ M) :
    (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * F x) = F I := by
  obtain ⟨C, hC⟩ := exists_norm_poissonReproductionDefect_le hdiff hbd
  have hzero := integral_eq_zero_of_upperHalfPlane_decay
    (fun z hz => differentiableAt_poissonReproductionDefect hdiff hz) hC
  simp only [poissonReproductionDefect_ofReal] at hzero
  have hP : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ)) :=
    (integrable_halfPlanePoisson one_pos).ofReal
  have hFc : Continuous (fun x : ℝ => F x) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact ((hdiff x (by simp)).continuousAt).comp Complex.continuous_ofReal.continuousAt
  have hPF : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * F x) := by
    refine (hP.bdd_mul (c := M) hFc.aestronglyMeasurable ?_).congr ?_
    · exact Eventually.of_forall fun x => hbd x (by simp)
    · exact Eventually.of_forall fun x => mul_comm _ _
  have hPc : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * F I) := hP.mul_const _
  have hsplit : (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * (F x - F I)) =
      (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * F x) - ∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * F I := by
    rw [← integral_sub hPF hPc]
    congr 1
    funext x
    ring
  have hconst : (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * F I) = F I := by
    rw [integral_mul_const, integral_complex_ofReal, integral_halfPlanePoisson one_pos]
    simp
  rw [hsplit, hconst] at hzero
  exact sub_eq_zero.mp hzero

end GaloisForLFunctions.HTGeometry
