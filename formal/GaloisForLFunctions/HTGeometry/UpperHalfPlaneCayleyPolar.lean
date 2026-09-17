import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCayleyDensity
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-!
The inverse Cayley transport followed by Euclidean polar coordinates.  This is
the first global measure step in the literal native-circle realization: no
source is changed, and the disk indicator retains the exact noncompact domain.
-/
namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Metric
noncomputable section

/-- Exact hyperbolic area transport through inverse Cayley and Euclidean polar
coordinates.  The disk indicator is intentional: it is the literal image of
the upper half-plane, before the radial `tanh` reparameterization. -/
theorem integral_diskToUpper_hyperbolic_polar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ 2 • f z) =
      ∫ p in polarCoord.target, p.1 •
        (ball 0 1).indicator
          (fun w : ℂ => (4 / (1 - Complex.normSq w) ^ 2) • f (diskToUpper w))
          (Complex.polarCoord.symm p) := by
  rw [integral_diskToUpper_hyperbolic]
  rw [← integral_indicator measurableSet_ball]
  rw [← Complex.integral_comp_polarCoord_symm]

/-- Exact radial transport from the unit disk to native hyperbolic radius.
The positive half-line is sent bijectively to the literal open unit interval. -/
theorem integral_tanh_half_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ r in Ioo (0 : ℝ) 1, f r) =
      ∫ d in Ioi (0 : ℝ), (1 / (2 * Real.cosh (d / 2) ^ 2)) • f (Real.tanh (d / 2)) := by
  have hderiv : ∀ d ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.tanh (t / 2))
        (1 / (2 * Real.cosh (d / 2) ^ 2)) (Ioi 0) d := by
    intro d _
    have hd := (HTGeometry.hasDerivAt_tanh (d / 2)).comp d ((hasDerivAt_id d).div_const 2)
    have hfun : (fun t : ℝ => Real.tanh (t / 2)) =
        Real.tanh ∘ fun x : ℝ => id x / 2 := by
      funext t
      simp only [Function.comp_apply, id_eq]
    have hcoef : 1 / Real.cosh (d / 2) ^ 2 * (1 / 2 : ℝ) =
        1 / (2 * Real.cosh (d / 2) ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [← hfun, hcoef] at hd
    exact hd.hasDerivWithinAt
  have hinj : InjOn (fun d : ℝ => Real.tanh (d / 2)) (Ioi 0) := by
    intro a ha b hb hab
    have hhalf : a / 2 = b / 2 := HTGeometry.tanh_strictMono.injective hab
    linarith
  have himage : (fun d : ℝ => Real.tanh (d / 2)) '' Ioi 0 = Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [← HTGeometry.tanh_image_Ioi_zero]
      have hd0 : 0 < d := hd
      refine ⟨d / 2, ?_, rfl⟩
      change 0 < d / 2
      exact div_pos hd0 (by norm_num)
    · intro hr
      rw [← HTGeometry.tanh_image_Ioi_zero] at hr
      rcases hr with ⟨d, hd, hvalue⟩
      have hd0 : 0 < d := hd
      refine ⟨2 * d, ?_, ?_⟩
      · change 0 < 2 * d
        exact mul_pos (by norm_num) hd0
      have htwo : (2 * d) / 2 = d := by ring
      change Real.tanh ((2 * d) / 2) = r
      rw [htwo]
      exact hvalue
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj f
  rw [himage] at hchange
  rw [hchange]
  refine setIntegral_congr_fun measurableSet_Ioi fun d _ => ?_
  rw [abs_of_pos (by positivity)]

/-- Exact disk-polar density, before the literal native-circle identification. -/
def diskPolarDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (p : ℝ × ℝ) : E :=
  p.1 • (4 / (1 - Complex.normSq (Complex.polarCoord.symm p)) ^ 2) •
    f (diskToUpper (Complex.polarCoord.symm p))

private theorem polarCoord_mem_ball_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    Complex.polarCoord.symm p ∈ ball 0 1 ↔
      p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi := by
  rcases hp with ⟨hp0, hpθ⟩
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp0]
  simp only [mem_prod, mem_Ioo]
  constructor
  · intro h
    exact ⟨⟨hp0, h⟩, hpθ⟩
  · intro h
    exact h.1.2

/-- The literal noncompact hyperbolic measure is the exact polar measure after
the Cayley map and `r = tanh(d/2)`.  `hf` is deliberately retained: applying
Fubini to a nonintegrable cap would be invalid. -/
theorem integral_diskToUpper_hyperbolic_polar_tanh {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E)
    (hf : IntegrableOn (diskPolarDensity f)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) :
    (∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ 2 • f z) =
      ∫ d in Ioi (0 : ℝ), (1 / (2 * Real.cosh (d / 2) ^ 2)) •
        ∫ theta in Ioo (-Real.pi) Real.pi,
          diskPolarDensity f (Real.tanh (d / 2), theta) := by
  let P : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  have hP : MeasurableSet P := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : P ⊆ polarCoord.target := by
    rintro p ⟨hp, hθ⟩
    exact ⟨hp.1, hθ⟩
  have hpolar :
      (∫ p in polarCoord.target, p.1 •
        (ball 0 1).indicator
          (fun w : ℂ => (4 / (1 - Complex.normSq w) ^ 2) • f (diskToUpper w))
          (Complex.polarCoord.symm p)) =
        ∫ p in P, diskPolarDensity f p := by
    rw [← integral_indicator polarCoord.open_target.measurableSet, ← integral_indicator hP]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      have hball := polarCoord_mem_ball_iff hp
      by_cases hmem : p ∈ P
      · rw [indicator_of_mem (hball.mpr hmem), indicator_of_mem hmem]
        rfl
      · have hnot : Complex.polarCoord.symm p ∉ ball 0 1 := fun h => hmem (hball.mp h)
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hmem]
        simp
    · have hnot : p ∉ P := fun h => hp (hsub h)
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hnot]
  calc
    (∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ 2 • f z) =
        ∫ p in polarCoord.target, p.1 •
          (ball 0 1).indicator
            (fun w : ℂ => (4 / (1 - Complex.normSq w) ^ 2) • f (diskToUpper w))
            (Complex.polarCoord.symm p) := integral_diskToUpper_hyperbolic_polar f
    _ = ∫ p in P, diskPolarDensity f p := hpolar
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ theta in Ioo (-Real.pi) Real.pi,
        diskPolarDensity f (r, theta) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact setIntegral_prod (diskPolarDensity f) hf
    _ = ∫ d in Ioi (0 : ℝ), (1 / (2 * Real.cosh (d / 2) ^ 2)) •
        ∫ theta in Ioo (-Real.pi) Real.pi,
          diskPolarDensity f (Real.tanh (d / 2), theta) :=
      integral_tanh_half_Ioi fun r => ∫ theta in Ioo (-Real.pi) Real.pi,
        diskPolarDensity f (r, theta)

end
end GaloisForLFunctions.HTGeometry
