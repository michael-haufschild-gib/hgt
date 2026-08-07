import Mathlib

/-!
# The translation modulus of a function with integrable derivative

The `L¹` modulus of continuity is linear in the shift: writing `f(x+h) − f(x) = ∫₀^h f'(x+s) ds`
and swapping the order of integration gives `∫ ‖f(·+h) − f‖ ≤ h ‖f'‖₁`.  The swap is Tonelli on the
strip `Ioc 0 h × ℝ`, whose joint-integrability hypothesis reduces — with the shift variable
*outside* — to translation invariance of the inner integral.

The shear `(s, x) ↦ x + s` pushes the strip measure forward to `h • volume`, which is what makes
the composed modulus measurable in the first place.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The shear `(s, x) ↦ x + s` is quasi measure preserving from the strip to the line: its
pushforward is `h • volume`. -/
theorem quasiMeasurePreserving_strip_shear (h : ℝ) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2 + p.1)
      ((volume.restrict (Set.Ioc (0:ℝ) h)).prod volume) volume := by
  have hshear := measurePreserving_prod_add_right (volume.restrict (Set.Ioc (0:ℝ) h)) volume
  refine ⟨by fun_prop, ?_⟩
  have hcomp : (fun p : ℝ × ℝ => p.2 + p.1)
      = Prod.snd ∘ (fun p : ℝ × ℝ => (p.1, p.2 + p.1)) := rfl
  rw [hcomp, ← Measure.map_map measurable_snd (by fun_prop), hshear.map_eq,
    Measure.map_snd_prod]
  exact Measure.smul_absolutelyContinuous

/-- Joint integrability of the sheared modulus on the strip. -/
theorem integrable_uncurry_norm_shear (g : ℝ → ℝ) (hg : Integrable g) (h : ℝ) :
    Integrable (Function.uncurry fun (s x : ℝ) => ‖g (x + s)‖)
      ((volume.restrict (Set.Ioc (0:ℝ) h)).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (s x : ℝ) => ‖g (x + s)‖)
      ((volume.restrict (Set.Ioc (0:ℝ) h)).prod volume) :=
    (hg.aestronglyMeasurable.norm).comp_quasiMeasurePreserving (quasiMeasurePreserving_strip_shear h)
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with s
    exact ((hg.comp_add_right s).norm)
  · have hconst : ∀ s : ℝ, (∫ x, ‖‖g (x + s)‖‖) = ∫ x, ‖g x‖ := by
      intro s
      simp only [norm_norm]
      exact integral_add_right_eq_self (fun x => ‖g x‖) s
    simp only [Function.uncurry, hconst]
    exact integrableOn_const (by simp)

/-- **The sheared double integral.**  Integrating the shifted modulus over the strip gives the
shift times the `L¹` norm. -/
theorem integral_integral_shear_eq (g : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ s in Set.Ioc (0:ℝ) h, ∫ x : ℝ, ‖g (x + s)‖) = h * ∫ x : ℝ, ‖g x‖ := by
  have hconst : ∀ s : ℝ, (∫ x : ℝ, ‖g (x + s)‖) = ∫ x : ℝ, ‖g x‖ :=
    fun s => integral_add_right_eq_self (fun x => ‖g x‖) s
  simp only [hconst]
  rw [setIntegral_const]
  have hvol : (volume.real (Set.Ioc (0:ℝ) h)) = h := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol, smul_eq_mul]

/-- **Linear `L¹` modulus of continuity.**  A function with integrable derivative has translation
modulus at most the shift times the `L¹` norm of the derivative.  Writing the increment as
`∫₀^h f'(x+s) ds` and swapping the order of integration is the whole proof; no bounded variation
and no Stieltjes integration by parts enters. -/
theorem integral_norm_translation_le (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hfc : Continuous (deriv f))
    (hf' : Integrable (deriv f)) {h : ℝ} (hh : 0 ≤ h)
    (hint : Integrable (fun x => ‖f (x + h) - f x‖)) :
    (∫ x : ℝ, ‖f (x + h) - f x‖) ≤ h * ∫ x : ℝ, ‖deriv f x‖ := by
  have hjoint := integrable_uncurry_norm_shear (deriv f) hf' h
  have hptw : ∀ x : ℝ, ‖f (x + h) - f x‖ ≤ ∫ s in Ioc (0:ℝ) h, ‖deriv f (x + s)‖ := by
    intro x
    have hrep : (∫ s in (0:ℝ)..h, deriv f (x + s)) = f (x + h) - f x := by
      rw [intervalIntegral.integral_comp_add_left (fun t => deriv f t) x,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => (hf t).hasDerivAt) (hfc.intervalIntegrable _ _)]
      ring_nf
    rw [← hrep, ← intervalIntegral.integral_of_le hh]
    exact intervalIntegral.norm_integral_le_abs_integral_norm.trans (le_of_eq (by
      rw [abs_of_nonneg (intervalIntegral.integral_nonneg hh (fun _ _ => norm_nonneg _))]))
  have hswapInt : Integrable (Function.uncurry fun (x s : ℝ) => ‖deriv f (x + s)‖)
      (volume.prod (volume.restrict (Ioc (0:ℝ) h))) := hjoint.swap
  have houter : Integrable (fun x => ∫ s in Ioc (0:ℝ) h, ‖deriv f (x + s)‖) :=
    MeasureTheory.Integrable.integral_prod_left hswapInt
  have hswap : (∫ x : ℝ, ∫ s in Ioc (0:ℝ) h, ‖deriv f (x + s)‖) = h * ∫ x : ℝ, ‖deriv f x‖ := by
    rw [← integral_integral_swap hjoint]
    exact integral_integral_shear_eq (deriv f) hh
  calc (∫ x : ℝ, ‖f (x + h) - f x‖)
      ≤ ∫ x : ℝ, ∫ s in Ioc (0:ℝ) h, ‖deriv f (x + s)‖ := integral_mono hint houter hptw
    _ = h * ∫ x : ℝ, ‖deriv f x‖ := hswap

end GaloisForLFunctions.HTGeometry
