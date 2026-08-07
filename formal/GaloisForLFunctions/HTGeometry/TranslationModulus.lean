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

open MeasureTheory

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

end GaloisForLFunctions.HTGeometry
