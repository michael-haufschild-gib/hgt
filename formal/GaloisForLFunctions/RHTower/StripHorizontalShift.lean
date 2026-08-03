import GaloisForLFunctions.HTGeometry.VerticalContourShift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Horizontal contour shift on a strip of exponential decay

A function holomorphic on a closed horizontal strip and decaying exponentially in the real
direction there has the same full-line integral on every horizontal line of the strip.

No new Cauchy theory is needed: the rotation `w |-> -i w` sends `re` to `im` and `im` to `-re`, so a
horizontal shift becomes the vertical one the corpus already owns, the vertical edges of the rotated
rectangle are the horizontal ends of the original, and the decay makes them vanish.
-/

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem rotate_neg_I (u s : ℝ) :
    -Complex.I * ((u : ℂ) + (s : ℂ) * Complex.I) = (s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_exp_neg_mul_abs' {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * |x|))) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
    ring_nf
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := c) hc 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Iic
    rw [abs_of_nonpos hx]
    ring_nf
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- **Horizontal contour shift for a strip-holomorphic function with real-direction exponential
decay.**  The full-line integral does not depend on the height.  The rotation `w ↦ -i w` turns the
horizontal shift into the vertical one the corpus already owns. -/
theorem integral_horizontal_shift_of_decay {F : ℂ → ℂ} {c C r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hF : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖F z‖ ≤ C * Real.exp (-(r * |z.re|))) :
    (∫ x : ℝ, F ((x : ℂ) + (c : ℂ) * Complex.I)) = ∫ x : ℝ, F ((x : ℂ)) := by
  set G : ℂ → ℂ := fun w => F (-Complex.I * w) with hG
  have hrot : ∀ u s : ℝ, G ((u : ℂ) + (s : ℂ) * Complex.I) =
      F ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) := by
    intro u s
    rw [hG]
    simp only
    rw [rotate_neg_I u s]
  have hline : ∀ s y : ℝ, G (((-s : ℝ) : ℂ) + (y : ℝ) * Complex.I) =
      F ((y : ℂ) + (s : ℂ) * Complex.I) := by
    intro s y
    rw [hrot (-s) y]
    norm_num
  have himF : ∀ u s : ℝ, |u| ≤ c → |((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).im| ≤ c := by
    intro u s hu
    simpa using hu
  have hdiff : DifferentiableOn ℂ G (verticalStrip (-c) 0) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (hF (-Complex.I * w) ?_).comp w (by fun_prop)
    have hre : (-Complex.I * w).im = -w.re := by simp [Complex.mul_im]
    rw [hre, abs_neg, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hnormG : ∀ u s : ℝ, |u| ≤ c →
      ‖G ((u : ℂ) + (s : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(r * |s|)) := by
    intro u s hu
    rw [hrot u s]
    have hre : ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).re = s := by simp
    have := hbound _ (himF u s hu)
    rwa [hre] at this
  have hintline : ∀ s : ℝ, |s| ≤ c →
      Integrable (fun y : ℝ => G (((s : ℝ) : ℂ) + (y : ℝ) * Complex.I)) := by
    intro s hs
    refine Integrable.mono' ((integrable_exp_neg_mul_abs' hr).const_mul C) ?_
      (Filter.Eventually.of_forall fun y => hnormG s y hs)
    have hcont : Continuous (fun y : ℝ => G (((s : ℝ) : ℂ) + (y : ℝ) * Complex.I)) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have hmem : |(-Complex.I * (((s : ℝ) : ℂ) + (y : ℝ) * Complex.I)).im| ≤ c := by
        have hre : (-Complex.I * (((s : ℝ) : ℂ) + (y : ℝ) * Complex.I)).im =
            -(((s : ℝ) : ℂ) + (y : ℝ) * Complex.I).re := by simp [Complex.mul_im]
        rw [hre, abs_neg]
        simpa using hs
      have := ((hF _ hmem).continuousAt).comp (x := y)
        (f := fun z : ℝ => -Complex.I * (((s : ℝ) : ℂ) + (z : ℝ) * Complex.I))
        (by fun_prop)
      simpa [hG, Function.comp_def] using this
    exact hcont.aestronglyMeasurable
  have hedge : ∀ sgn : ℝ → ℝ, (∀ T : ℝ, |sgn T| = |T|) →
      Tendsto (fun T : ℝ => ∫ u in (-c)..(0 : ℝ), G ((u : ℂ) + ((sgn T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by
    intro sgn hsgn
    refine tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => C * Real.exp (-(r * |T|))) ?_ ?_
    · filter_upwards with T
      intro u hu
      have hu' : |u| ≤ c := by
        rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      rw [← hsgn T]
      exact hnormG u (sgn T) hu'
    · have hbase : Tendsto (fun T : ℝ => Real.exp (-(r * |T|))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun T : ℝ => -(r * |T|)) atTop atBot := by
          have h2 : Tendsto (fun T : ℝ => r * |T|) atTop atTop :=
            Filter.Tendsto.const_mul_atTop hr tendsto_abs_atTop_atTop
          exact tendsto_neg_atTop_atBot.comp h2
        exact Real.tendsto_exp_atBot.comp h1
      simpa using hbase.const_mul C
  have hc0 : |(0 : ℝ)| ≤ c := by simpa using hc
  have hcc : |(-c)| ≤ c := by rw [abs_neg, abs_of_nonneg hc]
  have hshift := integral_vertical_line_eq_of_horizontal_tendsto (G := G) (c := -c) (d := 0)
    (by linarith) hdiff (hintline (-c) hcc) (hintline 0 hc0)
    (hedge (fun T => -T) (fun T => by rw [abs_neg]))
    (hedge (fun T => T) (fun _ => rfl))
  have hL : (∫ y : ℝ, G (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I)) = ∫ x : ℝ, F ((x : ℂ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hz := hline 0 y
    simpa using hz
  have hR : (∫ y : ℝ, G (((-c : ℝ) : ℂ) + (y : ℝ) * Complex.I)) =
      ∫ x : ℝ, F ((x : ℂ) + (c : ℂ) * Complex.I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hline c y
  rw [← hL, ← hR]
  exact hshift.symm

end RHTower
