import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip

/-!
# Exponential decay of the centered xi function on horizontal lines

The Fourier--Laplace kernel of the theta source at a complex frequency `w = t + i a` decays in the
real direction at rate `1 - |a|`, because the tilt `exp (a x)` only eats into the source's own decay.
Shifting the contour to the height `delta` therefore converts the frequency's imaginary part into a
factor `exp (t delta)`, which is `exp (-delta |t|)` for `t <= 0`; evenness of the centered xi
function covers the other side.

The estimate is uniform over `|a| <= A` for any `A < 1`, which is the exponential half of the
admissibility bound for the Guinand--Weil test class on closed horizontal strips.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Fourier--Laplace integrand of the theta source at a complex frequency, complexified in the
space variable. -/
def thetaStripKernel (w z : ℂ) : ℂ := Complex.exp (-Complex.I * w * z) * thetaCuspStripSource z

theorem norm_thetaStripKernel (w z : ℂ) :
    ‖thetaStripKernel w z‖ =
      Real.exp (w.re * z.im + w.im * z.re) * ‖thetaCuspStripSource z‖ := by
  rw [thetaStripKernel, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im]
  ring

theorem differentiableAt_thetaStripKernel (w : ℂ) {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    DifferentiableAt ℂ (thetaStripKernel w) z := by
  refine DifferentiableAt.mul ?_ (differentiableAt_thetaCuspStripSource hz)
  exact (Complex.differentiable_exp.differentiableAt).comp z (by fun_prop)

theorem integral_thetaStripKernel_real (w : ℂ) :
    (∫ x : ℝ, thetaStripKernel w ((x : ℝ) : ℂ)) = thetaCuspFourierLaplace w := by
  rw [thetaCuspFourierLaplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [thetaStripKernel, thetaCuspFourierLaplaceIntegrand, thetaCuspStripSource_ofReal]


/-- **Exponential decay of the centered xi function on every horizontal line of the strip.**  The
contour shift applies to the tilted kernel, whose real-direction decay rate is `1 - |a|`. -/
theorem exists_norm_XiC_horizontal_le {A δ : ℝ} (hA1 : A < 1)
    (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t a : ℝ, |a| ≤ A →
      ‖XiC ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨CK, hCK, hK⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  have hrate : 0 < 1 - A := by linarith
  set B : ℝ := ∫ x : ℝ, Real.exp (-((1 - A) * |x|)) with hB
  have hBnn : 0 ≤ B := integral_nonneg fun x => (Real.exp_pos _).le
  have hδlt : δ < Real.pi / 4 := by linarith
  refine ⟨CK * B, by positivity, ?_⟩
  -- the core estimate, for nonpositive frequency real part
  have hcore : ∀ t a : ℝ, t ≤ 0 → |a| ≤ A →
      ‖XiC ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ CK * B * Real.exp (-(δ * |t|)) := by
    intro t a ht ha
    set w : ℂ := (t : ℂ) + (a : ℂ) * Complex.I with hw
    have hwre : w.re = t := by rw [hw]; simp
    have hwim : w.im = a := by rw [hw]; simp
    -- decay of the kernel on the closed substrip
    have hgen : ∀ (M : ℝ) (z : ℂ), t * z.im ≤ M → |z.im| ≤ δ →
        ‖thetaStripKernel w z‖ ≤ (CK * Real.exp M) * Real.exp (-((1 - A) * |z.re|)) := by
      intro M z hM hz
      rw [norm_thetaStripKernel, hwre, hwim]
      have hKz : ‖thetaCuspStripSource z‖ ≤ CK * Real.exp (-|z.re|) := hK z hz
      have hexp1 : Real.exp (t * z.im + a * z.re) ≤ Real.exp M * Real.exp (A * |z.re|) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h2 : a * z.re ≤ A * |z.re| := by
          calc a * z.re ≤ |a * z.re| := le_abs_self _
            _ = |a| * |z.re| := abs_mul _ _
            _ ≤ A * |z.re| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        linarith
      calc Real.exp (t * z.im + a * z.re) * ‖thetaCuspStripSource z‖
          ≤ (Real.exp M * Real.exp (A * |z.re|)) * (CK * Real.exp (-|z.re|)) :=
            mul_le_mul hexp1 hKz (norm_nonneg _) (by positivity)
        _ = (CK * Real.exp M) * (Real.exp (A * |z.re|) * Real.exp (-|z.re|)) := by ring
        _ = (CK * Real.exp M) * Real.exp (-((1 - A) * |z.re|)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    have hbound : ∀ z : ℂ, |z.im| ≤ δ →
        ‖thetaStripKernel w z‖ ≤ (CK * Real.exp (|t| * δ)) * Real.exp (-((1 - A) * |z.re|)) := by
      intro z hz
      refine hgen (|t| * δ) z ?_ hz
      calc t * z.im ≤ |t * z.im| := le_abs_self _
        _ = |t| * |z.im| := abs_mul _ _
        _ ≤ |t| * δ := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
    have hdiff : ∀ z : ℂ, |z.im| ≤ δ → DifferentiableAt ℂ (thetaStripKernel w) z := by
      intro z hz
      refine differentiableAt_thetaStripKernel w ?_
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      linarith [hz, hδlt]
    have hshift := integral_horizontal_shift_of_decay (F := thetaStripKernel w) (c := δ)
      (C := CK * Real.exp (|t| * δ)) (r := 1 - A) hδ0 hrate hdiff hbound
    -- identify the height-zero integral with XiC
    have hFL : (∫ x : ℝ, thetaStripKernel w ((x : ℝ) : ℂ)) = XiC w := by
      rw [integral_thetaStripKernel_real]
      refine thetaCuspFourierLaplace_eq_XiC_on_strip ?_
      rw [thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq, hwim]
      constructor <;> [linarith [abs_le.mp ha]; linarith [abs_le.mp ha]]
    rw [← hFL, ← hshift]
    have hmaj : Integrable (fun x : ℝ =>
        (CK * Real.exp (t * δ)) * Real.exp (-((1 - A) * |x|))) :=
      (integrable_exp_neg_mul_abs' hrate).const_mul _
    have hbd : ∀ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖ ≤
        (CK * Real.exp (t * δ)) * Real.exp (-((1 - A) * |x|)) := by
      intro x
      have him : |((x : ℂ) + (δ : ℂ) * Complex.I).im| ≤ δ := by
        simpa using le_of_eq (abs_of_nonneg hδ0)
      have hval : ((x : ℂ) + (δ : ℂ) * Complex.I).im = δ := by simp
      have hre : ((x : ℂ) + (δ : ℂ) * Complex.I).re = x := by simp
      have := hgen (t * δ) _ (by rw [hval]) him
      rwa [hre] at this
    calc ‖∫ x : ℝ, thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖
        ≤ ∫ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, (CK * Real.exp (t * δ)) * Real.exp (-((1 - A) * |x|)) := by
          refine integral_mono ?_ hmaj hbd
          refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun x => ?_)
          · have hcont : Continuous
                (fun x : ℝ => thetaStripKernel w ((x : ℂ) + (δ : ℂ) * Complex.I)) := by
              refine continuous_iff_continuousAt.mpr fun x => ?_
              have hmem : |((x : ℂ) + (δ : ℂ) * Complex.I).im| ≤ δ := by
                simpa using le_of_eq (abs_of_nonneg hδ0)
              have hcomp := ((hdiff _ hmem).continuousAt).comp (x := x)
                (f := fun y : ℝ => ((y : ℂ) + (δ : ℂ) * Complex.I)) (by fun_prop)
              simpa [Function.comp_def] using hcomp
            exact hcont.norm.aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact hbd x
      _ = (CK * Real.exp (t * δ)) * B := by
          rw [MeasureTheory.integral_const_mul, ← hB]
      _ = CK * B * Real.exp (-(δ * |t|)) := by
          rw [abs_of_nonpos ht]
          ring_nf
  intro t a ha
  rcases le_or_gt t 0 with ht | ht
  · exact hcore t a ht ha
  · have heven : XiC ((t : ℂ) + (a : ℂ) * Complex.I) =
        XiC (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) := by
      rw [show (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) =
        -((t : ℂ) + (a : ℂ) * Complex.I) by push_cast; ring, XiC_even]
    rw [heven]
    have hna : |(-a)| ≤ A := by rwa [abs_neg]
    have := hcore (-t) (-a) (by linarith) hna
    rwa [abs_neg] at this

end RHTower
