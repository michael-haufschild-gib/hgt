import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal
import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The real-axis mass test is continuous. -/
private theorem continuous_xiMassAnalyticTest_real
    {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    Continuous (fun x : ℝ => xiMassAnalyticTest a τ (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    change HasDerivAt (⇑Complex.ofRealCLM) 1 x
    exact Complex.ofRealCLM.hasDerivAt
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  exact ((hasDerivAt_xiMassAnalyticTest ha τ hmem).comp x hz).continuousAt

/-- At real frequency, the actual mass-test Fourier kernel is integrable on every
positive vertical time line. -/
private theorem integrable_xiMassAnalyticTest_fourierKernel_real
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u w : ℝ) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((σ : ℂ) + u * I) x *
        Complex.exp (-(I * (w : ℂ) * x))) := by
  apply Integrable.mono' (integrable_exp_neg_mul_abs hσ)
  · exact ((continuous_xiMassAnalyticTest_real ha _).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
    rw [norm_mul, Complex.norm_exp]
    have hphase : (-(I * (w : ℂ) * (x : ℂ))).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
    simpa using hg

/-- The real Fourier phase is one-Lipschitz in frequency, with exact spatial cost `|x|`. -/
theorem norm_xiMassFourierPhase_sub_le (v w x : ℝ) :
    ‖Complex.exp (-(I * (v : ℂ) * (x : ℂ))) -
        Complex.exp (-(I * (w : ℂ) * (x : ℂ)))‖ ≤
      |v - w| * |x| := by
  have hv : -(I * (v : ℂ) * (x : ℂ)) =
      ((-(v * x) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hw : -(I * (w : ℂ) * (x : ℂ)) =
      ((-(w * x) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hv, hw]
  calc
    ‖Complex.exp (((-(v * x) : ℝ) : ℂ) * I) -
        Complex.exp (((-(w * x) : ℝ) : ℂ) * I)‖ ≤
        |-(v * x) - -(w * x)| :=
      Sieve.norm_exp_phase_sub_le (-(v * x)) (-(w * x))
    _ = |v - w| * |x| := by
      rw [show -(v * x) - -(w * x) = -(v - w) * x by ring,
        abs_mul, abs_neg]

/-- **Uniform frequency Lipschitz law for the actual Xi mass Fourier integral.**

On every positive vertical time line, the Lipschitz constant is independent of the height `u`:

`‖F(v)-F(w)‖ ≤ |v-w| ∫ |x| exp(-σ|x|) dx`.
-/
theorem norm_stripFourier_xiMassAnalyticTest_sub_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u v w : ℝ) :
    ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (v : ℂ) -
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ ≤
      |v - w| *
        (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) := by
  let g : ℝ → ℂ := fun x => xiMassAnalyticTest a ((σ : ℂ) + u * I) x
  let e : ℝ → ℝ → ℂ := fun r x => Complex.exp (-(I * (r : ℂ) * (x : ℂ)))
  have hv : Integrable (fun x : ℝ => g x * e v x) := by
    simpa only [g, e] using
      integrable_xiMassAnalyticTest_fourierKernel_real ha hσ u v
  have hw : Integrable (fun x : ℝ => g x * e w x) := by
    simpa only [g, e] using
      integrable_xiMassAnalyticTest_fourierKernel_real ha hσ u w
  have hmajor : Integrable (fun x : ℝ =>
      |v - w| * (|x| * Real.exp (-(σ * |x|)))) :=
    (integrable_abs_mul_exp_neg_mul_abs hσ).const_mul |v - w|
  calc
    ‖stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (v : ℂ) -
        stripFourier (xiMassAnalyticTest a ((σ : ℂ) + u * I)) (w : ℂ)‖ =
        ‖∫ x : ℝ, g x * e v x - g x * e w x‖ := by
      rw [stripFourier, stripFourier, ← integral_sub hv hw]
    _ ≤ ∫ x : ℝ, |v - w| * (|x| * Real.exp (-(σ * |x|))) := by
      apply norm_integral_le_of_norm_le hmajor
      refine ae_of_all _ fun x => ?_
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      have hg := norm_xiMassAnalyticTest_le
        (τ := ((σ : ℂ) + u * I)) ha (by simpa using hσ.le) hmem
      have hphase := norm_xiMassFourierPhase_sub_le v w x
      have hfactor : g x * e v x - g x * e w x =
          g x * (e v x - e w x) := by ring
      rw [hfactor, norm_mul]
      calc
        ‖g x‖ * ‖e v x - e w x‖ ≤
            Real.exp (-(σ * |x|)) * (|v - w| * |x|) := by
          apply mul_le_mul
          · simpa [g] using hg
          · simpa only [e] using hphase
          · exact norm_nonneg _
          · exact Real.exp_nonneg _
        _ = |v - w| * (|x| * Real.exp (-(σ * |x|))) := by ring
    _ = |v - w| * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) := by
      rw [integral_const_mul]

end

end RHTower
