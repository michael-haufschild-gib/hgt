import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay

/-!
# Rapid moments for the finite translation edge

The raw theta tail decays at every prescribed natural exponential rate.  Consequently its
moments, after division by the Taylor factorial, have any fixed geometric rate.  Choosing that
rate above the bounded spectral fibre is the quantitative input for controlling logarithmic
translation edges whose displacement is only logarithmic in the Taylor degree.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Absolute raw-tail moments at an arbitrary natural exponential rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  let C : ℝ := thetaCuspTailNatExpConstant p
  have hf : IntegrableOn
      (fun x : ℝ => |x ^ m * thetaCuspTailDerivative 0 x|) (Ioi 0) := by
    simpa only [Real.norm_eq_abs] using
      (integrableOn_pow_mul_thetaCuspTailDerivative m 0).norm
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_pow_mul_exp_nat_neg m p hp]
    positivity
  have hg : IntegrableOn
      (fun x : ℝ => C * (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    hbase.const_mul C
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        ∫ x : ℝ in Ioi 0,
          C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have htail := abs_thetaCuspTailDerivative_zero_le_nat_exp_neg p hx0
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      calc
        x ^ m * |thetaCuspTailDerivative 0 x| ≤
            x ^ m * (C * Real.exp (-(p : ℝ) * x)) :=
          mul_le_mul_of_nonneg_left htail (pow_nonneg hx0 _)
        _ = C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by ring
    _ = thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
      rw [integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

/-- Normalizing by the Taylor factorial leaves a freely prescribed geometric moment rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_div_factorial_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) /
        (m.factorial : ℝ) ≤
      thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1) := by
  have h := integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate m p hp
  have hfac : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hfac]
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := h
    _ = (thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1)) *
          (m.factorial : ℝ) := by ring

/-- Double integration by parts on a positive half-line, with all four endpoint values retained.
This abstract form is used for translated theta potentials: it prevents a seam term from being
silently lost when a reflected Haar packet is moved back to the positive source half-line. -/
theorem integral_Ioi_secondDerivative_mul_eq_boundary_add
    {a : ℝ} {f f' f'' : ℝ → ℂ} {g g' g'' : ℝ → ℂ}
    {A₁ B₁ A₂ B₂ : ℂ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioi a, HasDerivAt f' (f'' x) x)
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, HasDerivAt g' (g'' x) x)
    (hgf'' : IntegrableOn (g * f'') (Ioi a))
    (hg'f' : IntegrableOn (g' * f') (Ioi a))
    (hg''f : IntegrableOn (g'' * f) (Ioi a))
    (hzero₁ : Tendsto (g * f') (𝓝[>] a) (𝓝 A₁))
    (hinfty₁ : Tendsto (g * f') atTop (𝓝 B₁))
    (hzero₂ : Tendsto (g' * f) (𝓝[>] a) (𝓝 A₂))
    (hinfty₂ : Tendsto (g' * f) atTop (𝓝 B₂)) :
    (∫ x : ℝ in Ioi a, f'' x * g x) =
      (B₁ - A₁) - (B₂ - A₂) +
        ∫ x : ℝ in Ioi a, f x * g'' x := by
  have hfirst := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg hf' hgf'' hg'f' hzero₁ hinfty₁
  have hsecond := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg' hf hg'f' hg''f hzero₂ hinfty₂
  rw [show (∫ x : ℝ in Ioi a, f'' x * g x) =
      ∫ x : ℝ in Ioi a, g x * f'' x by
        apply integral_congr_ae
        filter_upwards [] with x
        ring,
    hfirst, hsecond]
  have hcomm : (∫ x : ℝ in Ioi a, g'' x * f x) =
      ∫ x : ℝ in Ioi a, f x * g'' x := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hcomm]
  ring

end


end RHTower
