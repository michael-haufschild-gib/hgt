import GaloisForLFunctions.RHTower.ConstrainedWeilFourierMultiplier
import GaloisForLFunctions.HTGeometry.GoldenRuleSelfEnergy
import GaloisForLFunctions.RHTower.XiMassPrimeSquareAsymptoticCarrier

/-!
# The pole and regular limit of the square-prime boundary

At abscissa 1 + 4 pi epsilon, the literal square-prime pole is half the
Poisson kernel in Fourier frequency. Its limit retains half the squared
mean of the original test. The regular zeta boundary is controlled by a
proved polynomial envelope, which is integrable against every Schwartz
spectral density; dominated convergence therefore removes its damping.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap Complex
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The literal pole multiplier at abscissa `1+4*pi*epsilon` and height `4*pi*xi`. -/
def squarePrimePoleMultiplier (ε ξ : ℝ) : ℝ :=
  2 * ((((4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹).re

theorem squarePrimePoleMultiplier_eq_half_poisson {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    squarePrimePoleMultiplier ε ξ = (1 / 2 : ℝ) * HTGeometry.halfPlanePoisson ε ξ := by
  have hp := Real.pi_pos
  have hd : ε ^ 2 + ξ ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < ε ^ 2 + ξ ^ 2)
  simp only [squarePrimePoleMultiplier, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, zero_add, mul_one,
    HTGeometry.halfPlanePoisson]
  have he : (4 * Real.pi * ε) * (4 * Real.pi * ε) + (4 * Real.pi * ξ) * (4 * Real.pi * ξ) =
      (4 * Real.pi) ^ 2 * (ε ^ 2 + ξ ^ 2) := by ring
  rw [he]
  field_simp [hp.ne', hd]
  ring

theorem integrable_squarePrimePole_spectralDensity (u : SchwartzMap ℝ ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ξ : ℝ => squarePrimePoleMultiplier ε ξ *
      ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2) := by
  have hp := (RHTower.integrable_spectralDensity u).bdd_mul
    (c := 1 / (Real.pi * ε))
    (HTGeometry.continuous_halfPlanePoisson hε).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (HTGeometry.halfPlanePoisson_pos hε ξ).le]
      exact HTGeometry.halfPlanePoisson_le hε ξ)
  refine (hp.const_mul (1 / 2 : ℝ)).congr ?_
  filter_upwards with ξ
  rw [squarePrimePoleMultiplier_eq_half_poisson hε]
  ring

/-- The square-prime pole leaves exactly half the squared mean of the original Schwartz test. -/
theorem tendsto_squarePrime_pole_meanSquare (u : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => ∫ ξ : ℝ,
      squarePrimePoleMultiplier ε ξ * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 ((1 / 2 : ℝ) * ‖∫ x : ℝ, u x‖ ^ 2)) := by
  have h := (HTGeometry.tendsto_halfPlanePoisson_weight
    (RHTower.integrable_spectralDensity u)
    (RHTower.continuous_spectralDensity u).continuousAt).const_mul (1 / 2 : ℝ)
  have hz : 𝓕 (u : ℝ → ℂ) 0 = ∫ x : ℝ, u x := by
    rw [Real.fourier_eq]
    simp
  rw [hz] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [squarePrimePoleMultiplier_eq_half_poisson hε]
  ring

/-- Every polynomial envelope is integrable against the actual Schwartz spectral density. -/
theorem integrable_polynomial_spectralDensity (u : SchwartzMap ℝ ℂ) (c : ℝ) (k : ℕ) :
    Integrable (fun ξ : ℝ => (1 + |c * ξ|) ^ k * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2) := by
  let F : SchwartzMap ℝ ℂ := fourier (SchwartzMap.autocorrelationSchwartz u)
  let PF : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ
    (fun ξ : ℝ => (((2 + (c * ξ) ^ 2) ^ k : ℝ) : ℂ)) F
  have hF (ξ : ℝ) : ‖F ξ‖ = ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
    dsimp only [F]
    rw [SchwartzMap.fourier_coe]
    exact RHTower.norm_fourier_autocorrelationSchwartz u ξ
  have hPF (ξ : ℝ) : ‖PF ξ‖ = (2 + (c * ξ) ^ 2) ^ k * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
    have he : PF ξ = (((2 + (c * ξ) ^ 2) ^ k : ℝ) : ℂ) • F ξ :=
      SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) F ξ
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (2 + (c * ξ) ^ 2) ^ k), hF]
  refine PF.integrable.norm.mono' ?_ ?_
  · exact (((continuous_const.add ((continuous_const.mul continuous_id).abs)).pow k).mul
      (RHTower.continuous_spectralDensity u)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hPF]
    have hp : 1 + |c * ξ| ≤ 2 + (c * ξ) ^ 2 := by
      nlinarith only [sq_nonneg (|c * ξ| - 1), sq_abs (c * ξ), sq_nonneg (c * ξ)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp k) (sq_nonneg _)

private theorem regular_zeta_differentiable_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ RHTower.Sieve.zetaLogDerivReg s := by
  by_cases h1 : s = 1
  · subst s
    exact RHTower.Sieve.differentiableAt_zetaLogDerivReg_one
  · exact RHTower.Sieve.differentiableAt_zetaLogDerivReg
      ((RHTower.Sieve.zetaResidueUnit_ne_zero_iff h1).mpr
        (riemannZeta_ne_zero_of_one_le_re hs))

/-- The regular square source paired with the original spectral density before removing damping. -/
def regularSquareDampedSpectralDensity (u : SchwartzMap ℝ ℂ) (ε ξ : ℝ) : ℝ :=
  2 * (RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re *
    ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2

private theorem continuous_regularSquareDampedSpectralDensity (u : SchwartzMap ℝ ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) : Continuous (regularSquareDampedSpectralDensity u ε) := by
  have hreg : Continuous (fun ξ : ℝ => RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro ξ
    have hs : 1 ≤ ((((1 + 4 * Real.pi * ε : ℝ) : ℂ) +
        ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hε)
    exact ContinuousAt.comp (f := fun ξ : ℝ =>
        (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I))
      (regular_zeta_differentiable_of_one_le_re hs).continuousAt (by fun_prop)
  exact ((Complex.continuous_re.comp hreg).const_mul 2).mul
    (RHTower.continuous_spectralDensity u)

/-- The regular boundary pairing is absolutely integrable at every nonnegative damping. -/
theorem integrable_regularSquareDampedSpectralDensity (u : SchwartzMap ℝ ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) : Integrable (regularSquareDampedSpectralDensity u ε) := by
  have hσ : 1 ≤ 1 + 4 * Real.pi * ε :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) hε)
  obtain ⟨K, _hK, hreg⟩ :=
    RHTower.exists_norm_zetaLogDerivReg_right_envelope (1 + 4 * Real.pi * ε) hσ
  refine ((integrable_polynomial_spectralDensity u (4 * Real.pi) 9).const_mul (2 * K)).mono'
    (continuous_regularSquareDampedSpectralDensity u hε).aestronglyMeasurable ?_
  filter_upwards with ξ
  have hb := (Complex.abs_re_le_norm (RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I))).trans
    (hreg (1 + 4 * Real.pi * ε) hσ le_rfl (4 * Real.pi * ξ))
  rw [regularSquareDampedSpectralDensity, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg ‖𝓕 (u : ℝ → ℂ) ξ‖)]
  calc
    _ ≤ 2 * (K * (1 + |4 * Real.pi * ξ|) ^ 9) * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

private theorem continuousAt_regularSquareDampedSpectralDensity_zero
    (u : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ContinuousAt (fun ε : ℝ => regularSquareDampedSpectralDensity u ε ξ) 0 := by
  have hs : 1 ≤ ((((1 + 4 * Real.pi * (0 : ℝ) : ℝ) : ℂ) +
      ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re := by simp
  have hpath : ContinuousAt (fun ε : ℝ =>
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)) 0 := by fun_prop
  have hreg : ContinuousAt (fun ε : ℝ => RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)) 0 :=
    ContinuousAt.comp (f := fun ε : ℝ =>
        (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I))
      (regular_zeta_differentiable_of_one_le_re hs).continuousAt hpath
  have hreal : ContinuousAt (fun ε : ℝ => (RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re) 0 :=
    ContinuousAt.comp (f := fun ε : ℝ => RHTower.Sieve.zetaLogDerivReg
        (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I))
      Complex.continuous_re.continuousAt hreg
  exact (hreal.const_mul 2).mul_const _

/-- Damping can be removed from the regular square-boundary pairing by a proved Schwartz majorant. -/
theorem tendsto_integral_regularSquareDampedSpectralDensity (u : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => ∫ ξ : ℝ, regularSquareDampedSpectralDensity u ε ξ)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (𝓝 (∫ ξ : ℝ, regularSquareDampedSpectralDensity u 0 ξ)) := by
  obtain ⟨K, _hK, hreg⟩ := RHTower.exists_norm_zetaLogDerivReg_right_envelope 2 (by norm_num)
  let B : ℝ → ℝ := fun ξ => (2 * K) * ((1 + |(4 * Real.pi) * ξ|) ^ 9 *
    ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2)
  apply tendsto_integral_filter_of_dominated_convergence B
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (continuous_regularSquareDampedSpectralDensity u hε.le).aestronglyMeasurable
  · have hπ : 0 < 4 * Real.pi := by positivity
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / (4 * Real.pi) by positivity)] with ε hε
    have hσ1 : 1 ≤ 1 + 4 * Real.pi * ε :=
      le_add_of_nonneg_right (mul_nonneg (by positivity) hε.1.le)
    have hprod : 4 * Real.pi * ε ≤ 1 := by
      simpa only [mul_comm] using (le_div_iff₀ hπ).mp hε.2
    have hσ2 : 1 + 4 * Real.pi * ε ≤ (2 : ℝ) := by linarith only [hprod]
    filter_upwards with ξ
    have hb := (Complex.abs_re_le_norm (RHTower.Sieve.zetaLogDerivReg
      (((1 + 4 * Real.pi * ε : ℝ) : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I))).trans
        (hreg (1 + 4 * Real.pi * ε) hσ1 hσ2 (4 * Real.pi * ξ))
    rw [regularSquareDampedSpectralDensity, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg ‖𝓕 (u : ℝ → ℂ) ξ‖)]
    calc
      _ ≤ 2 * (K * (1 + |4 * Real.pi * ξ|) ^ 9) * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (sq_nonneg _)
      _ = B ξ := by dsimp only [B]; ring
  · exact (integrable_polynomial_spectralDensity u (4 * Real.pi) 9).const_mul (2 * K)
  · filter_upwards with ξ
    exact (continuousAt_regularSquareDampedSpectralDensity_zero u ξ).mono_left nhdsWithin_le_nhds

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.tendsto_squarePrime_pole_meanSquare
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integrable_squarePrimePole_spectralDensity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integrable_polynomial_spectralDensity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integrable_regularSquareDampedSpectralDensity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.tendsto_integral_regularSquareDampedSpectralDensity
