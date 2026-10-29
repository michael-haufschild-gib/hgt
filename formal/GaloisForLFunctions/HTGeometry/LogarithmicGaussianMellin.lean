import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin
import GaloisForLFunctions.RHTower.RiemannKernelWeilRadical
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Gamma integrals in logarithmic Gaussian coordinates

The substitution `t = exp(2u)` preserves absolute Mellin convergence.
The resulting density `exp(2zu) exp(-c exp(2u))` has integral
`c^(-z) Gamma(z) / 2`. Its real and complex archimedean specializations
are `GammaR/2` and `GammaC/4` in Mathlib's normalization. Finite-product
Fubini proves absolute convergence and the product formula.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry

/-- Absolute Mellin convergence is equivalent to integrability after `t = exp(2u)`. -/
theorem mellinConvergent_iff_integrable_exp_two (f : ℝ → ℂ) (z : ℂ) :
    MellinConvergent f z ↔
      Integrable (fun u : ℝ => Complex.exp (2 * z * (u : ℂ)) * f (Real.exp (2 * u))) := by
  rw [MellinConvergent, RHTower.integrableOn_Ioi_iff_integrable_exp_smul]
  have he (u : ℝ) : Real.exp u • (((Real.exp u : ℝ) : ℂ) ^ (z - 1) • f (Real.exp u)) =
      Complex.exp (z * (u : ℂ)) * f (Real.exp u) := by
    simp only [Complex.real_smul, smul_eq_mul]
    rw [RHTower.ofReal_rexp_cpow_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [he]
  have hscale := integrable_comp_mul_left_iff
    (fun u : ℝ => Complex.exp (z * (u : ℂ)) * f (Real.exp u)) (by norm_num : (2 : ℝ) ≠ 0)
  have hfun : (fun u : ℝ => Complex.exp (z * ((2 * u : ℝ) : ℂ)) * f (Real.exp (2 * u))) =
      (fun u : ℝ => Complex.exp (2 * z * (u : ℂ)) * f (Real.exp (2 * u))) := by
    funext u
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 2
    ring
  rw [hfun] at hscale
  exact hscale.symm

/-- A Gaussian Mellin density after the logarithmic substitution `t = exp(2u)`. -/
def logGaussianMellinKernel (c : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (2 * z * (u : ℂ)) * (Real.exp (-(c * Real.exp (2 * u))) : ℂ)

/-- Positive Gaussian rate and positive real Mellin exponent give absolute convergence. -/
theorem integrable_logGaussianMellinKernel {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 0 < z.re) : Integrable (logGaussianMellinKernel c z) := by
  exact (mellinConvergent_iff_integrable_exp_two _ z).mp
    (RHTower.mellinConvergent_exp_neg_mul hc hz)

/-- The logarithmic Gaussian integral is exactly half the scaled Gamma integral. -/
theorem integral_logGaussianMellinKernel {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ u : ℝ, logGaussianMellinKernel c z u) =
      (c : ℂ) ^ (-z) * Complex.Gamma z / 2 := by
  have h := RHTower.mellin_eq_integral_exp_two
    (fun t : ℝ => (Real.exp (-(c * t)) : ℂ)) z
  rw [RHTower.mellin_exp_neg_mul_finiteExponentialSumMellin hc hz] at h
  change (c : ℂ) ^ (-z) * Complex.Gamma z =
    2 * (∫ u : ℝ, logGaussianMellinKernel c z u) at h
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  exact (mul_comm _ _).trans h.symm

/-- A real place contributes half of its standard shifted real Gamma factor. -/
theorem integral_logGaussianMellinKernel_real {s : ℂ} (hs : 0 < s.re) (e : ℕ) :
    (∫ u : ℝ, logGaussianMellinKernel Real.pi ((s + e) / 2) u) =
      Complex.Gammaℝ (s + e) / 2 := by
  have hz : 0 < ((s + (e : ℂ)) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re]
    exact div_pos (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg e)) zero_lt_two
  rw [integral_logGaussianMellinKernel Real.pi_pos hz, Complex.Gammaℝ_def]
  simp only [neg_div]

/-- A complex place contributes one quarter of Mathlib's standard complex Gamma factor. -/
theorem integral_logGaussianMellinKernel_complex {s : ℂ} (hs : 0 < s.re) :
    (∫ u : ℝ, logGaussianMellinKernel (2 * Real.pi) s u) = Complex.Gammaℂ s / 4 := by
  rw [integral_logGaussianMellinKernel (mul_pos zero_lt_two Real.pi_pos) hs, Complex.Gammaℂ_def]
  push_cast
  ring

/-- Finite coordinate products of the logarithmic Gaussian densities are absolutely integrable. -/
theorem integrable_logGaussianMellinProduct {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (z : ι → ℂ) (hc : ∀ i, 0 < c i) (hz : ∀ i, 0 < (z i).re) :
    Integrable (fun u : ι → ℝ => ∏ i, logGaussianMellinKernel (c i) (z i) (u i)) :=
  Integrable.fintype_prod (fun i => integrable_logGaussianMellinKernel (hc i) (hz i))

/-- Finite-product Fubini gives the exact product of scaled Gamma factors. -/
theorem integral_logGaussianMellinProduct {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (z : ι → ℂ) (hc : ∀ i, 0 < c i) (hz : ∀ i, 0 < (z i).re) :
    (∫ u : ι → ℝ, ∏ i, logGaussianMellinKernel (c i) (z i) (u i)) =
      ∏ i, (c i : ℂ) ^ (-z i) * Complex.Gamma (z i) / 2 := by
  rw [integral_fintype_prod_volume_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_logGaussianMellinKernel (hc i) (hz i)

end GaloisForLFunctions.HTGeometry