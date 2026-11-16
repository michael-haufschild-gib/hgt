import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularFourierProfiles
import GaloisForLFunctions.FamilyContinuationTheory.AngularHarmonicGaussian

/-! # Mellin transform of an even angular Fourier profile

Pairing with holomorphic Gaussians reduces the trace-Fourier transform to reciprocal
Laplace scaling. Mellin transformation gives the shifted Gamma quotient and proves
positivity of the cubic residue normalizer at every sextic angular weight.
-/

noncomputable section
open Complex MeasureTheory Filter Asymptotics Set
open scoped Classical SchwartzMap FourierTransform ComplexConjugate Topology

namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open MetaplecticMobiusDescent.CubicEisenstein.ProbeRadialMellin
open MetaplecticMobiusDescent.QuarticPoisson

theorem paperAngularFourier_continuous (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) :
    Continuous (paperAngularFourier k W) := by
  have hp : Continuous (fun t : ℝ => paperFrequency (Real.sqrt t : ℂ)) := by
    unfold paperFrequency
    fun_prop
  have hh := ((annularFourierCLM k W).continuous.comp hp).const_smul (2 / Real.sqrt 3 : ℝ)
  have he : paperAngularFourier k W = fun t : ℝ =>
      (2 / Real.sqrt 3 : ℝ) • annularFourierCLM k W (paperFrequency (Real.sqrt t : ℂ)) :=
    funext (paperAngularFourier_eq_plane k W hW)
  rw [he]
  exact hh

theorem paperAngularFourier_isBigO_top (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) (A : ℕ) :
    paperAngularFourier k W =O[atTop] (fun r : ℝ => r ^ (-(A : ℝ))) := by
  let C := (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
    (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ) (annularFourierCLM k W)
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb := paperAngularFourier_weighted_bound k W hW A r hr.le
  have hp : r ^ A * ‖paperAngularFourier k W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hr.le (by linarith : r ≤ 1 + r) A) (norm_nonneg _)).trans hb
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa only [mul_comm] using hp)

theorem paperAngularFourier_isBigO_zero (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) :
    paperAngularFourier k W =O[𝓝[>] 0] (fun r : ℝ => r ^ (-(0 : ℝ))) := by
  let C := (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * 0) *
    (Finset.Iic (2 * 0, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ) (annularFourierCLM k W)
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa only [pow_zero, one_mul, neg_zero, Real.rpow_zero, norm_one, mul_one] using
    paperAngularFourier_weighted_bound k W hW 0 r hr.le

theorem paperAngularFourier_mellin_convergent (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) (z : ℂ) (hz : 0 < z.re) :
    MellinConvergent (paperAngularFourier k W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((paperAngularFourier_continuous k W hW).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (paperAngularFourier_isBigO_top k W hW A) hA (paperAngularFourier_isBigO_zero k W hW) hz

def angularPowerProfile (n : ℕ) (f : ℝ → ℂ) (r : ℝ) : ℂ := (r : ℂ) ^ n * f r

theorem mellin_angularPowerProfile (n : ℕ) (f : ℝ → ℂ) (z : ℂ) :
    mellin (angularPowerProfile n f) z = mellin f (z + n) := by
  change mellin (fun r : ℝ => (r : ℂ) ^ n * f r) z = _
  simpa only [Complex.cpow_natCast, smul_eq_mul] using
    mellin_cpow_smul f z (n : ℂ)

theorem mellinConvergent_angularPowerProfile (n : ℕ) (f : ℝ → ℂ) (z : ℂ) :
    MellinConvergent (angularPowerProfile n f) z ↔ MellinConvergent f (z + n) := by
  change MellinConvergent (fun r : ℝ => (r : ℂ) ^ n * f r) z ↔ _
  simpa only [Complex.cpow_natCast, smul_eq_mul] using
    (MellinConvergent.cpow_smul (f := f) (s := z) (a := (n : ℂ)))

private theorem conj_direction_mul (u : ℂ) :
    (conj u / (‖u‖ : ℂ)) * u = (‖u‖ : ℂ) := by
  by_cases hu : u = 0
  · simp only [hu, norm_zero, Complex.ofReal_zero, mul_zero]
  · rw [div_mul_eq_mul_div, Complex.conj_mul', pow_two,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))]

private theorem direction_mul_conj (u : ℂ) :
    (u / (‖u‖ : ℂ)) * conj u = (‖u‖ : ℂ) := by
  by_cases hu : u = 0
  · simp only [hu, norm_zero, Complex.ofReal_zero, map_zero, mul_zero]
  · rw [div_mul_eq_mul_div, Complex.mul_conj', pow_two,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))]

/-- Harmonic-Gaussian pairing turns angular Fourier reflection into one-dimensional
Laplace inversion with the exact weight-dependent power. -/
theorem angular_laplace_duality (n : ℕ) (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    laplace (angularPowerProfile n (paperAngularFourier (2 * n) W)) t =
      ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
        laplace (angularPowerProfile n W) (paperConstant ^ 2 / t) := by
  have hg : Integrable (fun z : ℂ => z ^ (2 * n) * Complex.exp (-(t : ℂ) * ‖z‖ ^ 2)) := by
    have h := integrable_holomorphic_gaussian (2 * n) (t / Real.pi) (div_pos ht Real.pi_pos)
    rwa [show Real.pi * (t / Real.pi) = t by field_simp] at h
  have h := paper_fourier_pairing _ _ (integrable_angularRadial (2 * n) W) hg
  have hp (u : ℂ) : (conj u / (‖u‖ : ℂ)) ^ (2 * n) * u ^ (2 * n) =
      ((‖u‖ ^ 2 : ℝ) : ℂ) ^ n := by
    rw [← mul_pow, conj_direction_mul, pow_mul, Complex.ofReal_pow]
  have hq (u : ℂ) : (u / (‖u‖ : ℂ)) ^ (2 * n) * conj u ^ (2 * n) =
      ((‖u‖ ^ 2 : ℝ) : ℂ) ^ n := by
    rw [← mul_pow, direction_mul_conj, pow_mul, Complex.ofReal_pow]
  have hleft : (∫ u : ℂ, paperFourier (angularRadial (2 * n) W) u *
      (u ^ (2 * n) * Complex.exp (-(t : ℂ) * ‖u‖ ^ 2))) =
      (Real.pi : ℂ) * laplace (angularPowerProfile n (paperAngularFourier (2 * n) W)) t := by
    rw [laplace, ← integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      rw [paperFourier_angular]
      dsimp only [angularPowerProfile]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]
      calc
        _ = ((conj u / (‖u‖ : ℂ)) ^ (2 * n) * u ^ (2 * n)) *
            paperAngularFourier (2 * n) W (‖u‖ ^ 2) *
            Complex.exp (-(t : ℂ) * ‖u‖ ^ 2) := by ring
        _ = _ := by rw [hp, Complex.ofReal_pow]; simp only [neg_mul]
  have hright : (∫ z : ℂ, angularRadial (2 * n) W z *
      paperFourier (fun u : ℂ => u ^ (2 * n) * Complex.exp (-(t : ℂ) * ‖u‖ ^ 2)) z) =
      (Real.pi : ℂ) * (((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
        laplace (angularPowerProfile n W) (paperConstant ^ 2 / t)) := by
    simp_rw [paperFourier_even_harmonic_gaussian n t ht]
    rw [laplace, ← integral_const_mul, ← integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only [angularRadial, angularPowerProfile]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]
      calc
        _ = ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
            (((u / (‖u‖ : ℂ)) ^ (2 * n) * conj u ^ (2 * n)) * W (‖u‖ ^ 2) *
              Complex.exp (-((paperConstant ^ 2 / t : ℝ) : ℂ) * ‖u‖ ^ 2)) := by ring
        _ = _ := by rw [hq, Complex.ofReal_pow]; simp only [neg_mul]
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

private theorem mellin_angular_reciprocal_laplace (n : ℕ) (f : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
      laplace f (paperConstant ^ 2 / t)) (1 - z + n) =
      (paperConstant : ℂ) ^ (1 - 2 * z) * mellin (laplace f) (z + n) := by
  have hfun : (fun t : ℝ => ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
      laplace f (paperConstant ^ 2 / t)) =
      fun t : ℝ => (paperConstant : ℂ) ^ (2 * n + 1) •
        ((t : ℂ) ^ (-((2 * n + 1 : ℕ) : ℂ)) • laplace f (paperConstant ^ 2 * t⁻¹)) := by
    funext t
    simp only [Complex.cpow_neg, Complex.cpow_natCast, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv, smul_eq_mul]
    ring
  rw [hfun, mellin_const_smul, mellin_cpow_smul,
    show 1 - z + (n : ℂ) + -((2 * n + 1 : ℕ) : ℂ) = -(z + n) by push_cast; ring]
  rw [mellin_comp_inv (fun t : ℝ => laplace f (paperConstant ^ 2 * t)) (-(z + n)), neg_neg,
    mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  have hp : (paperConstant : ℂ) ^ (2 * n + 1) *
      ((paperConstant ^ 2 : ℝ) : ℂ) ^ (-(z + n)) =
      (paperConstant : ℂ) ^ (1 - 2 * z) := by
    rw [pow_succ, mul_assoc, paper_prefactor]
    rw [← Complex.cpow_natCast,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne')]
    congr 1
    push_cast
    ring
  rw [← mul_assoc, hp]

/-- The even angular Fourier Mellin factor is a shifted Gamma quotient. Its strip contains
the cubic detector residue for every sextic infinity type. -/
theorem angular_mellin_gamma (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < (n : ℝ) + 1) :
    mellin (paperAngularFourier (2 * n) W) z =
      ((paperConstant : ℂ) ^ (1 - 2 * z) * Complex.Gamma (z + n) /
        Complex.Gamma (1 - z + n)) * mellin W (1 - z) := by
  have hc := compact_source_mellin_convergent W (1 / 2) 2 (by norm_num) hW
    (W.smooth ⊤) (1 - z)
  have hL := mellin_laplace (angularPowerProfile n (paperAngularFourier (2 * n) W))
    (1 - z + n) (by simp only [add_re, sub_re, one_re, natCast_re]; linarith)
    (((Complex.continuous_ofReal.pow n).mul
      (paperAngularFourier_continuous (2 * n) W hW)).aestronglyMeasurable)
    (by
      rw [mellinConvergent_angularPowerProfile,
        show 1 - (1 - z + (n : ℂ)) + n = z by ring]
      exact paperAngularFourier_mellin_convergent (2 * n) W hW z hz)
  have hR := mellin_laplace (angularPowerProfile n W) (z + n)
    (by simp only [add_re, natCast_re]; exact add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n))
    (((Complex.continuous_ofReal.pow n).mul W.continuous).aestronglyMeasurable)
    (by
      rw [mellinConvergent_angularPowerProfile,
        show 1 - (z + (n : ℂ)) + n = 1 - z by ring]
      exact hc)
  have he : mellin (laplace (angularPowerProfile n (paperAngularFourier (2 * n) W)))
      (1 - z + n) =
      mellin (fun t : ℝ => ((paperConstant / t : ℝ) : ℂ) ^ (2 * n + 1) *
        laplace (angularPowerProfile n W) (paperConstant ^ 2 / t)) (1 - z + n) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [angular_laplace_duality n W t ht]
  rw [hL, mellin_angular_reciprocal_laplace, hR, mellin_angularPowerProfile,
    mellin_angularPowerProfile,
    show 1 - (1 - z + (n : ℂ)) + n = z by ring,
    show 1 - (z + (n : ℂ)) + n = 1 - z by ring] at he
  have hg : Complex.Gamma (1 - z + n) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [add_re, sub_re, one_re, natCast_re]
    linarith)
  apply mul_left_cancel₀ hg
  rw [he]
  field_simp

/-- Positive annular data have a positive real Mellin transform after every even angular
reflection throughout its positive Gamma strip. -/
theorem angular_mellin_positive (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2)
    (hreal : ∀ r, (W r).im = 0) (hnonneg : ∀ r, 0 ≤ (W r).re) (hne : W ≠ 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < (n : ℝ) + 1) :
    0 < (mellin (paperAngularFourier (2 * n) W) (s : ℂ)).re ∧
      (mellin (paperAngularFourier (2 * n) W) (s : ℂ)).im = 0 := by
  obtain ⟨hp, hz⟩ := positive_source_mellin W (1 / 2) 2 (by norm_num) hW
    hreal hnonneg hne (1 - s)
  have hh : mellin W (1 - (s : ℂ)) = ((mellin W ((1 - s : ℝ) : ℂ)).re : ℂ) := by
    rw [show 1 - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ext (by simp) (by simpa using hz)
  rw [angular_mellin_gamma n W hW (s : ℂ) hs hs1, hh]
  have hpow : (paperConstant : ℂ) ^ (1 - 2 * (s : ℂ)) =
      ((paperConstant ^ (1 - 2 * s) : ℝ) : ℂ) := by
    rw [show 1 - 2 * (s : ℂ) = ((1 - 2 * s : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow paperConstant_pos.le]
  rw [hpow, show (s : ℂ) + n = ((s + n : ℝ) : ℂ) by push_cast; rfl,
    show 1 - (s : ℂ) + n = ((1 - s + n : ℝ) : ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_im, and_true]
  exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos paperConstant_pos _)
    (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by linarith))) hp

/-- The cubic residue normalizer survives every sextic angular weight. -/
theorem angular_mellin_one_sixth_pos (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2)
    (hreal : ∀ r, (W r).im = 0) (hnonneg : ∀ r, 0 ≤ (W r).re) (hne : W ≠ 0) :
    0 < (mellin (paperAngularFourier (6 * k) W) (1 / 6)).re ∧
      (mellin (paperAngularFourier (6 * k) W) (1 / 6)).im = 0 := by
  simpa only [show 2 * (3 * k) = 6 * k by omega, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using
    angular_mellin_positive (3 * k) W hW hreal hnonneg hne (1 / 6)
      (by norm_num) (by have hn : (0 : ℝ) ≤ ((3 * k : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)

end GaloisForLFunctions.FamilyContinuationTheory
