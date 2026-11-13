/-
Cusp averages and the Bessel Mellin transform adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CubeAveragesAndNormalizedGauss

/-!
# Cusp averages and the Bessel Mellin transform

Finite additive Fourier coefficients, theta twists and the ninth cusp frequency. Squarefree
times cube is the exact support of the unramified Fourier coefficients. The cubic Bessel term
has a Mellin transform absolutely convergent in its half-plane, via the Schläfli mixture.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid

/-- The coefficient size on squarefree times cube support is exactly the cube-root factor. -/
theorem sourceFourier_squarefree_cube_norm (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I) :
    ‖rationalSourceResidualFourierCoefficient (primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ =
      ‖rationalSourceThetaScalar‖ * ‖ringComplex (primaryIdealGenerator J)‖ := by
  have hp := (primaryIdealGenerator_spec I hI).2
  have hc3 : IsCoprime (3 : O) (primaryIdealGenerator I) := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 _ hp
  have hc9 : IsCoprime (9 : O) (primaryIdealGenerator I) := by
    convert hc3.mul_left hc3 using 1 <;> norm_num
  have he := congrArg norm (rationalSourceResidualFourierCoefficient_squarefree_cube I J hI hJ hsq)
  simpa only [norm_star, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    symbol_norm_one _ _ hp hc9, normalizedCubicUnitGauss_squarefree_norm I hI hsq, mul_one] using he

/-- Squarefree times cube is the exact support of the unramified Fourier coefficients. -/
theorem sourceFourier_squarefree_cube_support_iff (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0 ↔
      ∃ A B : Ideal O, Squarefree A ∧ primaryIdealGenerator A ≠ 0 ∧ primaryIdealGenerator B ≠ 0 ∧ A * B ^ 3 = I := by
  constructor
  · exact rationalSourceFourier_squarefree_cube_support I hI
  · rintro ⟨A, B, hA, hAg, hBg, hAB⟩
    have he := congrArg primaryIdealGenerator hAB
    rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow] at he
    rw [← he]
    apply norm_pos_iff.mp
    rw [sourceFourier_squarefree_cube_norm A B hAg hBg hA]
    exact mul_pos (norm_pos_iff.mpr rationalSourceThetaScalar_ne_zero)
      (norm_pos_iff.mpr (ringComplex_ne_zero hBg))

/-- The positive Gaussian Mellin integral is a scaled Gamma integral. -/
lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ) (hs : 0 < s.re) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(r : ℂ) * (x : ℂ) ^ 2)) (Ioi 0) := by
  have hs2 : 0 < (s / (2 : ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t : ℂ))) (s / 2) := by
    simpa only [MellinConvergent, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg, mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t : ℂ))) (s := s / 2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ))) (s := s) (a := 2) (by norm_num)).mpr hlinear
  simpa only [MellinConvergent, smul_eq_mul, Real.rpow_two, Complex.ofReal_mul,
    Complex.ofReal_pow, neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ) (hs : 0 < s.re) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * Complex.exp (-(r : ℂ) * (x : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * ((1 / (r : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2)) := by
  have hs2 : 0 < (s / (2 : ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r * t : ℝ) : ℂ))) s 2
  simp only [mellin, smul_eq_mul, Real.rpow_two, Complex.ofReal_mul, Complex.ofReal_pow, Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

/-- The Schläfli mixture after multiplying by the cubic Mellin weight. -/
def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t : ℂ) ^ (-(2 : ℂ) / 3) * Complex.exp (-(t : ℂ)) *
    ((x : ℂ) ^ ((s - 1 / 3) - 1) * Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * (x : ℂ) ^ 2))

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1 / 3 < s.re) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (cubicMellinMixture s t) (Ioi 0) := by
  exact (complex_gaussian_power_integrable (s - 1 / 3) (1 / (4 * t))
    (by norm_num; linarith) (by positivity)).const_mul _

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1 / 3 < s.re) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in Ioi 0, cubicMellinMixture s t x) =
      ((1 / 2 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) * Complex.Gamma ((s - 1 / 3) / 2)) *
        ((t : ℂ) ^ ((s + 1 / 3) / 2 - 1) * Complex.exp (-(t : ℂ))) := by
  simp only [cubicMellinMixture, integral_const_mul]
  rw [complex_gaussian_power_integral (s - 1 / 3) (1 / (4 * t)) (by norm_num; linarith) (by positivity)]
  have hb : (1 / (((1 / (4 * t) : ℝ) : ℂ))) = (4 : ℂ) * (t : ℂ) := by push_cast; field_simp
  have hm : ((4 : ℂ) * (t : ℂ)) ^ ((s - 1 / 3) / 2) =
      (4 : ℂ) ^ ((s - 1 / 3) / 2) * (t : ℂ) ^ ((s - 1 / 3) / 2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (4 : ℝ)) ht.le ((s - 1 / 3) / 2)
  rw [hb, hm]
  have hp : (t : ℂ) ^ (-(2 : ℂ) / 3) * (t : ℂ) ^ ((s - 1 / 3) / 2) =
      (t : ℂ) ^ ((s + 1 / 3) / 2 - 1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1 / 2 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) * Complex.Gamma ((s - 1 / 3) / 2)) *
        (((t : ℂ) ^ (-(2 : ℂ) / 3) * (t : ℂ) ^ ((s - 1 / 3) / 2)) * Complex.exp (-(t : ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    ‖cubicMellinMixture s t x‖ =
      (t ^ (-(2 : ℝ) / 3) * Real.exp (-t)) *
        (x ^ ((s.re - 1 / 3) - 1) * Real.exp (-(1 / (4 * t)) * x ^ 2)) := by
  have he : -((1 / (4 * t) : ℝ) : ℂ) * (x : ℂ) ^ 2 = (-(1 / (4 * t)) * x ^ 2 : ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture, norm_mul, he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp, Complex.ofReal_re, Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (σ r : ℝ) (hs : 0 < σ) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, x ^ (σ - 1) * Real.exp (-r * x ^ 2)) =
      r ^ (-σ / 2) * (1 / 2) * Real.Gamma (σ / 2) := by
  simpa only [Real.rpow_two, sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := σ - 1) (b := r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1 / 3 < s.re) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in Ioi 0, ‖cubicMellinMixture s t x‖) =
      ((1 / 2 : ℝ) * (4 : ℝ) ^ ((s.re - 1 / 3) / 2) * Real.Gamma ((s.re - 1 / 3) / 2)) *
        (t ^ ((s.re + 1 / 3) / 2 - 1) * Real.exp (-t)) := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (t ^ (-(2 : ℝ) / 3) * Real.exp (-t)) *
        (x ^ ((s.re - 1 / 3) - 1) * Real.exp (-(1 / (4 * t)) * x ^ 2)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => cubicMellinMixture_norm s t x ht hx)
    _ = _ := by
      rw [integral_const_mul, real_gaussian_power_integral (s.re - 1 / 3) (1 / (4 * t))
        (by linarith) (by positivity)]
      have hpow : (1 / (4 * t) : ℝ) ^ (-(s.re - 1 / 3) / 2) =
          (4 : ℝ) ^ ((s.re - 1 / 3) / 2) * t ^ ((s.re - 1 / 3) / 2) := by
        rw [show -(s.re - 1 / 3) / 2 = -((s.re - 1 / 3) / 2) by ring,
          Real.rpow_neg_eq_inv_rpow, one_div, inv_inv,
          Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) ht.le]
      rw [hpow]
      have hp : t ^ (-(2 : ℝ) / 3) * t ^ ((s.re - 1 / 3) / 2) = t ^ ((s.re + 1 / 3) / 2 - 1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1 / 2 : ℝ) * (4 : ℝ) ^ ((s.re - 1 / 3) / 2) * Real.Gamma ((s.re - 1 / 3) / 2)) *
            ((t ^ (-(2 : ℝ) / 3) * t ^ ((s.re - 1 / 3) / 2)) * Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

/-- Absolute integrability justifies exchanging the Schläfli and Mellin integrals. -/
lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1 / 3 < s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · apply ((Real.GammaIntegral_convergent (show 0 < (s.re + 1 / 3) / 2 by linarith)).const_mul
      ((1 / 2 : ℝ) * (4 : ℝ) ^ ((s.re - 1 / 3) / 2) * Real.Gamma ((s.re - 1 / 3) / 2))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioi 0, cubicMellinMixture s t x) =
      (x : ℂ) ^ ((s - 1 / 3) - 1) * schlafliIntegral (1 / 3) x := by
  rw [schlafliIntegral, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he : Complex.exp (-(t : ℂ)) * Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * (x : ℂ) ^ 2) =
      Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1 / 3 : ℂ) - 1 = -(2 : ℂ) / 3 by ring]
  unfold cubicMellinMixture
  linear_combination (t : ℂ) ^ (-(2 : ℂ) / 3) * (x : ℂ) ^ ((s - 1 / 3) - 1) * he

lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) * schlafliBesselK (1 / 3) x =
      ((1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 3 : ℂ)) * (∫ t : ℝ in Ioi 0, cubicMellinMixture s t x) := by
  rw [schlafliBesselK, cubicMellinMixture_integral_t]
  have hdiv : (x / 2 : ℂ) ^ (-(1 / 3 : ℂ)) = (x : ℂ) ^ (-(1 / 3 : ℂ)) / (2 : ℂ) ^ (-(1 / 3 : ℂ)) := by
    have hm := Complex.mul_cpow_ofReal_nonneg
      (show 0 ≤ x / 2 by positivity) (by norm_num : 0 ≤ (2 : ℝ)) (-(1 / 3 : ℂ))
    have he : ((x / 2 : ℝ) : ℂ) * (2 : ℂ) = (x : ℂ) := by push_cast; ring
    norm_num only [Complex.ofReal_ofNat] at hm
    rw [he] at hm
    apply (eq_div_iff (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).mpr
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hm.symm
  rw [hdiv, Complex.cpow_neg (2 : ℂ) (1 / 3), div_inv_eq_mul]
  have hp : (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (-(1 / 3 : ℂ)) = (x : ℂ) ^ ((s - 1 / 3) - 1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 3 : ℂ) * schlafliIntegral (1 / 3) x * hp

lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1 / 3 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * schlafliBesselK (1 / 3) x) (Ioi 0) := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 3 : ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1 / 3 < s.re) :
    (∫ t : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0, cubicMellinMixture s t x) =
      ((1 / 2 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) * Complex.Gamma ((s - 1 / 3) / 2)) *
        Complex.Gamma ((s + 1 / 3) / 2) := by
  have hB : 0 < ((s + 1 / 3) / 2).re := by norm_num; linarith
  calc
    _ = ∫ t : ℝ in Ioi 0,
        ((1 / 2 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) * Complex.Gamma ((s - 1 / 3) / 2)) *
          ((t : ℂ) ^ ((s + 1 / 3) / 2 - 1) * Complex.exp (-(t : ℂ))) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => cubicMellinMixture_integral_x s hs t ht)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral, Complex.ofReal_exp, Complex.ofReal_neg, mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

/-- The cubic Bessel Mellin transform, including absolute convergence in its full half-plane. -/
theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1 / 3 < s.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * schlafliBesselK (1 / 3) x) =
      (2 : ℂ) ^ (s - 2) * Complex.Gamma ((s - 1 / 3) / 2) * Complex.Gamma ((s + 1 / 3) / 2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := cubicMellinMixture_integrable s hs
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4 : ℂ) ^ ((s - 1 / 3) / 2) = (2 : ℂ) ^ (2 * ((s - 1 / 3) / 2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s - 1 / 3) / 2)).symm
    norm_num at hh
    exact hh
  have hprod : (2 : ℂ) ^ (1 / 3 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) = (2 : ℂ) ^ s := by
    rw [h4, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  have hscale : (1 / 4 : ℂ) * (2 : ℂ) ^ s = (2 : ℂ) ^ (s - 2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
    ring
  calc
    _ = ((1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 3 : ℂ)) *
        (∫ x : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, cubicMellinMixture s t x) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => schlafliBesselK_cubic_mellin_mixture s x hx)
    _ = ((1 / 2 : ℂ) * (2 : ℂ) ^ (1 / 3 : ℂ)) *
        (((1 / 2 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2) * Complex.Gamma ((s - 1 / 3) / 2)) *
          Complex.Gamma ((s + 1 / 3) / 2)) := by rw [hswap, cubicMellinMixture_double_integral s hs]
    _ = ((1 / 4 : ℂ) * ((2 : ℂ) ^ (1 / 3 : ℂ) * (4 : ℂ) ^ ((s - 1 / 3) / 2))) *
        Complex.Gamma ((s - 1 / 3) / 2) * Complex.Gamma ((s + 1 / 3) / 2) := by ring
    _ = _ := by rw [hprod, hscale]

lemma schlafliBesselK_cubic_scaled_mellin_integrable (s : ℂ) (c : ℝ)
    (hs : 1 / 3 < s.re) (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (s - 1) * schlafliBesselK (1 / 3) (c * v)) (Ioi 0) := by
  have hb : MellinConvergent (fun v => schlafliBesselK (1 / 3) v) s := by
    simpa only [MellinConvergent, smul_eq_mul] using schlafliBesselK_cubic_mellin_integrable s hs
  simpa only [MellinConvergent, smul_eq_mul] using
    (MellinConvergent.comp_mul_left (f := fun v => schlafliBesselK (1 / 3) v) (s := s) hc).mpr hb

lemma schlafliBesselK_cubic_scaled_mellin (s : ℂ) (c : ℝ) (hs : 1 / 3 < s.re) (hc : 0 < c) :
    (∫ v : ℝ in Ioi 0, (v : ℂ) ^ (s - 1) * schlafliBesselK (1 / 3) (c * v)) =
      (c : ℂ) ^ (-s) * ((2 : ℂ) ^ (s - 2) * Complex.Gamma ((s - 1 / 3) / 2) * Complex.Gamma ((s + 1 / 3) / 2)) := by
  have he := mellin_comp_mul_left (fun v => schlafliBesselK (1 / 3) v) s hc
  simp only [mellin, smul_eq_mul] at he
  rw [schlafliBesselK_cubic_mellin s hs] at he
  exact he

lemma source_cubic_bessel_mellin_integrable (s freq : ℂ) (hs : -(1 / 3) < s.re) (hfreq : freq ≠ 0) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (2 * s) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq‖ * v)) (Ioi 0) := by
  have hc : 0 < 4 * Real.pi * ‖freq‖ := by positivity
  have ht : 1 / 3 < (2 * s + 1).re := by norm_num; linarith
  simpa only [show (2 * s + 1 : ℂ) - 1 = 2 * s by ring] using
    schlafliBesselK_cubic_scaled_mellin_integrable (2 * s + 1) (4 * Real.pi * ‖freq‖) ht hc

/-- The exact Gamma factor for each nonzero source Fourier mode. -/
theorem source_cubic_bessel_mellin (s freq : ℂ) (hs : -(1 / 3) < s.re) (hfreq : freq ≠ 0) :
    (∫ v : ℝ in Ioi 0, (v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq‖ * v)) =
      ((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) /
        ((4 * Real.pi * ‖freq‖ : ℝ) : ℂ) ^ (2 * s + 1) := by
  have hc : 0 < 4 * Real.pi * ‖freq‖ := by positivity
  have ht : 1 / 3 < (2 * s + 1).re := by norm_num; linarith
  have he := schlafliBesselK_cubic_scaled_mellin (2 * s + 1) (4 * Real.pi * ‖freq‖) ht hc
  rw [show (2 * s + 1 : ℂ) - 1 = 2 * s by ring,
    show (2 * s + 1 : ℂ) - 2 = 2 * s - 1 by ring,
    show ((2 * s + 1 : ℂ) - 1 / 3) / 2 = s + 1 / 3 by ring,
    show ((2 * s + 1 : ℂ) + 1 / 3) / 2 = s + 2 / 3 by ring, Complex.cpow_neg] at he
  rw [he]
  ring

/-- Prime valuations determine the squarefree factor and the cube factor separately. -/
theorem squarefree_cube_decomposition_unique {A B C D : Ideal O}
    (hB : B ≠ 0) (hD : D ≠ 0) (hA : Squarefree A) (hC : Squarefree C)
    (he : A * B ^ 3 = C * D ^ 3) : A = C ∧ B = D := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hA.ne_zero (pow_ne_zero _ hB),
    normalizedFactors_mul hC.ne_zero (pow_ne_zero _ hD),
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have ha := (squarefree_iff_nodup_normalizedFactors hA.ne_zero).mp hA
  have hc := (squarefree_iff_nodup_normalizedFactors hC.ne_zero).mp hC
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors C).count P ∧
      (normalizedFactors B).count P = (normalizedFactors D).count P := by
    have hp := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hp
    have ha1 := Multiset.nodup_iff_count_le_one.mp ha P
    have hc1 := Multiset.nodup_iff_count_le_one.mp hc P
    omega
  constructor
  · calc
      A = (normalizedFactors A).prod := (Ideal.prod_normalizedFactors_eq_self hA.ne_zero).symm
      _ = (normalizedFactors C).prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hcount P).1))
      _ = C := Ideal.prod_normalizedFactors_eq_self hC.ne_zero
  · calc
      B = (normalizedFactors B).prod := (Ideal.prod_normalizedFactors_eq_self hB).symm
      _ = (normalizedFactors D).prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hcount P).2))
      _ = D := Ideal.prod_normalizedFactors_eq_self hD

/-- The primary element `ab³` determines both ideal factors. -/
theorem primary_squarefree_cube_injective :
    Function.Injective (fun p :
      {I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
      {J : Ideal O // primaryIdealGenerator J ≠ 0} =>
        primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3) := by
  intro p q he
  have hi : p.1.val * p.2.val ^ 3 = q.1.val * q.2.val ^ 3 := by
    have hs := congrArg (fun x : O => (Ideal.span {x} : Ideal O)) he
    simpa only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (primaryIdealGenerator_spec p.1.val p.1.property.2).1,
      (primaryIdealGenerator_spec p.2.val p.2.property).1,
      (primaryIdealGenerator_spec q.1.val q.1.property.2).1,
      (primaryIdealGenerator_spec q.2.val q.2.property).1] using hs
  have hd := squarefree_cube_decomposition_unique
    (primaryIdealGenerator_ne_zero_ideal _ p.2.property)
    (primaryIdealGenerator_ne_zero_ideal _ q.2.property)
    p.1.property.1 q.1.property.1 hi
  exact Prod.ext (Subtype.ext hd.1) (Subtype.ext hd.2)

lemma sourceFourier_primary_pair_preimage (x : O) (hx : lambda ^ 2 ∣ x - 1)
    (hT : rationalSourceResidualFourierCoefficient x ≠ 0) :
    ∃ p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
      {J : Ideal O // primaryIdealGenerator J ≠ 0}),
      primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3 = x := by
  have hg : primaryIdealGenerator (Ideal.span {x}) = x :=
    primaryIdealGenerator_span x (primary_ne_zero x hx) hx
  have hg0 : primaryIdealGenerator (Ideal.span {x}) ≠ 0 := by rw [hg]; exact primary_ne_zero x hx
  have ht : rationalSourceResidualFourierCoefficient (primaryIdealGenerator (Ideal.span {x})) ≠ 0 := by rwa [hg]
  obtain ⟨I, J, hI, hIg, hJg, he⟩ := rationalSourceFourier_squarefree_cube_support (Ideal.span {x}) hg0 ht
  refine ⟨(⟨I, hI, hIg⟩, ⟨J, hJg⟩), ?_⟩
  simpa only [primaryIdealGenerator_mul, primaryIdealGenerator_pow, hg] using congrArg primaryIdealGenerator he

/-- Reindex a primary-supported Fourier sum by its unique squarefree and cube factors. -/
theorem sourceFourier_tsum_primary_pairs (w : O → ℂ)
    (hw : ∀ x, w x ≠ 0 → lambda ^ 2 ∣ x - 1) :
    (∑' x : O, w x * star (rationalSourceResidualFourierCoefficient x)) =
      ∑' p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
        {J : Ideal O // primaryIdealGenerator J ≠ 0}),
        w (primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3) *
          star (rationalSourceResidualFourierCoefficient
            (primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3)) := by
  let P := ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
    {J : Ideal O // primaryIdealGenerator J ≠ 0})
  let φ : P → O := fun p => primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3
  let f : O → ℂ := fun x => w x * star (rationalSourceResidualFourierCoefficient x)
  change (∑' x, f x) = ∑' p : P, f (φ p)
  apply tsum_eq_tsum_of_ne_zero_bij (fun p : Function.support (fun p : P => f (φ p)) => φ p.val)
  · exact primary_squarefree_cube_injective.comp Subtype.val_injective
  · intro x hx
    have hwx : w x ≠ 0 := by intro hz; exact hx (by simp only [f, hz, zero_mul])
    have hTx : rationalSourceResidualFourierCoefficient x ≠ 0 := by
      intro hz
      exact hx (by simp only [f, hz, star_zero, mul_zero])
    obtain ⟨p, hp⟩ := sourceFourier_primary_pair_preimage x (hw x hwx) hTx
    have hφ : φ p = x := hp
    exact ⟨⟨p, by change f (φ p) ≠ 0; rwa [hφ]⟩, hφ⟩
  · intro p
    rfl

/-- The different symbol is a cubic root of unity at every primary denominator. -/
lemma traceLambda_symbol_cube (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    (ringComplex (symbol traceLambda x)) ^ 3 = 1 := by
  have hs : traceLambda ^ 2 = (-3 : O) := by
    unfold traceLambda
    linear_combination 4 * cusp_omega_relation
  have hc3 : IsCoprime (3 : O) x := by
    simpa only [Units.val_one, pow_zero, mul_one] using ramified_primary_coprime (1 : Oˣ) 0 x hx
  have hc : IsCoprime traceLambda x := by
    have he : traceLambda * (-traceLambda) = (3 : O) := by linear_combination -hs
    rw [← he] at hc3
    exact hc3.of_mul_left_left
  rw [← map_pow, symbol_cube_of_isCoprime _ _ hx hc, map_one]

lemma traceLambda_symbol_norm (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    ‖ringComplex (symbol traceLambda x)‖ = 1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one, one_pow] using congrArg norm (traceLambda_symbol_cube x hx)

/-- Cubes contribute no different-symbol phase. -/
lemma traceLambda_symbol_mul_cube (a b : O) (hb : lambda ^ 2 ∣ b - 1) :
    ringComplex (symbol traceLambda (a * b ^ 3)) = ringComplex (symbol traceLambda a) := by
  rw [symbol_mul_denominator, symbol_pow_denominator, map_mul, map_pow,
    traceLambda_symbol_cube b hb, mul_one]

/-- The primary mask and different phase converting theta coefficients to cubic Gauss sums. -/
def fixedThetaTwist (Ψ : O →* ℂ) (x : O) : ℂ :=
  if lambda ^ 2 ∣ x - 1 then ringComplex (symbol traceLambda x) * Ψ x else 0

lemma fixedThetaTwist_primary (Ψ : O →* ℂ) (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    fixedThetaTwist Ψ x = ringComplex (symbol traceLambda x) * Ψ x := by
  simp only [fixedThetaTwist, if_pos hx]

lemma fixedThetaTwist_support (Ψ : O →* ℂ) (x : O) (hx : fixedThetaTwist Ψ x ≠ 0) :
    lambda ^ 2 ∣ x - 1 := by
  by_contra hn
  exact hx (by simp only [fixedThetaTwist, if_neg hn])

lemma fixedThetaTwist_norm (Ψ : O →* ℂ) (x : O) :
    ‖fixedThetaTwist Ψ x‖ = if lambda ^ 2 ∣ x - 1 then ‖Ψ x‖ else 0 := by
  by_cases hx : lambda ^ 2 ∣ x - 1
  · rw [fixedThetaTwist_primary Ψ x hx, norm_mul, traceLambda_symbol_norm x hx, one_mul, if_pos hx]
  · simp only [fixedThetaTwist, if_neg hx, norm_zero]

/-- Twisting cancels the different phase, leaving the normalized cubic Gauss coefficient. -/
theorem fixedThetaTwist_source_coefficient (Ψ : O →* ℂ) (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I) :
    rationalSourceThetaScalar⁻¹ *
      star (rationalSourceResidualFourierCoefficient (primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)) *
        fixedThetaTwist Ψ (primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3) =
      (‖ringComplex (primaryIdealGenerator J)‖ : ℂ) * normalizedCubicUnitGauss (primaryIdealGenerator I) *
        Ψ (primaryIdealGenerator I) * (Ψ (primaryIdealGenerator J)) ^ 3 := by
  have hIp := (primaryIdealGenerator_spec I hI).2
  have hJp := (primaryIdealGenerator_spec J hJ).2
  have hp := primary_mul _ _ hIp (primary_pow_congruence _ hJp 3)
  rw [normalized_sourceFourier_squarefree_cube I J hI hJ hsq,
    fixedThetaTwist_primary Ψ _ hp, traceLambda_symbol_mul_cube _ _ hJp, map_mul, map_pow]
  have hu : star (ringComplex (symbol traceLambda (primaryIdealGenerator I))) *
      ringComplex (symbol traceLambda (primaryIdealGenerator I)) = 1 := by
    simpa only [Complex.star_def, traceLambda_symbol_norm _ hIp, one_pow, Complex.ofReal_one] using
      Complex.conj_mul' (ringComplex (symbol traceLambda (primaryIdealGenerator I)))
  calc
    _ = (star (ringComplex (symbol traceLambda (primaryIdealGenerator I))) *
        ringComplex (symbol traceLambda (primaryIdealGenerator I))) *
        ((‖ringComplex (primaryIdealGenerator J)‖ : ℂ) * normalizedCubicUnitGauss (primaryIdealGenerator I) *
          Ψ (primaryIdealGenerator I) * (Ψ (primaryIdealGenerator J)) ^ 3) := by ring
    _ = _ := by rw [hu, one_mul]

/-- The twisted primary Fourier sum is exactly the squarefree-times-cube Gauss series. -/
theorem fixedThetaTwist_source_tsum (Ψ : O →* ℂ) (W : O → ℂ) :
    (∑' x : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient x) *
      fixedThetaTwist Ψ x) * W x) =
      ∑' p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
        {J : Ideal O // primaryIdealGenerator J ≠ 0}),
        ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
          normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
          Ψ (primaryIdealGenerator p.1.val) * (Ψ (primaryIdealGenerator p.2.val)) ^ 3) *
          W (primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3) := by
  let w : O → ℂ := fun x => rationalSourceThetaScalar⁻¹ * fixedThetaTwist Ψ x * W x
  have hw (x : O) (hx : w x ≠ 0) : lambda ^ 2 ∣ x - 1 := by
    apply fixedThetaTwist_support Ψ x
    intro hz
    exact hx (by simp only [w, hz, mul_zero, zero_mul])
  calc
    _ = ∑' x : O, w x * star (rationalSourceResidualFourierCoefficient x) := by
      apply tsum_congr
      intro x
      dsimp only [w]
      ring
    _ = _ := by
      rw [sourceFourier_tsum_primary_pairs w hw]
      apply tsum_congr
      intro p
      have he := fixedThetaTwist_source_coefficient Ψ p.1.val p.2.val
        p.1.property.2 p.2.property p.1.property.1
      dsimp only [w]
      linear_combination W (primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3) * he

/-- A character modulo `c` acquires precisely the additional modulus nine from the different. -/
lemma fixedThetaTwist_quotient_period (c : O) (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (x y : O) (hxy : (9 * c : O) ∣ x - y) :
    fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) x =
      fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) y := by
  have h9 : (9 : O) ∣ x - y := (dvd_mul_right 9 c).trans hxy
  have hc : c ∣ x - y := (dvd_mul_left c 9).trans hxy
  have hd : lambda ^ 2 ∣ x - y := lambda_sq_dvd_three.trans ((show (3 : O) ∣ 9 from ⟨3, by norm_num⟩).trans h9)
  have hp : lambda ^ 2 ∣ x - 1 ↔ lambda ^ 2 ∣ y - 1 := by
    constructor
    · intro hx
      convert dvd_sub hx hd using 1
      ring
    · intro hy
      convert dvd_add hd hy using 1
      ring
  have he : Ideal.Quotient.mk (Ideal.span {c}) x = Ideal.Quotient.mk (Ideal.span {c}) y :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hc)
  by_cases hx : lambda ^ 2 ∣ x - 1
  · rw [fixedThetaTwist_primary _ x hx, fixedThetaTwist_primary _ y (hp.mp hx),
      symbol_traceLambda_congr_mod_nine x y hx (hp.mp hx) h9]
    change ringComplex (symbol traceLambda y) * Ψ (Ideal.Quotient.mk _ x) =
      ringComplex (symbol traceLambda y) * Ψ (Ideal.Quotient.mk _ y)
    rw [he]
  · simp only [fixedThetaTwist, if_neg hx, if_neg (fun hy => hx (hp.mpr hy))]

/-- The finite residue-class multiplier used to twist the actual residual source. -/
def finiteThetaTwist (c : O) (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (x : O ⧸ Ideal.span {9 * c}) : ℂ :=
  fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) (Quotient.out x)

lemma finiteThetaTwist_mk (c : O) (Ψ : (O ⧸ Ideal.span {c}) →* ℂ) (x : O) :
    finiteThetaTwist c Ψ (Ideal.Quotient.mk (Ideal.span {9 * c}) x) =
      fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) x := by
  apply fixedThetaTwist_quotient_period
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {9 * c}) x)))

/-- Finite additive Fourier coefficients normalized for direct reconstruction. -/
def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R → ℂ) (h : R) : ℂ :=
  (∑ x, φ x * ψ (-h * x)) / (Fintype.card R : ℂ)

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R → ℂ) (x : R) :
    (∑ h, finiteAdditiveFourierCoeff ψ φ h * ψ (h * x)) = φ x := by
  have hN : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑ h, ∑ y, φ y * ψ (-h * y) * ψ (h * x)) / (Fintype.card R : ℂ) := by
      simp only [finiteAdditiveFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    _ = (∑ y, φ y * ∑ h, ψ (h * (x - y))) / (Fintype.card R : ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑ y, φ y * (if x - y = 0 then (Fintype.card R : ℂ) else 0)) / (Fintype.card R : ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ, apply_ite, Nat.cast_zero]
    _ = φ x := by
      have he : (∑ y, φ y * (if x - y = 0 then (Fintype.card R : ℂ) else 0)) =
          φ x * (Fintype.card R : ℂ) := by simp [sub_eq_zero]
      rw [he, mul_div_cancel_right₀ _ hN]

/-- Every Fourier coefficient is bounded by the mean absolute value of the multiplier. -/
lemma finiteAdditiveFourierCoeff_norm_le {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R → ℂ) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖ ≤ (∑ x, ‖φ x‖) / (Fintype.card R : ℝ) := by
  rw [finiteAdditiveFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ x, ‖φ x * ψ (-h * x)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]

/-- Conjugation reverses the geometric trace character. -/
lemma star_tracePhase (z : ℂ) : star (tracePhase z) = tracePhase (-z) := by
  change star (Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))) =
    Complex.exp (2 * Real.pi * Complex.I * (-z + starRingEnd ℂ (-z)))
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_add, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_conj]
  ring

lemma conjugate_cuspCharacterSeries (a : O → ℂ) (z : ℂ) :
    star (cuspCharacterSeries a z) =
      ∑' h : O, star (a h) * tracePhase (-cuspFrequency h * z) := by
  rw [cuspCharacterSeries, tsum_star]
  apply tsum_congr
  intro h
  rw [star_mul, star_tracePhase, neg_mul]
  ring

lemma conjugate_cuspCharacterSeries_summable (a : O → ℂ)
    (ha : Summable (fun h => ‖a h‖)) (z : ℂ) :
    Summable (fun h => star (a h) * tracePhase (-cuspFrequency h * z)) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_star, tracePhase_norm, mul_one] using ha

/-- A finite translation acts diagonally on the absolutely convergent source Fourier series. -/
theorem conjugate_cuspCharacterSeries_finite_translation {ι : Type*} [Fintype ι]
    (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (shift weight : ι → ℂ) (z : ℂ) :
    (∑ i, weight i * star (cuspCharacterSeries a (z + shift i))) =
      ∑' h : O, (∑ i, weight i * tracePhase (-cuspFrequency h * shift i)) *
        star (a h) * tracePhase (-cuspFrequency h * z) := by
  simp only [conjugate_cuspCharacterSeries, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun i _ =>
    (conjugate_cuspCharacterSeries_summable a ha (z + shift i)).mul_left (weight i))]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, mul_add, AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- These rational translations realize the primitive residue trace character. -/
def thetaFourierTranslation (c : O) (h : O ⧸ Ideal.span {c}) : ℂ :=
  -3 * ringComplex (Quotient.out h) / ringComplex c

lemma thetaFourierTranslation_phase (c : O) (hc : c ≠ 0)
    (h : O ⧸ Ideal.span {c}) (x : O) :
    tracePhase (-cuspFrequency x * thetaFourierTranslation c h) =
      residueTraceQuotientChar 1 c hc (h * Ideal.Quotient.mk _ x) := by
  have hm : h * Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ (Quotient.out h * x) := by
    rw [map_mul, Ideal.Quotient.mk_out]
  rw [hm, residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency thetaFourierTranslation
  simp only [map_mul, map_ofNat, mul_one]
  congr 1
  field_simp

lemma thetaFourierTranslation_inversion (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ) (x : O) :
    (∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
      tracePhase (-cuspFrequency x * thetaFourierTranslation c h)) = φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion _ (residueTraceQuotientChar_primitive c hc) φ _

/-- The actual conjugate residual source twisted by a finite residue-class multiplier. -/
def traceTwistedConjugateSource (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {c})]
    (φ : (O ⧸ Ideal.span {c}) → ℂ) (v : ℝ) (hv : 0 < v) (z : ℂ) : ℂ :=
  ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
    star (cubicSourceResidualFunction (upperPoint (z + thetaFourierTranslation c h) v hv))

/-- Finite Fourier inversion inserts exactly the requested multiplier into every source mode. -/
theorem traceTwistedConjugateSource_fourier (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    traceTwistedConjugateSource c hc φ v hv z =
      ∑' h : O, φ (Ideal.Quotient.mk _ h) * star (rationalSourceModeAmplitude v h) *
        tracePhase (-cuspFrequency h * z) := by
  simp only [traceTwistedConjugateSource, cubicSourceResidualFunction_fourier_expansion]
  rw [conjugate_cuspCharacterSeries_finite_translation _ (rationalSourceModeAmplitude_summable v hv)]
  simp only [thetaFourierTranslation_inversion c hc]

/-- The cubic Bessel kernel is real on the positive axis. -/
lemma star_schlafliBesselK_cubic (x : ℝ) (hx : 0 < x) :
    star (schlafliBesselK (1 / 3) x) = schlafliBesselK (1 / 3) x := by
  have hp := (Complex.ofReal_cpow (show 0 ≤ x / 2 by positivity) (-(1 : ℝ) / 3)).symm
  push_cast at hp
  simp only [neg_div] at hp
  rw [schlafliBesselK, hp, cubicSchlafliIntegral_ofReal]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

lemma traceTwistedConjugateSource_bessel (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ) (hφ : φ 0 = 0)
    (v : ℝ) (hv : 0 < v) :
    traceTwistedConjugateSource c hc φ v hv 0 =
      ∑' h : O, φ (Ideal.Quotient.mk _ h) * star (rationalSourceResidualFourierCoefficient h) *
        (v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  rw [traceTwistedConjugateSource_fourier]
  apply tsum_congr
  intro h
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
  by_cases hh : h = 0
  · subst h
    simp only [map_zero, hφ, zero_mul]
  · rw [rationalSourceModeAmplitude_bessel v hv h hh, star_mul, star_mul,
      star_schlafliBesselK_cubic _ (by
        have hf := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
        positivity)]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring

lemma fixedThetaTwist_zero (Ψ : O →* ℂ) : fixedThetaTwist Ψ 0 = 0 := by
  by_contra hz
  exact primary_ne_zero 0 (fixedThetaTwist_support Ψ 0 hz) rfl

/-- An exact Gauss-series realization by a finite sum of translates of the actual residual source. -/
theorem finiteThetaTwist_source_bessel (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (v : ℝ) (hv : 0 < v) :
    rationalSourceThetaScalar⁻¹ *
      traceTwistedConjugateSource (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ) v hv 0 =
      ∑' p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
        {J : Ideal O // primaryIdealGenerator J ≠ 0}),
        ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
          normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
          Ψ (Ideal.Quotient.mk _ (primaryIdealGenerator p.1.val)) *
          (Ψ (Ideal.Quotient.mk _ (primaryIdealGenerator p.2.val))) ^ 3) *
          ((v : ℂ) * schlafliBesselK (1 / 3)
            (4 * Real.pi * ‖cuspFrequency (primaryIdealGenerator p.1.val *
              (primaryIdealGenerator p.2.val) ^ 3)‖ * v)) := by
  have hz : finiteThetaTwist c Ψ 0 = 0 := by
    rw [← map_zero (Ideal.Quotient.mk (Ideal.span {9 * c})), finiteThetaTwist_mk, fixedThetaTwist_zero]
  rw [traceTwistedConjugateSource_bessel _ _ _ hz v hv, ← tsum_mul_left]
  calc
    _ = ∑' h : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient h) *
        fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) h) *
        ((v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)) := by
      apply tsum_congr
      intro h
      rw [finiteThetaTwist_mk]
      ring
    _ = _ := fixedThetaTwist_source_tsum _ _

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I) * (freq * direction + star (freq * direction))

lemma tracePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => tracePhase (freq * (z + (x : ℂ) * direction)))
      (horizontalPhaseMultiplier freq direction * tracePhase (freq * (z + (t : ℂ) * direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq * (z + (x : ℂ) * direction)) (freq * direction) t := by
    convert! (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const direction).const_add z).const_mul freq using 1 <;> norm_num
  have he := ((hz.add hz.star).const_mul (2 * Real.pi * Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I) *
      (freq * (z + (x : ℂ) * direction) + star (freq * (z + (x : ℂ) * direction)))))
    ((2 * Real.pi * Complex.I) * (freq * direction + star (freq * direction)) *
      Complex.exp ((2 * Real.pi * Complex.I) *
        (freq * (z + (t : ℂ) * direction) + star (freq * (z + (t : ℂ) * direction))))) t
  simpa only [Pi.add_apply, mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖ ≤ 4 * Real.pi * ‖freq‖ * ‖direction‖ := by
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    norm_num [norm_mul, abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul, hc]
  calc
    _ ≤ (2 * Real.pi) * (‖freq * direction‖ + ‖star (freq * direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star, norm_mul]; ring

lemma horizontalPhaseMultiplier_wirtinger (freq : ℂ) :
    (1 / 2 : ℂ) * (horizontalPhaseMultiplier freq 1 +
      Complex.I * horizontalPhaseMultiplier freq Complex.I) = 2 * Real.pi * Complex.I * star freq := by
  simp only [horizontalPhaseMultiplier, mul_one, star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three]
  ring

/-- The antiholomorphic derivative expressed through the two real horizontal directions. -/
def horizontalWirtingerBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (deriv (fun t : ℝ => f (z + (t : ℂ))) 0 +
    Complex.I * deriv (fun t : ℝ => f (z + (t : ℂ) * Complex.I)) 0)

/-- One summable frequency moment permits termwise horizontal differentiation. -/
theorem traceFourierSeries_hasDerivAt {ι : Type*} (freq a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖))
    (hfa : Summable (fun i => ‖freq i‖ * ‖a i‖)) (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∑' i, a i * tracePhase (freq i * (z + (x : ℂ) * direction)))
      (∑' i, horizontalPhaseMultiplier (freq i) direction *
        (a i * tracePhase (freq i * (z + (t : ℂ) * direction)))) t := by
  have hd (i : ι) (x : ℝ) :
      HasDerivAt (fun y : ℝ => a i * tracePhase (freq i * (z + (y : ℂ) * direction)))
        (horizontalPhaseMultiplier (freq i) direction *
          (a i * tracePhase (freq i * (z + (x : ℂ) * direction)))) x := by
    convert! (tracePhase_hasDerivAt (freq i) z direction x).const_mul (a i) using 1
    ring
  have hb (i : ι) (x : ℝ) :
      ‖horizontalPhaseMultiplier (freq i) direction *
        (a i * tracePhase (freq i * (z + (x : ℂ) * direction)))‖ ≤
      (4 * Real.pi * ‖direction‖) * (‖freq i‖ * ‖a i‖) := by
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    calc
      _ ≤ (4 * Real.pi * ‖freq i‖ * ‖direction‖) * ‖a i‖ :=
        mul_le_mul_of_nonneg_right (horizontalPhaseMultiplier_norm _ _) (norm_nonneg _)
      _ = _ := by ring
  have hz : Summable (fun i => a i * tracePhase (freq i * (z + (0 : ℂ) * direction))) := by
    apply Summable.of_norm
    simpa only [norm_mul, tracePhase_norm, mul_one] using ha
  exact hasDerivAt_tsum
    (𝕜 := ℝ)
    (g := fun i (x : ℝ) => a i * tracePhase (freq i * (z + (x : ℂ) * direction)))
    (g' := fun i (x : ℝ) => horizontalPhaseMultiplier (freq i) direction *
      (a i * tracePhase (freq i * (z + (x : ℂ) * direction))))
    (y₀ := 0) (hfa.mul_left (4 * Real.pi * ‖direction‖)) hd hb hz t

lemma traceFourierSeries_directional_summable {ι : Type*} (freq a : ι → ℂ)
    (hfa : Summable (fun i => ‖freq i‖ * ‖a i‖)) (z direction : ℂ) :
    Summable (fun i => horizontalPhaseMultiplier (freq i) direction *
      (a i * tracePhase (freq i * z))) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => ?_) (hfa.mul_left (4 * Real.pi * ‖direction‖))
  rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
  calc
    _ ≤ (4 * Real.pi * ‖freq i‖ * ‖direction‖) * ‖a i‖ :=
      mul_le_mul_of_nonneg_right (horizontalPhaseMultiplier_norm _ _) (norm_nonneg _)
    _ = _ := by ring

theorem traceFourierSeries_wirtingerBar {ι : Type*} (freq a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) (hfa : Summable (fun i => ‖freq i‖ * ‖a i‖)) (z : ℂ) :
    horizontalWirtingerBar (fun w => ∑' i, a i * tracePhase (freq i * w)) z =
      ∑' i, (2 * Real.pi * Complex.I * star (freq i)) * (a i * tracePhase (freq i * z)) := by
  have h1 := (traceFourierSeries_hasDerivAt freq a ha hfa z 1 0).deriv
  have hI := (traceFourierSeries_hasDerivAt freq a ha hfa z Complex.I 0).deriv
  simp only [mul_one, Complex.ofReal_zero, zero_mul, add_zero] at h1 hI
  rw [horizontalWirtingerBar, h1, hI]
  have hs1 := traceFourierSeries_directional_summable freq a hfa z 1
  have hsI := (traceFourierSeries_directional_summable freq a hfa z Complex.I).mul_left Complex.I
  rw [← tsum_mul_left, ← hs1.tsum_add hsI, ← tsum_mul_left]
  apply tsum_congr
  intro i
  linear_combination (a i * tracePhase (freq i * z)) * horizontalPhaseMultiplier_wirtinger (freq i)

lemma frequency_exp_absorption (a r : ℝ) (ha : 0 < a) :
    r * Real.exp (-a * r) ≤ (2 / a) * Real.exp (-(a / 2) * r) := by
  have he := Real.add_one_le_exp ((a / 2) * r)
  have hr : r ≤ (2 / a) * Real.exp ((a / 2) * r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith only [he]
  calc
    _ ≤ ((2 / a) * Real.exp ((a / 2) * r)) * Real.exp (-a * r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma cuspFrequency_firstMoment_exp_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun h : O => ‖cuspFrequency h‖ * Real.exp (-a * ‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => frequency_exp_absorption a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a / 2) (half_pos ha)).mul_left (2 / a)

/-- The actual source amplitudes have a summable first frequency moment at every positive height. -/
lemma rationalSourceModeAmplitude_frequency_summable (v : ℝ) (hv : 0 < v) :
    Summable (fun h : O => ‖cuspFrequency h‖ * ‖rationalSourceModeAmplitude v h‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselCoefficient_strip_bound rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential v v hv le_rfl
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun h => ?_)
    ((cuspFrequency_firstMoment_exp_summable (Real.pi * v) (mul_pos Real.pi_pos hv)).mul_left C)
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, norm_zero, zero_mul, mul_zero, le_refl]
  · rw [rationalSourceModeAmplitude_bessel v hv h hh]
    calc
      _ ≤ ‖cuspFrequency h‖ * (C * Real.exp (-(Real.pi * v) * ‖cuspFrequency h‖)) :=
        mul_le_mul_of_nonneg_left (hb h hh v ⟨le_rfl, le_rfl⟩) (norm_nonneg _)
      _ = _ := by ring

lemma residueMultiplier_source_summable (c : O) [Fintype (O ⧸ Ideal.span {c})]
    (φ : (O ⧸ Ideal.span {c}) → ℂ) (v : ℝ) (hv : 0 < v) :
    Summable (fun h : O => ‖φ (Ideal.Quotient.mk _ h) * star (rationalSourceModeAmplitude v h)‖) ∧
      Summable (fun h : O => ‖-cuspFrequency h‖ *
        ‖φ (Ideal.Quotient.mk _ h) * star (rationalSourceModeAmplitude v h)‖) := by
  let C : ℝ := ∑ x, ‖φ x‖
  have hb (h : O) : ‖φ (Ideal.Quotient.mk _ h)‖ ≤ C :=
    Finset.single_le_sum (fun x _ => norm_nonneg (φ x)) (Finset.mem_univ _)
  constructor
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun h => ?_) ((rationalSourceModeAmplitude_summable v hv).mul_left C)
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (hb h) (norm_nonneg _)
  · apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun h => ?_) ((rationalSourceModeAmplitude_frequency_summable v hv).mul_left C)
    rw [norm_neg, norm_mul, norm_star]
    calc
      _ ≤ ‖cuspFrequency h‖ * (C * ‖rationalSourceModeAmplitude v h‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb h) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring

/-- The horizontal derivative of the actual finite twist is its frequency-weighted Fourier series. -/
theorem traceTwistedConjugateSource_wirtingerBar (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (v : ℝ) (hv : 0 < v) (z : ℂ) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) z =
      ∑' h : O, (-2 * Real.pi * Complex.I * star (cuspFrequency h)) *
        (φ (Ideal.Quotient.mk _ h) * star (rationalSourceModeAmplitude v h) *
          tracePhase (-cuspFrequency h * z)) := by
  have he : traceTwistedConjugateSource c hc φ v hv =
      (fun z : ℂ => ∑' h : O, (φ (Ideal.Quotient.mk _ h) * star (rationalSourceModeAmplitude v h)) *
        tracePhase ((-cuspFrequency h) * z)) :=
    funext (traceTwistedConjugateSource_fourier c hc φ v hv)
  obtain ⟨ha, hfa⟩ := residueMultiplier_source_summable c φ v hv
  rw [he, traceFourierSeries_wirtingerBar _ _ ha hfa z]
  apply tsum_congr
  intro h
  simp only [star_neg]
  ring

lemma traceTwistedConjugateSource_wirtingerBar_zero (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0 =
      ∑' h : O, (-2 * Real.pi * Complex.I * star (cuspFrequency h)) *
        φ (Ideal.Quotient.mk _ h) * star (rationalSourceResidualFourierCoefficient h) *
        (v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  rw [traceTwistedConjugateSource_wirtingerBar]
  apply tsum_congr
  intro h
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, star_zero, mul_zero, zero_mul]
  · rw [rationalSourceModeAmplitude_bessel v hv h hh, star_mul, star_mul,
      star_schlafliBesselK_cubic _ (by
        have hf := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
        positivity)]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring

/-- The frequency-weighted cubic Gauss series is an actual horizontal source derivative. -/
theorem finiteThetaTwist_source_wirtingerBar (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (v : ℝ) (hv : 0 < v) :
    rationalSourceThetaScalar⁻¹ * horizontalWirtingerBar
      (traceTwistedConjugateSource (9 * c) (mul_ne_zero (by norm_num) hc) (finiteThetaTwist c Ψ) v hv) 0 =
      ∑' p : ({I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} ×
        {J : Ideal O // primaryIdealGenerator J ≠ 0}),
        ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
          normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
          Ψ (Ideal.Quotient.mk _ (primaryIdealGenerator p.1.val)) *
          (Ψ (Ideal.Quotient.mk _ (primaryIdealGenerator p.2.val))) ^ 3) *
          ((-2 * Real.pi * Complex.I * star (cuspFrequency (primaryIdealGenerator p.1.val *
              (primaryIdealGenerator p.2.val) ^ 3))) * (v : ℂ) * schlafliBesselK (1 / 3)
            (4 * Real.pi * ‖cuspFrequency (primaryIdealGenerator p.1.val *
              (primaryIdealGenerator p.2.val) ^ 3)‖ * v)) := by
  rw [traceTwistedConjugateSource_wirtingerBar_zero, ← tsum_mul_left]
  calc
    _ = ∑' h : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient h) *
        fixedThetaTwist (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) h) *
        ((-2 * Real.pi * Complex.I * star (cuspFrequency h)) * (v : ℂ) *
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)) := by
      apply tsum_congr
      intro h
      rw [finiteThetaTwist_mk]
      ring
    _ = _ := fixedThetaTwist_source_tsum _ _

/-- A common Gamma-density majorant for the cubic Schläfli kernel and its derivative. -/
def cubicSchlafliMajorant (t : ℝ) : ℝ := t ^ (-(2 : ℝ) / 3) * Real.exp (-t / 2)

lemma cubicSchlafliMajorant_integrable : IntegrableOn cubicSchlafliMajorant (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := -(2 : ℝ) / 3) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  convert! hh using 1
  congr 1
  funext t
  simp only [cubicSchlafliMajorant, Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicSchlafliMajorant_integral_nonneg : 0 ≤ ∫ t in Ioi 0, cubicSchlafliMajorant t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

def cubicSchlafliDensityDeriv (x t : ℝ) : ℝ := -(x / (2 * t)) * cubicSchlafliDensity x t

lemma cubicSchlafliDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicSchlafliDensity y t) (cubicSchlafliDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4 * t)).const_sub (-t)).exp.const_mul (t ^ (-(2 : ℝ) / 3))
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one] at he
  convert! he using 1
  unfold cubicSchlafliDensityDeriv cubicSchlafliDensity
  ring

lemma cubicSchlafliDensityDeriv_bound (δ x t : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) (ht : 0 < t) :
    ‖cubicSchlafliDensityDeriv x t‖ ≤ (4 / δ) * Real.exp (-x / 2) * cubicSchlafliMajorant t := by
  have hxp := hδ.trans_le hx
  have hdamp : (x / (2 * t)) * Real.exp (-(x ^ 2 / (8 * t))) ≤ 4 / x := by
    have hy : (x ^ 2 / (8 * t)) * Real.exp (-(x ^ 2 / (8 * t))) ≤ 1 := by
      have hb : x ^ 2 / (8 * t) ≤ Real.exp (x ^ 2 / (8 * t)) := by
        linarith only [Real.add_one_le_exp (x ^ 2 / (8 * t))]
      calc
        _ ≤ Real.exp (x ^ 2 / (8 * t)) * Real.exp (-(x ^ 2 / (8 * t))) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hr : x / (2 * t) = (4 / x) * (x ^ 2 / (8 * t)) := by field_simp; ring
    rw [hr, mul_assoc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ 4 / x)
  have hyoung : x / 2 - t / 2 ≤ x ^ 2 / (8 * t) :=
    (le_div_iff₀ (by positivity : 0 < 8 * t)).mpr (by nlinarith only [sq_nonneg (x - 2 * t)])
  have he : Real.exp (-t - x ^ 2 / (4 * t)) ≤
      Real.exp (-x / 2) * Real.exp (-t / 2) * Real.exp (-(x ^ 2 / (8 * t))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show x ^ 2 / (4 * t) = 2 * (x ^ 2 / (8 * t)) by ring]
    linarith only [hyoung]
  have hn : ‖cubicSchlafliDensityDeriv x t‖ =
      (x / (2 * t)) * t ^ (-(2 : ℝ) / 3) * Real.exp (-t - x ^ 2 / (4 * t)) := by
    unfold cubicSchlafliDensityDeriv cubicSchlafliDensity
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    ring
  rw [hn]
  calc
    _ ≤ (x / (2 * t)) * t ^ (-(2 : ℝ) / 3) *
        (Real.exp (-x / 2) * Real.exp (-t / 2) * Real.exp (-(x ^ 2 / (8 * t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x / (2 * t)) * Real.exp (-(x ^ 2 / (8 * t)))) *
        Real.exp (-x / 2) * cubicSchlafliMajorant t := by unfold cubicSchlafliMajorant; ring
    _ ≤ (4 / x) * Real.exp (-x / 2) * cubicSchlafliMajorant t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdamp (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hδ hx) (Real.exp_pos _).le

lemma cubicSchlafliDensityDeriv_integrable (x : ℝ) (hx : 0 < x) :
    IntegrableOn (cubicSchlafliDensityDeriv x) (Ioi 0) := by
  apply (cubicSchlafliMajorant_integrable.const_mul ((4 / x) * Real.exp (-x / 2))).mono'
  · unfold cubicSchlafliDensityDeriv cubicSchlafliDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicSchlafliDensityDeriv_bound x x t hx le_rfl ht

/-- Local domination differentiates the Schläfli integral on the positive axis. -/
lemma cubicSchlafliIntegral_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ t in Ioi 0, cubicSchlafliDensity y t)
      (∫ t in Ioi 0, cubicSchlafliDensityDeriv x t) x := by
  have hδ : 0 < x / 2 := half_pos hx
  have hU : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith only [hx])
  have hb : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ y ∈ Ioi (x / 2),
      ‖cubicSchlafliDensityDeriv y t‖ ≤ (4 / (x / 2)) * cubicSchlafliMajorant t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    have hyp := hδ.trans hy
    calc
      _ ≤ (4 / (x / 2)) * Real.exp (-y / 2) * cubicSchlafliMajorant t :=
        cubicSchlafliDensityDeriv_bound _ y t hδ hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hyp])
        have hg : 0 ≤ cubicSchlafliMajorant t :=
          mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 / (x / 2))) hg
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := cubicSchlafliDensity) (F' := cubicSchlafliDensityDeriv)
    (bound := fun t => (4 / (x / 2)) * cubicSchlafliMajorant t) hU
    (Eventually.of_forall (fun y => by unfold cubicSchlafliDensity; fun_prop))
    (cubicSchlafliDensity_integrable x)
    (by unfold cubicSchlafliDensityDeriv cubicSchlafliDensity; fun_prop)
    hb (cubicSchlafliMajorant_integrable.const_mul (4 / (x / 2)))
    (Eventually.of_forall (fun t y _ => cubicSchlafliDensity_hasDerivAt y t))).2

lemma schlafliBesselK_one_third_ofReal (x : ℝ) (hx : 0 < x) :
    schlafliBesselK (1 / 3) x =
      (((1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) * ∫ t in Ioi 0, cubicSchlafliDensity x t : ℝ) : ℂ) := by
  have hp := (Complex.ofReal_cpow (show 0 ≤ x / 2 by positivity) (-(1 : ℝ) / 3)).symm
  push_cast at hp
  simp only [neg_div] at hp
  rw [schlafliBesselK, hp, cubicSchlafliIntegral_ofReal]
  push_cast
  simp only [neg_div]

/-- The explicit derivative of the real cubic Bessel kernel. -/
def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1 : ℝ) / 12) * (x / 2) ^ (-(4 : ℝ) / 3) * (∫ t in Ioi 0, cubicSchlafliDensity x t) +
    (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) * (∫ t in Ioi 0, cubicSchlafliDensityDeriv x t)

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1 / 3) y) (cubicBesselRealDeriv x : ℂ) x := by
  have hp : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (y / 2) ^ (-(1 : ℝ) / 3))
      ((-(1 : ℝ) / 12) * (x / 2) ^ (-(4 : ℝ) / 3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p := -(1 : ℝ) / 3) (Or.inl (by positivity : x / 2 ≠ 0))).const_mul (1 / 2 : ℝ)
    convert! hh using 1 <;> norm_num
    ring
  have hr := hp.mul (cubicSchlafliIntegral_hasDerivAt x hx)
  have he : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (y / 2) ^ (-(1 : ℝ) / 3) *
      ∫ t in Ioi 0, cubicSchlafliDensity y t) (cubicBesselRealDeriv x) x := hr
  apply he.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_one_third_ofReal y hy

lemma cubicSchlafliDensity_majorant (x t : ℝ) (ht : 0 < t) :
    cubicSchlafliDensity x t ≤ Real.exp (-x / 2) * cubicSchlafliMajorant t := by
  have hf : x / 2 - t / 2 ≤ x ^ 2 / (4 * t) :=
    (le_div_iff₀ (by positivity : 0 < 4 * t)).mpr
      (by nlinarith only [sq_nonneg (x - t), sq_nonneg t])
  calc
    _ ≤ t ^ (-(2 : ℝ) / 3) * Real.exp (-x / 2 + -t / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hf]))
        (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [Real.exp_add]; unfold cubicSchlafliMajorant; ring

lemma cubicSchlafliIntegral_norm_upper (x : ℝ) :
    ‖∫ t in Ioi 0, cubicSchlafliDensity x t‖ ≤
      Real.exp (-x / 2) * ∫ t in Ioi 0, cubicSchlafliMajorant t := by
  have hp : 0 ≤ ∫ t in Ioi 0, cubicSchlafliDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hp, ← integral_const_mul]
  exact setIntegral_mono_on (cubicSchlafliDensity_integrable x)
    (cubicSchlafliMajorant_integrable.const_mul (Real.exp (-x / 2))) measurableSet_Ioi
    (fun t ht => cubicSchlafliDensity_majorant x t ht)

lemma cubicSchlafliIntegralDeriv_norm_upper (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖∫ t in Ioi 0, cubicSchlafliDensityDeriv x t‖ ≤
      ((4 / δ) * Real.exp (-x / 2)) * ∫ t in Ioi 0, cubicSchlafliMajorant t := by
  have hi := cubicSchlafliDensityDeriv_integrable x (hδ.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicSchlafliMajorant_integrable.const_mul ((4 / δ) * Real.exp (-x / 2))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicSchlafliDensityDeriv_bound δ x t hδ hx ht)
  rw [integral_const_mul] at hb
  exact (norm_integral_le_integral_norm _).trans hb

/-- The cubic Bessel derivative has uniform exponential decay away from zero. -/
theorem cubicBesselRealDeriv_exp_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x → ‖(cubicBesselRealDeriv x : ℂ)‖ ≤ C * Real.exp (-x / 2) := by
  let A : ℝ := ∫ t in Ioi 0, cubicSchlafliMajorant t
  have hA : 0 ≤ A := cubicSchlafliMajorant_integral_nonneg
  refine ⟨((1 / 12 : ℝ) * (δ / 2) ^ (-(4 : ℝ) / 3) +
    (1 / 2 : ℝ) * (δ / 2) ^ (-(1 : ℝ) / 3) * (4 / δ)) * A, by positivity, ?_⟩
  intro x hx
  have hxp := hδ.trans_le hx
  have hp1 : (x / 2) ^ (-(1 : ℝ) / 3) ≤ (δ / 2) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hx]) (by norm_num)
  have hp4 : (x / 2) ^ (-(4 : ℝ) / 3) ≤ (δ / 2) ^ (-(4 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hx]) (by norm_num)
  rw [Complex.norm_real, cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1 : ℝ) / 12) * (x / 2) ^ (-(4 : ℝ) / 3) * (∫ t in Ioi 0, cubicSchlafliDensity x t)‖ +
        ‖(1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) * (∫ t in Ioi 0, cubicSchlafliDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1 / 12 : ℝ) * (x / 2) ^ (-(4 : ℝ) / 3) * ‖∫ t in Ioi 0, cubicSchlafliDensity x t‖ +
        (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) * ‖∫ t in Ioi 0, cubicSchlafliDensityDeriv x t‖ := by
      simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x / 2) _)]
      norm_num
    _ ≤ (1 / 12 : ℝ) * (δ / 2) ^ (-(4 : ℝ) / 3) * (Real.exp (-x / 2) * A) +
        (1 / 2 : ℝ) * (δ / 2) ^ (-(1 : ℝ) / 3) * (((4 / δ) * Real.exp (-x / 2)) * A) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hp4 (by norm_num))
          (cubicSchlafliIntegral_norm_upper x) (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hp1 (by norm_num))
          (cubicSchlafliIntegralDeriv_norm_upper δ x hδ hx) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The real differential of the exponent of a horizontal trace character. -/
def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction =
      (2 * Real.pi * Complex.I) * (freq * direction + star (freq * direction)) := by
  simp only [horizontalPhaseCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

lemma tracePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => tracePhase (freq * w))
      (tracePhase (freq * z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x := z)
  convert! hh using 1

/-- The nonconstant Bessel amplitude associated with a Fourier coefficient sequence. -/
def cubicBesselAmplitude (c : O → ℂ) (v : ℝ) (h : O) : ℂ :=
  if h = 0 then 0 else c h * (v : ℂ) *
    schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)

def cubicBesselAmplitudeDeriv (c : O → ℂ) (v : ℝ) (h : O) : ℂ :=
  if h = 0 then 0 else c h *
    (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) +
      (v : ℂ) * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) *
        (cubicBesselRealDeriv (4 * Real.pi * ‖cuspFrequency h‖ * v) : ℂ))

lemma cubicBesselAmplitude_hasDerivAt (c : O → ℂ) (v : ℝ) (hv : 0 < v) (h : O) :
    HasDerivAt (fun y : ℝ => cubicBesselAmplitude c y h) (cubicBesselAmplitudeDeriv c v h) v := by
  by_cases hh : h = 0
  · simp only [cubicBesselAmplitude, cubicBesselAmplitudeDeriv, if_pos hh]
    exact hasDerivAt_const v 0
  have hr := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4 * Real.pi * ‖cuspFrequency h‖ * y)
      (4 * Real.pi * ‖cuspFrequency h‖) v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).const_mul (4 * Real.pi * ‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4 * Real.pi * ‖cuspFrequency h‖ * v)
    (by positivity)).scomp v hslope
  have he := ((Complex.ofRealCLM.hasDerivAt (x := v)).mul hk).const_mul (c h)
  simp only [cubicBesselAmplitude, cubicBesselAmplitudeDeriv, if_neg hh]
  convert! he using 1 <;>
    simp only [Function.comp_def, Pi.mul_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
      Complex.real_smul, mul_one, one_mul, mul_assoc]

def cubicBesselTerm (c : O → ℂ) (h : O) (p : ℝ × ℂ) : ℂ :=
  cubicBesselAmplitude c p.1 h * tracePhase (cuspFrequency h * p.2)

def cubicBesselTermFDeriv (c : O → ℂ) (h : O) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
    (cubicBesselAmplitudeDeriv c p.1 h * tracePhase (cuspFrequency h * p.2)) +
      cubicBesselTerm c h p • (horizontalPhaseCLM (cuspFrequency h)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma cubicBesselTerm_hasFDerivAt (c : O → ℂ) (h : O) (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasFDerivAt (cubicBesselTerm c h) (cubicBesselTermFDeriv c h p) p := by
  have hvd := (cubicBesselAmplitude_hasDerivAt c p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hzd := (tracePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  convert! hvd.mul hzd using 1
  apply ContinuousLinearMap.ext
  intro direction
  change (direction.1 : ℂ) * (cubicBesselAmplitudeDeriv c p.1 h * tracePhase (cuspFrequency h * p.2)) +
      cubicBesselTerm c h p * horizontalPhaseCLM (cuspFrequency h) direction.2 =
    cubicBesselAmplitude c p.1 h *
      (tracePhase (cuspFrequency h * p.2) * horizontalPhaseCLM (cuspFrequency h) direction.2) +
      tracePhase (cuspFrequency h * p.2) * ((direction.1 : ℂ) * cubicBesselAmplitudeDeriv c p.1 h)
  unfold cubicBesselTerm
  ring

lemma cubicBesselTerm_strip_bound (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, ∀ p : ℝ × ℂ, p.1 ∈ Icc a b →
      ‖cubicBesselTerm c h p‖ ≤ C * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselCoefficient_strip_bound c hsub a b ha hab
  refine ⟨C, hC, ?_⟩
  intro h p hp
  by_cases hh : h = 0
  · simp only [cubicBesselTerm, cubicBesselAmplitude, if_pos hh, zero_mul, norm_zero]
    positivity
  · simp only [cubicBesselTerm, cubicBesselAmplitude, if_neg hh, norm_mul, tracePhase_norm, mul_one]
    simpa only [norm_mul] using hb h hh p.1 hp

lemma cubicBesselTerm_summable_norm (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    Summable (fun h : O => ‖cubicBesselTerm c h p‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselTerm_strip_bound c hsub p.1 p.1 hp le_rfl
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => hb h p ⟨le_rfl, le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi * p.1) (mul_pos Real.pi_pos hp)).mul_left C)

/-- The frequency gap converts Bessel and Bessel-derivative decay into a common summable scale. -/
lemma cubicBesselCoefficient_weighted_bounds (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (a : ℝ) (ha : 0 < a) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ h : O, h ≠ 0 → ∀ v : ℝ, a ≤ v →
      ‖c h‖ * ‖schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ ≤
        A * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) ∧
      ‖c h‖ * ‖(cubicBesselRealDeriv (4 * Real.pi * ‖cuspFrequency h‖ * v) : ℂ)‖ ≤
        B * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  have hd : 0 < ‖(3 : ℂ) * ringComplex traceLambda‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  let δ : ℝ := 4 * Real.pi * a * ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨U, hU, hu⟩ := schlafliBesselK_one_third_exp_upper δ hδ
  obtain ⟨D, hD, hd⟩ := cubicBesselRealDeriv_exp_upper δ hδ
  obtain ⟨C, hC, hc⟩ := hsub (Real.pi * a) (mul_pos Real.pi_pos ha)
  refine ⟨C * U, C * D, mul_nonneg hC hU, mul_nonneg hC hD, ?_⟩
  intro h hh v hv
  have hx : δ ≤ 4 * Real.pi * ‖cuspFrequency h‖ * v := by
    have hm := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * Real.pi)
    dsimp [δ]
    nlinarith only [hm']
  have hcombine (y E : ℝ) (hy : 0 ≤ y) (hE : 0 ≤ E)
      (he : y ≤ E * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2)) :
      ‖c h‖ * y ≤ (C * E) * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
    calc
      _ ≤ (C * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖)) *
          (E * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2)) :=
        mul_le_mul (hc h hh) he hy (by positivity)
      _ = (C * E) * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖ +
          -(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) := by rw [Real.exp_add]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC hE)
        have hm := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * Real.pi * ‖cuspFrequency h‖)
        nlinarith only [hm]
  exact ⟨hcombine _ _ (norm_nonneg _) hU (hu _ hx), hcombine _ _ (norm_nonneg _) hD (hd _ hx)⟩

lemma cubicBesselAmplitudeDeriv_norm_le (c : O → ℂ) (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    ‖cubicBesselAmplitudeDeriv c v h‖ ≤
      ‖c h‖ * ‖schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ +
      (v * (4 * Real.pi * ‖cuspFrequency h‖)) *
        (‖c h‖ * ‖(cubicBesselRealDeriv (4 * Real.pi * ‖cuspFrequency h‖ * v) : ℂ)‖) := by
  rw [cubicBesselAmplitudeDeriv, if_neg hh, norm_mul]
  calc
    _ ≤ ‖c h‖ * (‖schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ +
        ‖(v : ℂ) * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) *
          (cubicBesselRealDeriv (4 * Real.pi * ‖cuspFrequency h‖ * v) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0 ≤ 4 * Real.pi * ‖cuspFrequency h‖)]
      ring

lemma cubicBesselTermFDeriv_norm_le (c : O → ℂ) (h : O) (p : ℝ × ℂ) :
    ‖cubicBesselTermFDeriv c h p‖ ≤ ‖cubicBesselAmplitudeDeriv c p.1 h‖ +
      ‖cubicBesselTerm c h p‖ * (4 * Real.pi * ‖cuspFrequency h‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  change ‖(direction.1 : ℂ) * (cubicBesselAmplitudeDeriv c p.1 h * tracePhase (cuspFrequency h * p.2)) +
    cubicBesselTerm c h p * horizontalPhaseCLM (cuspFrequency h) direction.2‖ ≤ _
  calc
    _ ≤ ‖(direction.1 : ℂ) * (cubicBesselAmplitudeDeriv c p.1 h * tracePhase (cuspFrequency h * p.2))‖ +
        ‖cubicBesselTerm c h p * horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖ * ‖cubicBesselAmplitudeDeriv c p.1 h‖ +
        ‖cubicBesselTerm c h p‖ * ‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, tracePhase_norm, mul_one, norm_mul, horizontalPhaseCLM_apply]
      rfl
    _ ≤ ‖direction‖ * ‖cubicBesselAmplitudeDeriv c p.1 h‖ +
        ‖cubicBesselTerm c h p‖ * ((4 * Real.pi * ‖cuspFrequency h‖) * ‖direction‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (norm_fst_le direction) (norm_nonneg _)
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (horizontalPhaseMultiplier_norm _ _).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le direction) (by positivity))
    _ = _ := by ring

lemma cubicBesselTermFDeriv_strip_bound (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, ∀ p : ℝ × ℂ, p.1 ∈ Icc a b →
      ‖cubicBesselTermFDeriv c h p‖ ≤ C * ((1 + ‖cuspFrequency h‖) *
        Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖)) := by
  obtain ⟨A, B, hA, hB, hweighted⟩ := cubicBesselCoefficient_weighted_bounds c hsub a ha
  obtain ⟨T, hT, ht⟩ := cubicBesselTerm_strip_bound c hsub a b ha hab
  let D := B * b * (4 * Real.pi) + T * (4 * Real.pi)
  have hb := ha.trans_le hab
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A + D, add_nonneg hA hD, ?_⟩
  intro h p hp
  by_cases hh : h = 0
  · have hz : cubicBesselTermFDeriv c h p = 0 := by
      subst h
      apply ContinuousLinearMap.ext
      intro direction
      simp [cubicBesselTermFDeriv, cubicBesselAmplitudeDeriv, cubicBesselTerm, cubicBesselAmplitude]
    rw [hz, norm_zero]
    positivity
  have hv := ha.trans_le hp.1
  obtain ⟨hKu, hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖cubicBesselAmplitudeDeriv c p.1 h‖ ≤
      A * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) +
      (b * (4 * Real.pi * ‖cuspFrequency h‖)) *
        (B * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖)) := by
    apply (cubicBesselAmplitudeDeriv_norm_le c p.1 hv h hh).trans
    apply add_le_add hKu
    exact mul_le_mul (mul_le_mul_of_nonneg_right hp.2 (by positivity)) hKd
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  calc
    _ ≤ ‖cubicBesselAmplitudeDeriv c p.1 h‖ + ‖cubicBesselTerm c h p‖ *
        (4 * Real.pi * ‖cuspFrequency h‖) := cubicBesselTermFDeriv_norm_le c h p
    _ ≤ (A * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) +
        (b * (4 * Real.pi * ‖cuspFrequency h‖)) * (B * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖))) +
        (T * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖)) * (4 * Real.pi * ‖cuspFrequency h‖) :=
      add_le_add hamp (mul_le_mul_of_nonneg_right (ht h p hp) (by positivity))
    _ = (A + D * ‖cuspFrequency h‖) * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by dsimp [D]; ring
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith only [mul_nonneg hA (norm_nonneg (cuspFrequency h)), hD]

/-- Local uniform derivative bounds give joint differentiability in height and horizontal position. -/
theorem cubicBesselSeries_hasFDerivAt (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasFDerivAt (fun q : ℝ × ℂ => ∑' h : O, cubicBesselTerm c h q)
      (∑' h : O, cubicBesselTermFDeriv c h p) p := by
  have ha : 0 < p.1 / 2 := half_pos hp
  have hab : p.1 / 2 ≤ 2 * p.1 := by linarith only [hp]
  obtain ⟨C, hC, hb⟩ := cubicBesselTermFDeriv_strip_bound c hsub _ _ ha hab
  have hs : Summable (fun h : O => (1 + ‖cuspFrequency h‖) *
      Real.exp (-(Real.pi * (p.1 / 2)) * ‖cuspFrequency h‖)) := by
    simpa only [add_mul, one_mul] using
      (summable_exp_neg_cuspFrequency_norm (Real.pi * (p.1 / 2)) (mul_pos Real.pi_pos ha)).add
        (cuspFrequency_firstMoment_exp_summable (Real.pi * (p.1 / 2)) (mul_pos Real.pi_pos ha))
  have hmem : p ∈ Ioo (p.1 / 2) (2 * p.1) ×ˢ (univ : Set ℂ) :=
    ⟨⟨by linarith only [hp], by linarith only [hp]⟩, mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected
    (f := cubicBesselTerm c) (f' := cubicBesselTermFDeriv c)
    (hs.mul_left C) (isOpen_Ioo.prod isOpen_univ) (isPreconnected_Ioo.prod isPreconnected_univ)
    (fun h q hq => cubicBesselTerm_hasFDerivAt c h q (ha.trans hq.1.1))
    (fun h q hq => hb h q ⟨hq.1.1.le, hq.1.2.le⟩) hmem
    (cubicBesselTerm_summable_norm c hsub p hp).of_norm hmem

lemma positiveHeight_cpow_hasDerivAt (s : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  have he := (hasDerivAt_id' (x := (x : ℂ))).cpow_const (c := s)
    (Complex.ofReal_mem_slitPlane.mpr hx)
  simpa using he.comp_ofReal

/-- In positive cusp coordinates the actual residual source is its constant mode plus the Bessel series. -/
theorem cubicSourceResidualFunction_bessel_coordinates (p : ℝ × ℂ) (hp : 0 < p.1) :
    cubicSourceResidualFunction (cuspCoordinateLift p) =
      (3 * (Real.pi : ℂ) * constantArithmeticResidue) * (p.1 : ℂ) ^ (2 / 3 : ℂ) +
        ∑' h : O, cubicBesselTerm rationalSourceResidualFourierCoefficient h p := by
  have hs := (cubicBesselTerm_summable_norm rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential p hp).of_norm
  have hz : Summable (fun h : O => if h = 0 then rationalSourceModeAmplitude p.1 0 else 0) :=
    (hasSum_ite_eq 0 _).summable
  have hsplit (h : O) : rationalSourceModeAmplitude p.1 h * tracePhase (cuspFrequency h * p.2) =
      (if h = 0 then rationalSourceModeAmplitude p.1 0 else 0) +
        cubicBesselTerm rationalSourceResidualFourierCoefficient h p := by
    by_cases hh : h = 0
    · subst h
      simp only [cubicBesselTerm, cubicBesselAmplitude, if_true, zero_mul, add_zero,
        cuspFrequency, map_zero, zero_div, AddChar.map_zero_eq_one, mul_one]
    · rw [rationalSourceModeAmplitude_bessel p.1 hp h hh]
      simp only [cubicBesselTerm, cubicBesselAmplitude, if_neg hh, zero_add]
  rw [show cuspCoordinateLift p = upperPoint p.2 p.1 hp from cuspCoordinateLift_positive _ _ hp,
    cubicSourceResidualFunction_fourier_expansion, cuspCharacterSeries]
  simp_rw [hsplit]
  rw [hz.tsum_add hs, tsum_ite_eq, rationalSourceModeAmplitude_zero]

/-- The actual residual source is jointly differentiable in height and horizontal position. -/
theorem cubicSourceResidualFunction_coordinate_differentiableAt (p : ℝ × ℂ) (hp : 0 < p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => cubicSourceResidualFunction (cuspCoordinateLift q)) p := by
  have hs := (cubicBesselSeries_hasFDerivAt rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential p hp).differentiableAt
  have hc : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      (3 * (Real.pi : ℂ) * constantArithmeticResidue) * (q.1 : ℂ) ^ (2 / 3 : ℂ)) p := by
    exact ((positiveHeight_cpow_hasDerivAt (2 / 3) p.1 hp).differentiableAt.comp p
      differentiableAt_fst).const_mul _
  apply (hc.add hs).congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact cubicSourceResidualFunction_bessel_coordinates q hq

/-- The positive denominator of the hyperbolic Möbius action in cusp coordinates. -/
def mobiusCoordinateDenominator (g : SL(2, ℂ)) (p : ℝ × ℂ) : ℝ :=
  Complex.normSq (g 1 0 * p.2 + g 1 1) + Complex.normSq (g 1 0) * p.1 ^ 2

lemma mobiusCoordinateDenominator_pos (g : SL(2, ℂ)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    0 < mobiusCoordinateDenominator g p := by
  simpa only [mobiusCoordinateDenominator, Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g p.2 p.1 hp

/-- Height and horizontal position under the hyperbolic Möbius action. -/
def mobiusCoordinates (g : SL(2, ℂ)) (p : ℝ × ℂ) : ℝ × ℂ :=
  (p.1 / mobiusCoordinateDenominator g p,
    ((g 0 0 * p.2 + g 0 1) * star (g 1 0 * p.2 + g 1 1) +
      g 0 0 * star (g 1 0) * (p.1 : ℂ) ^ 2) / (mobiusCoordinateDenominator g p : ℂ))

lemma mobiusCoordinates_height_pos (g : SL(2, ℂ)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    0 < (mobiusCoordinates g p).1 := div_pos hp (mobiusCoordinateDenominator_pos g p hp)

lemma mobiusCoordinates_differentiableAt (g : SL(2, ℂ)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    DifferentiableAt ℝ (mobiusCoordinates g) p := by
  have hd := (mobiusCoordinateDenominator_pos g p hp).ne'
  have hden : DifferentiableAt ℝ (mobiusCoordinateDenominator g) p := by
    unfold mobiusCoordinateDenominator
    simp only [Complex.normSq_apply]
    fun_prop
  have hinv := (hasDerivAt_inv hd).differentiableAt.comp p hden
  have hheight : DifferentiableAt ℝ (fun q : ℝ × ℂ => q.1 / mobiusCoordinateDenominator g q) p := by
    convert! (differentiableAt_fst (𝕜 := ℝ)).mul hinv using 1 <;>
      simp only [div_eq_mul_inv, Pi.mul_apply, Function.comp_def]
  have hnum : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
    (g 0 0 * q.2 + g 0 1) * star (g 1 0 * q.2 + g 1 1) +
      g 0 0 * star (g 1 0) * (q.1 : ℂ) ^ 2) p := by fun_prop
  apply hheight.prodMk
  convert! hnum.mul (Complex.ofRealCLM.differentiableAt.comp p hinv) using 1 <;>
    simp only [Complex.ofReal_inv, div_eq_mul_inv, Pi.mul_apply, Function.comp_def,
      Complex.ofRealCLM_apply] <;> rfl

lemma mobiusCoordinates_lift (g : SL(2, ℂ)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    cuspCoordinateLift (mobiusCoordinates g p) = g • cuspCoordinateLift p := by
  rw [show cuspCoordinateLift p = upperPoint p.2 p.1 hp from cuspCoordinateLift_positive _ _ hp,
    show cuspCoordinateLift (mobiusCoordinates g p) =
      upperPoint (mobiusCoordinates g p).2 (mobiusCoordinates g p).1
        (mobiusCoordinates_height_pos g p hp) from cuspCoordinateLift_positive _ _ _,
    mobius_upperPoint]
  apply upperPoint_congr
  · simp only [mobiusCoordinates, mobiusCoordinateDenominator, Complex.normSq_eq_norm_sq]
  · simp only [mobiusCoordinates, mobiusCoordinateDenominator, Complex.normSq_eq_norm_sq]

/-- Every fixed cusp translate of the actual source is jointly differentiable. -/
theorem cubicSourceResidualFunction_translate_coordinate_differentiableAt
    (g : SL(2, ℂ)) (p : ℝ × ℂ) (hp : 0 < p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => cubicSourceResidualFunction (g • cuspCoordinateLift q)) p := by
  have hd := (cubicSourceResidualFunction_coordinate_differentiableAt (mobiusCoordinates g p)
    (mobiusCoordinates_height_pos g p hp)).comp p (mobiusCoordinates_differentiableAt g p hp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg cubicSourceResidualFunction (mobiusCoordinates_lift g q hq).symm

/-- Inverse cusp coordinates centered at the image of infinity. -/
def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℝ × ℂ :=
  (v / (‖c‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2)),
    -d / c - star z / (c ^ 2 * ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c ≠ 0) (hv : 0 < v) : 0 < (inverseCuspCoordinates c d v z).1 := by
  dsimp [inverseCuspCoordinates]
  positivity

def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℝ × ℂ :=
  (v / (‖c‖ ^ 2 * (v ^ 2 + t ^ 2 * ‖direction‖ ^ 2)),
    -d / c - (t : ℂ) * star direction / (c ^ 2 * ((v ^ 2 + t ^ 2 * ‖direction‖ ^ 2 : ℝ) : ℂ)))

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t : ℂ) * direction) = inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates, inverseCuspPath, star_mul, Complex.star_def,
    Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ) (hc : c ≠ 0) (hv : 0 < v) :
    inverseCuspPath c d v direction 0 = (1 / (‖c‖ ^ 2 * v), -d / c) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero, zero_div, sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc, hv.ne']

/-- At the cusp center the vertical derivative vanishes and the horizontal derivative is conjugate-linear. -/
lemma inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ) (hc : c ≠ 0) (hv : 0 < v) :
    HasDerivAt (inverseCuspPath c d v direction) (0, -(star direction) / (c ^ 2 * (v : ℂ) ^ 2)) 0 := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ => v ^ 2 + t ^ 2 * ‖direction‖ ^ 2) 0 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖direction‖ ^ 2)).const_add (v ^ 2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ => (t : ℂ) * star direction) (star direction) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (star direction)
  have hdenC := hden.ofReal_comp.const_mul (c ^ 2)
  have hdenR := hden.const_mul (‖c‖ ^ 2)
  have hcz : c ^ 2 * ((v ^ 2 + (0 : ℝ) ^ 2 * ‖direction‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖ ^ 2 * (v ^ 2 + (0 : ℝ) ^ 2 * ‖direction‖ ^ 2) ≠ 0 := by positivity
  have hz : HasDerivAt (fun t : ℝ => -d / c - (t : ℂ) * star direction /
      (c ^ 2 * ((v ^ 2 + t ^ 2 * ‖direction‖ ^ 2 : ℝ) : ℂ)))
      (-(star direction) / (c ^ 2 * (v : ℂ) ^ 2)) 0 := by
    convert! (hnum.div hdenC hcz).const_sub (-d / c) using 1
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero, Complex.ofReal_pow,
      Complex.ofReal_zero, mul_zero, sub_zero]
    field_simp
  have hy : HasDerivAt (fun t : ℝ => v / (‖c‖ ^ 2 * (v ^ 2 + t ^ 2 * ‖direction‖ ^ 2))) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) v).div hdenR hrz using 1 <;> simp
  exact hy.prodMk hz

lemma inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ) (hc : c ≠ 0) (hv : 0 < v)
    (F : ℝ × ℂ → ℂ) (A : (ℝ × ℂ) →L[ℝ] ℂ)
    (hF : HasFDerivAt F A (1 / (‖c‖ ^ 2 * v), -d / c)) :
    HasDerivAt (fun t => F (inverseCuspPath c d v direction t))
      (A (0, -(star direction) / (c ^ 2 * (v : ℂ) ^ 2))) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

/-- The inverse hyperbolic action has the centered cusp-coordinate formula. -/
theorem inverse_cusp_action (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    g⁻¹ • upperPoint (z + g 0 0 / g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0 = g 1 1 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1 = -g 0 1 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0 = -g 1 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1 = g 0 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hl : (-g 1 0) * (z + g 0 0 / g 1 0) + g 0 0 = -(g 1 0 * z) := by field_simp; ring
  have ht : g 1 1 * (z + g 0 0 / g 1 0) + (-g 0 1) = g 1 1 * z + 1 / g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0 * z)‖ ^ 2 + ‖-g 1 0‖ ^ 2 * v ^ 2 =
      ‖g 1 0‖ ^ 2 * (v ^ 2 + ‖z‖ ^ 2) := by rw [norm_neg, norm_neg, norm_mul, mul_pow]; ring
  have hnormc : ((‖g 1 0‖ ^ 2 : ℝ) : ℂ) = g 1 0 * star (g 1 0) := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v ^ 2 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have hTc : ((v ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0) ≠ 0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00, h01, h10, h11, hl, ht, hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul, hnormc]
    simp only [Complex.star_def, map_neg, map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc, hcc, hTc]
    rw [Complex.ofReal_add, Complex.ofReal_pow, hnormz]
    simp only [Complex.star_def]
    ring
  · rw [h10, h11, hl, hden]
    rfl

def horizontalWirtingerZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (deriv (fun t : ℝ => f (z + (t : ℂ))) 0 -
    Complex.I * deriv (fun t : ℝ => f (z + (t : ℂ) * Complex.I)) 0)

lemma real_linear_horizontal_decompose (A : (ℝ × ℂ) →L[ℝ] ℂ) (z : ℂ) :
    A (0, z) = (z.re : ℂ) * A (0, 1) + (z.im : ℂ) * A (0, Complex.I) := by
  have hz : ((0, z) : ℝ × ℂ) = z.re • (0, 1) + z.im • (0, Complex.I) := by
    apply Prod.ext
    · simp
    · simpa only [Prod.snd_add, Prod.smul_snd, Complex.real_smul, mul_one] using z.re_add_im.symm
  rw [hz, map_add, map_smul, map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℝ × ℂ) →L[ℝ] ℂ) (k : ℂ) :
    (1 / 2 : ℂ) * (A (0, k) + Complex.I * A (0, -Complex.I * k)) =
      k * ((1 / 2 : ℂ) * (A (0, 1) - Complex.I * A (0, Complex.I))) := by
  rw [real_linear_horizontal_decompose A k, real_linear_horizontal_decompose A (-Complex.I * k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, zero_mul, neg_mul, one_mul, zero_add, zero_sub, Complex.ofReal_neg]
  conv_rhs => lhs; rw [← k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma horizontalWirtingerZ_eq_fderiv (F : ℝ × ℂ → ℂ) (A : (ℝ × ℂ) →L[ℝ] ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (v, z)) :
    horizontalWirtingerZ (fun w => F (v, w)) z =
      (1 / 2 : ℂ) * (A (0, 1) - Complex.I * A (0, Complex.I)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ => F (v, z + (t : ℂ) * direction)) (A (0, direction)) 0 := by
    have hz : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const direction).const_add z
    have hp := (hasDerivAt_const (0 : ℝ) v).prodMk hz
    have hf : HasFDerivAt F A (v, z + (0 : ℂ) * direction) := by simpa only [zero_mul, add_zero] using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ, h1, hI]

/-- Inverse cusp coordinates exchange the two horizontal Wirtinger derivatives. -/
theorem inverse_cusp_wirtinger_rule (c d : ℂ) (v : ℝ) (hc : c ≠ 0) (hv : 0 < v)
    (F : ℝ × ℂ → ℂ) (A : (ℝ × ℂ) →L[ℝ] ℂ)
    (hF : HasFDerivAt F A (1 / (‖c‖ ^ 2 * v), -d / c)) :
    horizontalWirtingerBar (fun z => F (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) *
        horizontalWirtingerZ (fun z => F (1 / (‖c‖ ^ 2 * v), z)) (-d / c) := by
  rw [horizontalWirtingerZ_eq_fderiv F A _ _ hF]
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ => F (inverseCuspCoordinates c d v (t : ℂ))) =
      (fun t : ℝ => F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [← inverseCuspCoordinates_line, mul_one]
  have heI : (fun t : ℝ => F (inverseCuspCoordinates c d v ((t : ℂ) * Complex.I))) =
      (fun t : ℝ => F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1, heI, h1, hI]
  simp only [star_one, Complex.star_def, Complex.conj_I, neg_neg]
  convert real_linear_wirtinger_swap A (-1 / (c ^ 2 * (v : ℂ) ^ 2)) using 1 <;> congr 2 <;> ring

lemma horizontalWirtingerBar_translate (f : ℂ → ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z => f (z + a)) 0 = horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add, add_zero, add_comm]

/-- The coordinate chain rule at a finite cusp interchanges the two Wirtinger derivatives. -/
lemma coordinate_cusp_wirtinger_rule (f : HyperbolicSpace → ℂ)
    (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v)
    (hf : DifferentiableAt ℝ (fun q : ℝ × ℂ => f (g • cuspCoordinateLift q))
      (1 / (‖g 1 0‖ ^ 2 * v), -g 1 1 / g 1 0)) :
    horizontalWirtingerBar (fun z => f (upperPoint z v hv)) (g 0 0 / g 1 0) =
      (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) * horizontalWirtingerZ
        (fun z => f (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
        (-g 1 1 / g 1 0) := by
  let F : ℝ × ℂ → ℂ := fun q => f (g • cuspCoordinateLift q)
  have hp : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have he (z : ℂ) : F (inverseCuspCoordinates (g 1 0) (g 1 1) v z) =
      f (upperPoint (z + g 0 0 / g 1 0) v hv) := by
    unfold F
    rw [show cuspCoordinateLift (inverseCuspCoordinates (g 1 0) (g 1 1) v z) =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) from cuspCoordinateLift_positive _ _ _,
      ← inverse_cusp_action g hc v hv z, smul_inv_smul]
  have hr := inverse_cusp_wirtinger_rule (g 1 0) (g 1 1) v hc hv F _ hf.hasFDerivAt
  rw [funext he] at hr
  have hr' := (horizontalWirtingerBar_translate
    (fun z => f (upperPoint z v hv)) (g 0 0 / g 1 0)).symm.trans hr
  simpa only [F, cuspCoordinateLift_positive _ _ hp] using hr'

/-- Cusp inversion acts on the actual residual source derivative with its exact weight. -/
theorem cubicSourceResidualFunction_cusp_derivative (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (fun z => cubicSourceResidualFunction (upperPoint z v hv)) (g 0 0 / g 1 0) =
      (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) * horizontalWirtingerZ
        (fun z => cubicSourceResidualFunction (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
        (-g 1 1 / g 1 0) :=
  coordinate_cusp_wirtinger_rule cubicSourceResidualFunction g hc v hv
    (cubicSourceResidualFunction_translate_coordinate_differentiableAt g _ (by positivity))

/-- The same exact cusp weight applies to the conjugate source used in the Gauss twists. -/
theorem conjugate_cubicSourceResidualFunction_cusp_derivative (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0)
    (v : ℝ) (hv : 0 < v) :
    horizontalWirtingerBar (fun z => star (cubicSourceResidualFunction (upperPoint z v hv)))
        (g 0 0 / g 1 0) =
      (-1 / ((g 1 0) ^ 2 * (v : ℂ) ^ 2)) * horizontalWirtingerZ
        (fun z => star (cubicSourceResidualFunction
          (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))) (-g 1 1 / g 1 0) := by
  apply coordinate_cusp_wirtinger_rule (fun w => star (cubicSourceResidualFunction w)) g hc v hv
  exact Complex.conjCLE.differentiableAt.comp _
    (cubicSourceResidualFunction_translate_coordinate_differentiableAt g _ (by positivity))

/-- A character has one nonzero Fourier coefficient, at its dual residue class. -/
lemma finiteAdditiveFourierCoeff_character {R : Type*} [CommRing R] [Fintype R]
    (ψ χ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ χ h = if χ = ψ.mulShift h then 1 else 0 := by
  classical
  by_cases he : χ = ψ.mulShift h
  · simp only [if_pos he, he, finiteAdditiveFourierCoeff, AddChar.mulShift_apply]
    have hp (x : R) : ψ (h * x) * ψ (-h * x) = 1 := by
      rw [← AddChar.map_add_eq_mul]
      simp
    simp only [hp, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  · rw [if_neg he, finiteAdditiveFourierCoeff]
    have hn : χ * ψ.mulShift (-h) ≠ 1 := by
      intro hh
      apply he
      ext x
      have hv : χ x * ψ (-h * x) = 1 := congrArg (fun φ : AddChar R ℂ => φ x) hh
      have hp : ψ (-h * x) * ψ (h * x) = 1 := by
        rw [← AddChar.map_add_eq_mul]
        simp
      change χ x = ψ (h * x)
      calc
        _ = χ x * (ψ (-h * x) * ψ (h * x)) := by rw [hp, mul_one]
        _ = _ := by rw [← mul_assoc, hv, one_mul]
    have hs := AddChar.sum_eq_zero_of_ne_one hn
    change (∑ x, χ x * ψ (-h * x)) = 0 at hs
    rw [hs, zero_div]

/-- A primitive trace character parametrizes every character of a finite ring. -/
theorem finiteAdditiveCharacter_exists_unique {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (χ : AddChar R ℂ) :
    ∃! h : R, χ = ψ.mulShift h := by
  classical
  have hex : ∃ h : R, χ = ψ.mulShift h := by
    by_contra hn
    push_neg at hn
    have hi := finiteAdditiveFourier_inversion ψ hψ χ 0
    simp only [finiteAdditiveFourierCoeff_character, if_neg (hn _), zero_mul,
      Finset.sum_const_zero, AddChar.map_zero_eq_one] at hi
    exact zero_ne_one hi
  obtain ⟨h, hh⟩ := hex
  refine ⟨h, hh, ?_⟩
  intro k hk
  exact AddChar.to_mulShift_inj_of_isPrimitive hψ (hk.symm.trans hh)

/-- Distinct primitive Fourier frequencies cannot carry the same translation character. -/
lemma period_fourier_zero_of_character (f : ℂ → ℂ)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z)
    (h : O) (b χ : ℂ) (hχ : χ ≠ tracePhase (cuspFrequency h * b))
    (htranslate : ∀ z, f (z + b) = χ * f z) :
    ∫ z in periodDomain, f z * tracePhase (-cuspFrequency h * z) = 0 := by
  have he := period_fourier_translation f hper h b
  simp only [htranslate, mul_assoc] at he
  rw [integral_const_mul] at he
  apply (mul_eq_zero.mp (show (χ - tracePhase (cuspFrequency h * b)) *
      (∫ z in periodDomain, f z * tracePhase (-cuspFrequency h * z)) = 0 by
    linear_combination he)).resolve_left (sub_ne_zero.mpr hχ)

/-- The scaled ramified row has the original cusp lattice as its period lattice. -/
def ramifiedScaledRow (t : O) (v : ℝ) (z : ℂ) : ℂ :=
  ramifiedSourceFunction t (cuspCoordinateLift (3 * v, 3 * z))

lemma ramifiedScaledRow_period (t : O) (v : ℝ) (hv : 0 < v) (n : O) (z : ℂ) :
    ramifiedScaledRow t v (z + 3 * ringComplex n) = ramifiedScaledRow t v z := by
  simp only [ramifiedScaledRow, cuspCoordinateLift_positive _ _ (show 0 < 3 * v by positivity)]
  exact ramifiedSourceFunction_scaled_period t (3 * v) (by positivity) n z

lemma ramifiedScaledRow_character (t x : O) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    ramifiedScaledRow t v (z + ringComplex x) =
      complexCharacter (ramifiedParabolic t x) * ramifiedScaledRow t v z := by
  simp only [ramifiedScaledRow, cuspCoordinateLift_positive _ _ (show 0 < 3 * v by positivity)]
  rw [mul_add, ramifiedSourceFunction_period, ramifiedParabolic_character]

/-- Nonzero ramified Fourier coefficients must match every cusp translation phase. -/
theorem ramifiedScaledRow_fourier_character (t h : O) (v : ℝ) (hv : 0 < v)
    (hh : (∫ z in periodDomain, ramifiedScaledRow t v z * tracePhase (-cuspFrequency h * z)) ≠ 0)
    (x : O) :
    tracePhase (cuspFrequency h * ringComplex x) = complexCharacter (ramifiedParabolic t x) := by
  by_contra hn
  exact hh (period_fourier_zero_of_character _ (ramifiedScaledRow_period t v hv) h
    (ringComplex x) (complexCharacter (ramifiedParabolic t x)) (Ne.symm hn)
    (ramifiedScaledRow_character t x v hv))

lemma ramifiedParabolic_zero (t : O) : ramifiedParabolic t 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [ramifiedParabolic]

lemma ramifiedParabolic_add (t x y : O) :
    ramifiedParabolic t (x + y) = ramifiedParabolic t x * ramifiedParabolic t y := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The stabilizer character at a lower cusp, expressed without choosing an embedding orientation. -/
def ramifiedCuspLinearChar (t : O) : AddChar O ℂ where
  toFun x := complexCharacter (ramifiedParabolic t x)
  map_zero_eq_one' := by rw [ramifiedParabolic_zero, map_one]
  map_add_eq_mul' x y := by rw [ramifiedParabolic_add, map_mul]

lemma ramifiedCuspLinearChar_period (t x : O) (hx : x ∈ Ideal.span {(3 : O)}) :
    ramifiedCuspLinearChar t x = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change complexCharacter (ramifiedParabolic t (3 * y)) = 1
  rw [ramifiedParabolic_three, map_pow, complexCharacter_cube]

def ramifiedCuspQuotientChar (t : O) : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ :=
  principalQuotientAddChar 3 (ramifiedCuspLinearChar t) (ramifiedCuspLinearChar_period t)

lemma ramifiedCuspQuotientChar_mk (t x : O) :
    ramifiedCuspQuotientChar t (Ideal.Quotient.mk (Ideal.span {(3 : O)}) x) =
      complexCharacter (ramifiedParabolic t x) :=
  principalQuotientAddChar_mk 3 _ _ x

section
local instance : Finite (O ⧸ Ideal.span {(3 : O)}) :=
  (Ideal.span {(3 : O)}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
local instance : Fintype (O ⧸ Ideal.span {(3 : O)}) := Fintype.ofFinite _

/-- The unique residue class carrying the ramified cusp character. -/
def ramifiedCuspFrequencyClass (t : O) : O ⧸ Ideal.span {(3 : O)} :=
  Classical.choose (finiteAdditiveCharacter_exists_unique
    (residueTraceQuotientChar 1 3 (by norm_num))
    (residueTraceQuotientChar_primitive 3 (by norm_num)) (ramifiedCuspQuotientChar t))

lemma ramifiedCuspFrequencyClass_spec (t : O) :
    ramifiedCuspQuotientChar t =
      (residueTraceQuotientChar 1 3 (by norm_num)).mulShift (ramifiedCuspFrequencyClass t) :=
  (Classical.choose_spec (finiteAdditiveCharacter_exists_unique
    (residueTraceQuotientChar 1 3 (by norm_num))
    (residueTraceQuotientChar_primitive 3 (by norm_num)) (ramifiedCuspQuotientChar t))).1

end

lemma residueTraceQuotientChar_three_phase (h x : O) :
    residueTraceQuotientChar h 3 (by norm_num) (Ideal.Quotient.mk _ x) =
      tracePhase (cuspFrequency h * ringComplex x) := by
  rw [residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul, map_ofNat]
  congr 1
  ring

/-- Each ramified cusp row is supported on one intrinsic residue class modulo three. -/
theorem ramifiedScaledRow_fourier_support (t h : O) (v : ℝ) (hv : 0 < v)
    (hoff : Ideal.Quotient.mk (Ideal.span {(3 : O)}) h ≠ ramifiedCuspFrequencyClass t) :
    ∫ z in periodDomain, ramifiedScaledRow t v z * tracePhase (-cuspFrequency h * z) = 0 := by
  by_contra hn
  have he : residueTraceQuotientChar h 3 (by norm_num) = ramifiedCuspQuotientChar t := by
    ext r
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [residueTraceQuotientChar_three_phase, ramifiedCuspQuotientChar_mk]
    exact ramifiedScaledRow_fourier_character t h v hv hn x
  rw [residueTraceQuotientChar_mulShift, ramifiedCuspFrequencyClass_spec] at he
  exact hoff (AddChar.to_mulShift_inj_of_isPrimitive
    (residueTraceQuotientChar_primitive 3 (by norm_num)) he)

lemma ramifiedCuspFrequencyClass_ne_zero (t : O)
    (ht : complexCharacter (ramifiedParabolic t 1) ≠ 1) : ramifiedCuspFrequencyClass t ≠ 0 := by
  intro hz
  have he := ramifiedCuspFrequencyClass_spec t
  rw [hz, AddChar.mulShift_zero] at he
  have hv := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ 1)) he
  rw [ramifiedCuspQuotientChar_mk, AddChar.one_apply] at hv
  exact ht hv

section
local instance : Finite (O ⧸ Ideal.span {(3 : O)}) :=
  (Ideal.span {(3 : O)}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
local instance : Fintype (O ⧸ Ideal.span {(3 : O)}) := Fintype.ofFinite _

/-- An integral representative of the dual phase of a ramified symbol. -/
def ramifiedArithmeticPhase (u : Oˣ) (n : ℕ) : O :=
  principalResidueRep 3 (Classical.choose (finiteAdditiveCharacter_exists_unique
    (residueTraceQuotientChar 1 3 (by norm_num))
    (residueTraceQuotientChar_primitive 3 (by norm_num)) (ramifiedQuotientChar u n)))

lemma ramifiedArithmeticPhase_spec (u : Oˣ) (n : ℕ) (x : O) :
    ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * x)) =
      tracePhase (cuspFrequency (ramifiedArithmeticPhase u n) * ringComplex x) := by
  have he := (Classical.choose_spec (finiteAdditiveCharacter_exists_unique
    (residueTraceQuotientChar 1 3 (by norm_num))
    (residueTraceQuotientChar_primitive 3 (by norm_num)) (ramifiedQuotientChar u n))).1
  have hh : ramifiedQuotientChar u n =
      residueTraceQuotientChar (ramifiedArithmeticPhase u n) 3 (by norm_num) := by
    rw [residueTraceQuotientChar_mulShift]
    simpa only [ramifiedArithmeticPhase, principalResidueRep_spec] using he
  have hv := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ x)) hh
  rw [residueTraceQuotientChar_three_phase] at hv
  exact (principalQuotientAddChar_mk 3 _ _ x).symm.trans hv

end

/-- Ramified denominator variation on a primary affine line is its additive character. -/
lemma ramified_symbol_primary_affine (u : Oˣ) (n : ℕ) (a x : O)
    (ha : lambda ^ 2 ∣ a - 1) :
    ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) =
      ringComplex (symbol ((u : O) * lambda ^ n) a) *
        tracePhase (cuspFrequency (ramifiedArithmeticPhase u n) * ringComplex x) := by
  obtain ⟨A, hA⟩ := three_dvd_lambda_sq.trans ha
  have hd : (3 : O) ∣ a + 3 * x - 1 := ⟨A + x, by linear_combination hA⟩
  have he : (3 : O) ∣ a * (1 + 3 * x) - 1 := ⟨A + a * x, by linear_combination hA⟩
  have h9 : (9 : O) ∣ a + 3 * x - a * (1 + 3 * x) :=
    ⟨-x * A, by linear_combination -3 * x * hA⟩
  rw [ramified_symbol_congr_mod_nine u n _ _ hd he h9,
    symbol_mul_denominator, map_mul, ramifiedArithmeticPhase_spec]

/-- Frequency for a cusp with horizontal period nine. -/
def ninthCuspFrequency (h : O) : ℂ := cuspFrequency h / 3

lemma affineCusp_phase_identity (h h1 q a k r x : O) (ha : a ≠ 0) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + r * a) :
    tracePhase (cuspFrequency r * ringComplex x) *
      tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * x) / ringComplex (q * a)) =
      tracePhase (ninthCuspFrequency h / ringComplex q) * residueAdditive (3 * k) a x := by
  rw [← AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have hk' := congrArg ringComplex hk
  simp only [map_mul, map_add, map_ofNat] at hk'
  simp only [ninthCuspFrequency, cuspFrequency, hh, map_mul, map_add, map_ofNat]
  rw [show ringComplex h1 = 3 * ringComplex k - ringComplex r * ringComplex a by
    linear_combination -hk']
  field_simp [ringComplex_ne_zero ha, ringComplex_ne_zero hq,
    ringComplex_ne_zero traceLambda_ne_zero] <;> ring

/-- The affine ramified summand factors into its phase and an ordinary cubic Gauss summand. -/
lemma affineCuspGaussTerm_factor (h h1 q a k x : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a) :
    (ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) *
      ringComplex (symbol (a + 3 * x) a)) *
        tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * x) / ringComplex (q * a)) =
      (tracePhase (ninthCuspFrequency h / ringComplex q) *
        (ringComplex (symbol ((u : O) * lambda ^ n) a) * ringComplex (symbol 3 a))) *
          (ringComplex (symbol x a) * residueAdditive (3 * k) a x) := by
  have hs : symbol (a + 3 * x) a = symbol (3 * x) a := symbol_congr ⟨1, by ring⟩
  rw [ramified_symbol_primary_affine u n a x hap, hs, symbol_mul_numerator 3 x a,
    map_mul ringComplex (symbol 3 a) (symbol x a)]
  have he := affineCusp_phase_identity h h1 q a k (ramifiedArithmeticPhase u n) x ha hq hh hk
  calc
    _ = (ringComplex (symbol ((u : O) * lambda ^ n) a) * ringComplex (symbol 3 a) *
        ringComplex (symbol x a)) *
      (tracePhase (cuspFrequency (ramifiedArithmeticPhase u n) * ringComplex x) *
        tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * x) / ringComplex (q * a))) := by ring
    _ = _ := by rw [he]; ring

/-- The two cubic symbols are absorbed into a quadratic ramified frequency factor. -/
lemma cubicUnitGaussSum_ramified_single_twist (k r a : O) (ha : a ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hr : IsCoprime (3 * r) a) :
    ringComplex (symbol r a) * ringComplex (symbol 3 a) * cubicUnitGaussSum k a =
      cubicUnitGaussSum (9 * r ^ 2 * k) a := by
  have hcop : IsCoprime a (9 * r ^ 2) := by
    rw [show (9 : O) = 3 * 3 by norm_num]
    exact ((hr.of_mul_left_left.mul_left hr.of_mul_left_left).mul_left
      hr.of_mul_left_right.pow_left).symm
  have ht := cubicUnitGaussSum_frequency_twist k a (9 * r ^ 2) ha hcop
  have hc : ringComplex (symbol r a) * ringComplex (symbol 3 a) *
      ringComplex (symbol (9 * r ^ 2) a) = 1 := by
    rw [← map_mul, ← map_mul, ← symbol_mul_numerator, ← symbol_mul_numerator]
    rw [show r * 3 * (9 * r ^ 2) = (3 * r) ^ 3 by ring,
      symbol_pow_numerator _ a hap, symbol_cube_of_isCoprime _ a hap hr, map_one]
  calc
    _ = (ringComplex (symbol r a) * ringComplex (symbol 3 a)) *
        (ringComplex (symbol (9 * r ^ 2) a) * cubicUnitGaussSum (k * (9 * r ^ 2)) a) := by rw [ht]
    _ = cubicUnitGaussSum (k * (9 * r ^ 2)) a := by rw [← mul_assoc, hc, one_mul]
    _ = _ := by congr 1; ring

/-- The finite affine Gauss sum at a ramified cusp branch. -/
def ramifiedAffineGauss (h q a : O) (u : Oˣ) (n : ℕ) : ℂ :=
  ∑' x : CubicUnitResidue a,
    (ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * principalResidueRep a x.1)) *
      ringComplex (symbol (a + 3 * principalResidueRep a x.1) a)) *
        tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * principalResidueRep a x.1) /
          ringComplex (q * a))

/-- The intrinsic additive phase affects the support but cancels from the unramified Gauss frequency. -/
theorem ramifiedAffineGauss_eq_unramified (h h1 q a k : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a) :
    ramifiedAffineGauss h q a u n = tracePhase (ninthCuspFrequency h / ringComplex q) *
      cubicUnitGaussSum (3 * ((u : O) * lambda ^ n) ^ 2 * h1) a := by
  have he : ramifiedAffineGauss h q a u n =
      (tracePhase (ninthCuspFrequency h / ringComplex q) *
        (ringComplex (symbol ((u : O) * lambda ^ n) a) * ringComplex (symbol 3 a))) *
          cubicUnitGaussSum k a := by
    rw [ramifiedAffineGauss, cubicUnitGaussSum, ← tsum_mul_left]
    exact tsum_congr (fun x => affineCuspGaussTerm_factor h h1 q a k
      (principalResidueRep a x.1) u n ha hap hq hh hk)
  rw [he, mul_assoc, cubicUnitGaussSum_ramified_single_twist k _ a ha hap
    (ramified_primary_coprime u n a hap)]
  congr 1
  apply cubicUnitGaussSum_frequency_congr _ _ a ha
  refine ⟨3 * ((u : O) * lambda ^ n) ^ 2 * ramifiedArithmeticPhase u n, ?_⟩
  linear_combination 3 * ((u : O) * lambda ^ n) ^ 2 * hk

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
