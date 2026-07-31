import Mathlib
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments
import GaloisForLFunctions.RHTower.TrivialZeroFirstDerivative

/-!
# The explicit Poisson-source test function

The even Schwartz function

`f(x) = x² (x² - 3/(2π)) e^{-π x²}`

vanishes at the origin together with its integral, so it lies in the source space of Meyer's
Poisson operator.  Its Mellin transform is the closed form

`ℳf(s) = (s-1)/4 · π^{-(s+4)/2} · Γ((s+2)/2)`,

valid on `Re s > -2`, which vanishes only at `s = 1`.  In particular it is nonzero at every
point of `[-1, 0)`, the range travelled by the terminal pole of the bounded-exponent Euler
multiplier.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The explicit even Schwartz test function of the Poisson source space. -/
noncomputable def meyerPoissonTest (x : ℝ) : ℝ :=
  x ^ 2 * (x ^ 2 - 3 / (2 * Real.pi)) * Real.exp (-Real.pi * x ^ 2)

theorem continuous_meyerPoissonTest : Continuous meyerPoissonTest := by
  unfold meyerPoissonTest
  fun_prop

theorem meyerPoissonTest_even (x : ℝ) : meyerPoissonTest (-x) = meyerPoissonTest x := by
  simp [meyerPoissonTest]

theorem meyerPoissonTest_abs (x : ℝ) : meyerPoissonTest |x| = meyerPoissonTest x := by
  rw [meyerPoissonTest, meyerPoissonTest, sq_abs]

theorem meyerPoissonTest_zero : meyerPoissonTest 0 = 0 := by
  simp [meyerPoissonTest]

theorem integrableOn_pow_mul_gaussian (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-Real.pi * t ^ 2)) (Ioi 0) := by
  have hn : (-1 : ℝ) < (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos (s := (n : ℝ)) hn
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]

/-- The source test function integrates to zero over the ray. -/
theorem integral_Ioi_meyerPoissonTest : (∫ t in Ioi (0 : ℝ), meyerPoissonTest t) = 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsplit : ∀ t : ℝ, meyerPoissonTest t
      = t ^ 4 * Real.exp (-Real.pi * t ^ 2)
        - 3 / (2 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)) := by
    intro t
    rw [meyerPoissonTest]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hsplit t)]
  rw [integral_sub (integrableOn_pow_mul_gaussian 4)
    ((integrableOn_pow_mul_gaussian 2).const_mul _)]
  rw [integral_const_mul, integral_Ioi_pow_four_gaussian, integral_Ioi_sq_gaussian]
  field_simp
  ring

/-- **The source test function has vanishing integral**, i.e. its Fourier transform vanishes at
the origin. -/
theorem integral_meyerPoissonTest : (∫ x : ℝ, meyerPoissonTest x) = 0 := by
  have h : (∫ x : ℝ, meyerPoissonTest x) = ∫ x : ℝ, meyerPoissonTest |x| := by
    congr 1
    funext x
    exact (meyerPoissonTest_abs x).symm
  rw [h, integral_comp_abs, integral_Ioi_meyerPoissonTest, mul_zero]

/-! ## Mellin transform -/

theorem mellinConvergent_cpow_gaussian {s : ℂ} (n : ℕ) (h : 0 < (s + (n : ℂ)).re) :
    MellinConvergent (fun t : ℝ => (t : ℂ) ^ ((n : ℕ) : ℂ) • gaussianKernel t) s := by
  rw [MellinConvergent.cpow_smul]
  exact mellinConvergent_gaussianKernel h

/-- The source test is a Gaussian monomial difference. -/
theorem meyerPoissonTest_gaussian_decomposition (t : ℝ) :
    ((meyerPoissonTest t : ℝ) : ℂ)
      = (t : ℂ) ^ ((4 : ℕ) : ℂ) • gaussianKernel t
        - ((3 : ℂ) / (2 * (Real.pi : ℂ))) • ((t : ℂ) ^ ((2 : ℕ) : ℂ) • gaussianKernel t) := by
  rw [Complex.cpow_natCast, Complex.cpow_natCast, meyerPoissonTest, gaussianKernel,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp

theorem meyerPoissonTest_ofReal_eq_sub :
    (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ))
      = (fun t : ℝ => (t : ℂ) ^ ((4 : ℕ) : ℂ) • gaussianKernel t)
        - fun t : ℝ => ((3 : ℂ) / (2 * (Real.pi : ℂ))) •
            ((t : ℂ) ^ ((2 : ℕ) : ℂ) • gaussianKernel t) :=
  funext meyerPoissonTest_gaussian_decomposition

theorem re_add_natCast_four {s : ℂ} (hs : -2 < s.re) : 0 < (s + ((4 : ℕ) : ℂ)).re := by
  have hre : (s + ((4 : ℕ) : ℂ)).re = s.re + 4 := by simp
  rw [hre]
  linarith

theorem re_add_natCast_two {s : ℂ} (hs : -2 < s.re) : 0 < (s + ((2 : ℕ) : ℂ)).re := by
  have hre : (s + ((2 : ℕ) : ℂ)).re = s.re + 2 := by simp
  rw [hre]
  linarith

theorem mellinConvergent_meyerPoissonTest {s : ℂ} (hs : -2 < s.re) :
    MellinConvergent (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) s := by
  rw [meyerPoissonTest_ofReal_eq_sub]
  exact (hasMellin_sub (mellinConvergent_cpow_gaussian 4 (re_add_natCast_four hs))
    ((mellinConvergent_cpow_gaussian 2 (re_add_natCast_two hs)).const_smul _)).1

theorem aestronglyMeasurable_meyerPoissonTest :
    AEStronglyMeasurable (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
  (Complex.continuous_ofReal.comp continuous_meyerPoissonTest).aestronglyMeasurable

/-- The weighted ray integral of the modulus converges to the right of `-2`. -/
theorem integrableOn_rpow_mul_norm_meyerPoissonTest {s : ℂ} (hs : -2 < s.re) :
    IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * ‖((meyerPoissonTest x : ℝ) : ℂ)‖) (Ioi 0) :=
  (mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi
    aestronglyMeasurable_meyerPoissonTest).mp (mellinConvergent_meyerPoissonTest hs)

/-- **Mellin transform of the explicit source test function.** -/
theorem mellin_meyerPoissonTest {s : ℂ} (hs : -2 < s.re) :
    mellin (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) s
      = (s - 1) / 4 * (Real.pi : ℂ) ^ (-(s + 4) / 2) * Complex.Gamma ((s + 2) / 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have hre4' : 0 < (s + 4).re := by
    have hre : (s + (4 : ℂ)).re = s.re + 4 := by simp
    rw [hre]
    linarith
  have hre2' : 0 < (s + 2).re := by
    have hre : (s + (2 : ℂ)).re = s.re + 2 := by simp
    rw [hre]
    linarith
  have hF : MellinConvergent (fun t : ℝ => (t : ℂ) ^ ((4 : ℕ) : ℂ) • gaussianKernel t) s :=
    mellinConvergent_cpow_gaussian 4 (re_add_natCast_four hs)
  have hG : MellinConvergent
      (fun t : ℝ => ((3 : ℂ) / (2 * (Real.pi : ℂ))) •
        ((t : ℂ) ^ ((2 : ℕ) : ℂ) • gaussianKernel t)) s :=
    (mellinConvergent_cpow_gaussian 2 (re_add_natCast_two hs)).const_smul _
  have hsub : mellin ((fun t : ℝ => (t : ℂ) ^ ((4 : ℕ) : ℂ) • gaussianKernel t)
      - fun t : ℝ => ((3 : ℂ) / (2 * (Real.pi : ℂ))) •
        ((t : ℂ) ^ ((2 : ℕ) : ℂ) • gaussianKernel t)) s
      = mellin (fun t : ℝ => (t : ℂ) ^ ((4 : ℕ) : ℂ) • gaussianKernel t) s
        - mellin (fun t : ℝ => ((3 : ℂ) / (2 * (Real.pi : ℂ))) •
            ((t : ℂ) ^ ((2 : ℕ) : ℂ) • gaussianKernel t)) s := (hasMellin_sub hF hG).2
  rw [meyerPoissonTest_ofReal_eq_sub, hsub,
    mellin_cpow_smul, mellin_const_smul, mellin_cpow_smul]
  rw [show ((4 : ℕ) : ℂ) = (4 : ℂ) from by norm_num,
    show ((2 : ℕ) : ℂ) = (2 : ℂ) from by norm_num]
  rw [mellin_gaussianKernel hre4', mellin_gaussianKernel hre2']
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre : (s + (2 : ℂ)).re = s.re + 2 := by simp
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hwne : ((s + 2) / 2 : ℂ) ≠ 0 := div_ne_zero hs2 two_ne_zero
  have hGam : Complex.Gamma ((s + 4) / 2) = ((s + 2) / 2) * Complex.Gamma ((s + 2) / 2) := by
    rw [show ((s + 4) / 2 : ℂ) = (s + 2) / 2 + 1 from by ring, Complex.Gamma_add_one _ hwne]
  have hcp : (Real.pi : ℂ) ^ (-(s + 2) / 2)
      = (Real.pi : ℂ) ^ (-(s + 4) / 2) * (Real.pi : ℂ) := by
    rw [show (-(s + 2) / 2 : ℂ) = (-(s + 4) / 2) + 1 from by ring, Complex.cpow_add _ _ hpi,
      Complex.cpow_one]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, hGam, hcp, smul_eq_mul]
  field_simp
  ring

/-- The transform is nonzero away from `s = 1`; in particular on the segment travelled by the
terminal pole. -/
theorem mellin_meyerPoissonTest_ne_zero {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1) :
    mellin (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) s ≠ 0 := by
  rw [mellin_meyerPoissonTest hs]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have h1 : (s - 1) / 4 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hs1) (by norm_num)
  have h2 : (Real.pi : ℂ) ^ (-(s + 4) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hpi h.1
  have h3 : Complex.Gamma ((s + 2) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    refine ne_neg_natCast_of_zero_lt_re ?_ m
    have hwre : ((s + 2) / 2 : ℂ).re = (s.re + 2) / 2 := by
      rw [Complex.div_ofNat_re, Complex.add_re]
      norm_num
    rw [hwre]
    linarith
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

end RHTower
