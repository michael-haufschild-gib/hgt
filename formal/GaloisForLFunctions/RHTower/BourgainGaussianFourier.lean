/-
# Fourier representation of Bourgain's Gaussian spacing energy

The positive spacing kernel in `BourgainGaussianSpacing` is itself a Fourier
transform.  This file begins the exact bridge from spacing energy to a
twelfth moment by proving the normalized one-dimensional Gaussian identity
with Bourgain's `e(x) = exp(2πix)` convention.
-/
import GaloisForLFunctions.RHTower.BourgainGaussianSpacing
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory

namespace RHTower

noncomputable section

/-- Gaussian times the additive character of frequency `a`. -/
def bourgainGaussianFourierIntegrand (a x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * (x : ℂ) ^ (2 : ℕ))) *
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (x : ℂ))

theorem integrable_bourgainGaussianFourierIntegrand (a : ℝ) :
    Integrable (bourgainGaussianFourierIntegrand a) := by
  have hpi : (0 : ℝ) < (Real.pi : ℂ).re := by
    simpa using Real.pi_pos
  have hgauss :
      Integrable
        (fun x : ℝ =>
          Complex.exp (-((Real.pi : ℂ) * (x : ℂ) ^ (2 : ℕ)))) :=
    by
      convert integrable_cexp_neg_mul_sq hpi using 1
      funext x
      congr 1
      ring
  apply hgauss.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with x
    rw [Complex.norm_exp]
    simp

/-- Self-duality of the normalized Gaussian, in the precise sign and
`2π` convention used by Bourgain's spacing argument. -/
theorem integral_bourgainGaussianFourierIntegrand (a : ℝ) :
    ∫ x : ℝ, bourgainGaussianFourierIntegrand a x =
      (Real.exp (-Real.pi * a ^ (2 : ℕ)) : ℂ) := by
  have hpi : (0 : ℝ) < (Real.pi : ℂ).re := by
    simpa using Real.pi_pos
  have hpi_ne : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := fourierIntegral_gaussian
    (b := (Real.pi : ℂ)) hpi ((2 * Real.pi * a : ℝ) : ℂ)
  rw [show
      (Real.pi : ℂ) / (Real.pi : ℂ) = 1 by
        exact div_self hpi_ne,
    Complex.one_cpow, one_mul] at h
  have hexponent :
      -(((2 * Real.pi * a : ℝ) : ℂ) ^ (2 : ℕ)) /
          (4 * (Real.pi : ℂ)) =
        ((-Real.pi * a ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hexponent] at h
  rw [Complex.ofReal_exp]
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [bourgainGaussianFourierIntegrand]
  rw [mul_comm]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- Four-dimensional product kernel whose frequency is the scaled
coordinate difference `X·(u-v)`. -/
def bourgainGaussianPairIntegrand
    (X u v x : BourgainPhaseSpace) : ℂ :=
  ∏ j : Fin 4,
    bourgainGaussianFourierIntegrand
      (X j * (u j - v j)) (x j)

theorem integrable_bourgainGaussianPairIntegrand
    (X u v : BourgainPhaseSpace) :
    Integrable (bourgainGaussianPairIntegrand X u v) := by
  exact Integrable.fintype_prod fun j =>
    integrable_bourgainGaussianFourierIntegrand
      (X j * (u j - v j))

/-- Exact four-dimensional Fourier representation of one Gaussian spacing
kernel. -/
theorem integral_bourgainGaussianPairIntegrand
    (X u v : BourgainPhaseSpace) :
    ∫ x : BourgainPhaseSpace,
        bourgainGaussianPairIntegrand X u v x =
      (Real.exp (-Real.pi * bourgainScaledSqDist X u v) : ℂ) := by
  unfold bourgainGaussianPairIntegrand
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_bourgainGaussianFourierIntegrand]
  rw [← Complex.ofReal_prod]
  rw [← Real.exp_sum]
  congr 1
  simp only [bourgainScaledSqDist, Finset.mul_sum]

/-- Sum of all pair kernels in the six-fold Bourgain moment cloud. -/
def bourgainGaussianMomentIntegrand
    (H : ℕ) (X : BourgainPhaseSpace) (x : BourgainPhaseSpace) : ℂ :=
  ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
    bourgainGaussianPairIntegrand X
      (bourgainSixfoldMoment h) (bourgainSixfoldMoment h') x

theorem integrable_bourgainGaussianMomentIntegrand
    (H : ℕ) (X : BourgainPhaseSpace) :
    Integrable (bourgainGaussianMomentIntegrand H X) := by
  apply integrable_finsetSum
  intro h _
  apply integrable_finsetSum
  intro h' _
  exact integrable_bourgainGaussianPairIntegrand X
    (bourgainSixfoldMoment h) (bourgainSixfoldMoment h')

/-- The Gaussian spacing energy is exactly the Fourier integral of its pair
kernel sum. -/
theorem integral_bourgainGaussianMomentIntegrand
    (H : ℕ) (X : BourgainPhaseSpace) :
    ∫ x : BourgainPhaseSpace,
        bourgainGaussianMomentIntegrand H X x =
      (bourgainGaussianSpacingEnergy H X : ℂ) := by
  unfold bourgainGaussianMomentIntegrand bourgainGaussianSpacingEnergy
  push_cast
  rw [integral_finsetSum]
  · apply Fintype.sum_congr
    intro h
    rw [integral_finsetSum]
    · simp_rw [integral_bourgainGaussianPairIntegrand]
      simp_rw [Complex.ofReal_exp]
      push_cast
      rfl
    · intro h' _
      exact integrable_bourgainGaussianPairIntegrand X
        (bourgainSixfoldMoment h) (bourgainSixfoldMoment h')
  · intro h _
    apply integrable_finsetSum
    intro h' _
    exact integrable_bourgainGaussianPairIntegrand X
      (bourgainSixfoldMoment h) (bourgainSixfoldMoment h')

/-- Coordinatewise product of a spacing scale and a Fourier variable. -/
def bourgainCoordinateScale
    (X x : BourgainPhaseSpace) : BourgainPhaseSpace :=
  fun j => X j * x j

/-- Product Gaussian on the four-dimensional Fourier space. -/
def bourgainFourierGaussianWeight
    (x : BourgainPhaseSpace) : ℂ :=
  ∏ j : Fin 4,
    Complex.exp (-((Real.pi : ℂ) * (x j : ℂ) ^ (2 : ℕ)))

/-- A pair kernel is the product Gaussian times the additive character of
the difference vector. -/
theorem bourgainGaussianPairIntegrand_eq_character_sub
    (X u v x : BourgainPhaseSpace) :
    bourgainGaussianPairIntegrand X u v x =
      bourgainFourierGaussianWeight x *
        bourgainAdditiveCharacter
          (bourgainCoordinateScale X x) (u - v) := by
  unfold bourgainGaussianPairIntegrand bourgainFourierGaussianWeight
    bourgainAdditiveCharacter bourgainCoordinateScale bourgainDot
  simp only [bourgainGaussianFourierIntegrand, Pi.sub_apply,
    Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Additive character converts a vector difference into a character times
the conjugate character. -/
theorem bourgainAdditiveCharacter_sub
    (x u v : BourgainPhaseSpace) :
    bourgainAdditiveCharacter x (u - v) =
      bourgainAdditiveCharacter x u *
        (starRingEnd ℂ) (bourgainAdditiveCharacter x v) := by
  have hdot :
      bourgainDot x (u - v) =
        bourgainDot x u - bourgainDot x v := by
    unfold bourgainDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.sub_apply]
    ring
  rw [bourgainAdditiveCharacter, bourgainAdditiveCharacter,
    bourgainAdditiveCharacter, hdot]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The pair-kernel sum is a Gaussian times the squared norm of the
six-fold Fourier cloud. -/
theorem bourgainGaussianMomentIntegrand_eq_norm_sq
    (H : ℕ) (X x : BourgainPhaseSpace) :
    bourgainGaussianMomentIntegrand H X x =
      bourgainFourierGaussianWeight x *
        (‖∑ h : Fin 6 → Fin H,
          bourgainAdditiveCharacter
            (bourgainCoordinateScale X x)
            (bourgainSixfoldMoment h)‖ ^ (2 : ℕ) : ℝ) := by
  let G : ℂ := bourgainFourierGaussianWeight x
  let A : (Fin 6 → Fin H) → ℂ := fun h =>
    bourgainAdditiveCharacter
      (bourgainCoordinateScale X x) (bourgainSixfoldMoment h)
  have hinner (h : Fin 6 → Fin H) :
      (∑ h' : Fin 6 → Fin H,
          G * (A h * (starRingEnd ℂ) (A h'))) =
        (G * A h) *
          (∑ h' : Fin 6 → Fin H, (starRingEnd ℂ) (A h')) := by
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro h'
    ring
  have hconj :
      (∑ h : Fin 6 → Fin H, (starRingEnd ℂ) (A h)) =
        (starRingEnd ℂ) (∑ h : Fin 6 → Fin H, A h) := by
    rw [map_sum]
  unfold bourgainGaussianMomentIntegrand
  simp_rw [bourgainGaussianPairIntegrand_eq_character_sub,
    bourgainAdditiveCharacter_sub]
  change
    (∑ h : Fin 6 → Fin H,
      ∑ h' : Fin 6 → Fin H,
        G * (A h * (starRingEnd ℂ) (A h'))) =
      G * (‖∑ h : Fin 6 → Fin H, A h‖ ^ (2 : ℕ) : ℝ)
  calc
    (∑ h : Fin 6 → Fin H,
        ∑ h' : Fin 6 → Fin H,
          G * (A h * (starRingEnd ℂ) (A h'))) =
        ∑ h : Fin 6 → Fin H,
          (G * A h) *
            (∑ h' : Fin 6 → Fin H,
              (starRingEnd ℂ) (A h')) := by
      apply Fintype.sum_congr
      exact hinner
    _ = (∑ h : Fin 6 → Fin H, G * A h) *
          (∑ h' : Fin 6 → Fin H,
            (starRingEnd ℂ) (A h')) := by
      rw [Finset.sum_mul]
    _ = G * (∑ h : Fin 6 → Fin H, A h) *
          (starRingEnd ℂ) (∑ h : Fin 6 → Fin H, A h) := by
      rw [← Finset.mul_sum, hconj]
    _ = G * (‖∑ h : Fin 6 → Fin H, A h‖ ^ (2 : ℕ) : ℝ) := by
      rw [mul_assoc, show
        (∑ h : Fin 6 → Fin H, A h) *
            (starRingEnd ℂ) (∑ h : Fin 6 → Fin H, A h) =
          (‖∑ h : Fin 6 → Fin H, A h‖ ^ (2 : ℕ) : ℂ) by
        simpa [mul_comm] using
          Complex.conj_mul' (∑ h : Fin 6 → Fin H, A h)]
      push_cast
      rfl

/-- The six-fold Fourier cloud is exactly the sixth power of the original
short curve sum with unit coefficients. -/
theorem bourgainSixfoldFourierSum_eq_pow_six
    (H : ℕ) (z : BourgainPhaseSpace) :
    (∑ h : Fin 6 → Fin H,
        bourgainAdditiveCharacter z (bourgainSixfoldMoment h)) =
      bourgainShortCurveSum H (fun _ => 1) z ^ (6 : ℕ) := by
  symm
  simpa [bourgainSixfoldWeight] using
    bourgainShortCurveSum_pow_six H (fun _ => 1) z

/-- Pointwise identification of the pair-kernel sum with the Gaussian-weighted
twelfth moment of Bourgain's original curve sum. -/
theorem bourgainGaussianMomentIntegrand_eq_twelfthMoment
    (H : ℕ) (X x : BourgainPhaseSpace) :
    bourgainGaussianMomentIntegrand H X x =
      bourgainFourierGaussianWeight x *
        (‖bourgainShortCurveSum H (fun _ => 1)
          (bourgainCoordinateScale X x)‖ ^ (12 : ℕ) : ℝ) := by
  rw [bourgainGaussianMomentIntegrand_eq_norm_sq]
  congr 1
  rw [bourgainSixfoldFourierSum_eq_pow_six]
  rw [norm_pow]
  rw [← pow_mul]

/-- Exact first-spacing/moment bridge.  The Gaussian spacing energy equals a
four-dimensional Gaussian-weighted twelfth moment of the original exponential
sum. -/
theorem integral_bourgainGaussianTwelfthMoment
    (H : ℕ) (X : BourgainPhaseSpace) :
    ∫ x : BourgainPhaseSpace,
        bourgainFourierGaussianWeight x *
          (‖bourgainShortCurveSum H (fun _ => 1)
            (bourgainCoordinateScale X x)‖ ^ (12 : ℕ) : ℝ) =
      (bourgainGaussianSpacingEnergy H X : ℂ) := by
  rw [← integral_bourgainGaussianMomentIntegrand H X]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (bourgainGaussianMomentIntegrand_eq_twelfthMoment H X x).symm

end

end RHTower
