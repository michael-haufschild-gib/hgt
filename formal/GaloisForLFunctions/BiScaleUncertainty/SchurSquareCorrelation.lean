import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Diagonal tensor correlations and their exact increment defect

The squared correlation is realized by simultaneous translation of the literal
product source on the plane. Its finite Gram forms are integrals of squares.
The Lévy energy splits into the squared-correlation energy and a nonnegative
quartic defect, including when either energy is infinite.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SchurSquare
set_option autoImplicit false

def tensorWave (f : C_c(ℝ, ℝ)) (x : ℝ) (z : ℝ × ℝ) : ℝ :=
  f (z.1 + x) * f (z.2 + x)

def profile (f : C_c(ℝ, ℝ)) (x : ℝ) : ℝ := autocorr f x ^ 2

theorem profile_nonneg (f : C_c(ℝ, ℝ)) (x : ℝ) : 0 ≤ profile f x := sq_nonneg _

theorem profile_eq_zero_iff (f : C_c(ℝ, ℝ)) (x : ℝ) :
    profile f x = 0 ↔ autocorr f x = 0 := sq_eq_zero_iff

theorem profile_neg (f : C_c(ℝ, ℝ)) (x : ℝ) : profile f (-x) = profile f x := by
  simp only [profile, autocorr_neg]

theorem continuous_profile (f : C_c(ℝ, ℝ)) : Continuous (profile f) :=
  (continuous_autocorr_compact f).pow 2

theorem integrable_tensorWave_mul (f : C_c(ℝ, ℝ)) (x y : ℝ) :
    Integrable (fun z => tensorWave f x z * tensorWave f y z) (volume.prod volume) := by
  have hi := integrable_shift_mul_shift f.continuous f.hasCompactSupport x y
  apply (hi.mul_prod hi).congr
  filter_upwards [] with z
  dsimp [tensorWave]
  ring

/-- Actual product-space realization of the squared translation correlation. -/
theorem integral_tensorWave_mul (f : C_c(ℝ, ℝ)) (x y : ℝ) :
    (∫ z, tensorWave f x z * tensorWave f y z ∂volume.prod volume) =
      profile f (y - x) := by
  calc
    _ = ∫ z : ℝ × ℝ, (f (z.1 + x) * f (z.1 + y)) *
        (f (z.2 + x) * f (z.2 + y)) ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [tensorWave]
      ring
    _ = (∫ u, f (u + x) * f (u + y)) * ∫ u, f (u + x) * f (u + y) :=
      integral_prod_mul (μ := volume) (ν := volume)
        (fun u : ℝ => f (u + x) * f (u + y)) (fun u : ℝ => f (u + x) * f (u + y))
    _ = _ := by rw [integral_shift_mul_shift]; exact (sq _).symm

/-- The full squared Gram form is the energy of a concrete finite tensor packet. -/
theorem integral_tensorPacket_sq {ι : Type*} (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    (∫ z, (∑ i ∈ s, w i * tensorWave f (t i) z) ^ 2 ∂volume.prod volume) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * profile f (t i - t j) := by
  have he (z : ℝ × ℝ) : (∑ i ∈ s, w i * tensorWave f (t i) z) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (w i * w j) *
        (tensorWave f (t i) z * tensorWave f (t j) z) := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum s (fun i _ =>
    integrable_finsetSum s (fun j _ => (integrable_tensorWave_mul f (t i) (t j)).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum s (fun j _ => (integrable_tensorWave_mul f (t i) (t j)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_tensorWave_mul,
    show t j - t i = -(t i - t j) by ring, profile_neg]

/-- Squaring transfers every compact-source correlation to a pointwise nonnegative Bochner kernel. -/
theorem gram_nonneg {ι : Type*} (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * profile f (t i - t j) := by
  rw [← integral_tensorPacket_sq]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem increment_nonneg (f : C_c(ℝ, ℝ)) (x : ℝ) :
    0 ≤ profile f 0 - profile f x := by
  have h := abs_autocorr_le_zero f.hasCompactSupport f.continuous x
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [profile, ← sq, sq_abs, sub_nonneg] using hs

/-- The exact term discarded by the nonlinear cone transfer. -/
theorem increment_decomposition (f : C_c(ℝ, ℝ)) (x : ℝ) :
    (profile f 0 - profile f x) + (autocorr f 0 - autocorr f x) ^ 2 =
      2 * autocorr f 0 * (autocorr f 0 - autocorr f x) := by
  dsimp [profile]
  ring

theorem increment_le (f : C_c(ℝ, ℝ)) (x : ℝ) :
    profile f 0 - profile f x ≤ 2 * autocorr f 0 * (autocorr f 0 - autocorr f x) := by
  nlinarith only [increment_decomposition f x, sq_nonneg (autocorr f 0 - autocorr f x)]

def levyEnergy (f : C_c(ℝ, ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((profile f 0 - profile f x) * archLevySinhWeight x)

def quarticDefect (f : C_c(ℝ, ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((autocorr f 0 - autocorr f x) ^ 2 * archLevySinhWeight x)

private theorem measurable_weight : Measurable archLevySinhWeight :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).measurable).div
    Real.continuous_sinh.measurable

/-- An exact nonnegative energy split, with no finiteness or regularity premise. -/
theorem levyEnergy_add_quarticDefect (f : C_c(ℝ, ℝ)) :
    levyEnergy f + quarticDefect f = ENNReal.ofReal (2 * autocorr f 0) *
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) := by
  have hm : Measurable (fun x => ENNReal.ofReal
      ((profile f 0 - profile f x) * archLevySinhWeight x)) :=
    ((measurable_const.sub (continuous_profile f).measurable).mul
      measurable_weight).ennreal_ofReal
  rw [levyEnergy, quarticDefect, ← lintegral_add_left hm]
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * autocorr f 0) *
        ENNReal.ofReal ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [← ENNReal.ofReal_add
        (mul_nonneg (increment_nonneg f x) (archLevySinhWeight_pos hx).le)
        (mul_nonneg (sq_nonneg (autocorr f 0 - autocorr f x)) (archLevySinhWeight_pos hx).le),
        ← add_mul, increment_decomposition, mul_assoc,
        ENNReal.ofReal_mul (mul_nonneg (by positivity) (autocorr_zero_nonneg f))]
    _ = _ := lintegral_const_mul _
      (((measurable_const.sub (continuous_autocorr_compact f).measurable).mul
        measurable_weight).ennreal_ofReal)

theorem levyEnergy_le (f : C_c(ℝ, ℝ)) :
    levyEnergy f ≤ ENNReal.ofReal (2 * autocorr f 0) *
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) := by
  rw [← levyEnergy_add_quarticDefect]
  exact le_self_add

end GaloisForLFunctions.BiScaleUncertainty.SchurSquare
