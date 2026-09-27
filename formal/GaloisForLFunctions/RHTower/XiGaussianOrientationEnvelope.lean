import GaloisForLFunctions.RHTower.XiResidualOrientationBudget
import GaloisForLFunctions.HTGeometry.PolynomialHeatImaginaryBound

/-!
# Full polynomial heat phase charged to reciprocal orientation

The coefficient estimate is applied to the complete imaginary amplitude.
Polynomial phase and heat phase receive explicit factorial envelopes, while
every critical-line copy contributes exactly zero.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianOrientationMonomialEnvelope (j : ℕ) (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  2 * (j : ℝ) ^ 2 * ((2 * j + 2).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 2) +
    (t ^ 2 / 2) * ((2 * j + 4).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 4)

def xiGaussianOrientationEnvelope (N : ℕ) (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, xiGaussianOrientationMonomialEnvelope j s t

theorem xiGaussianOrientationMonomialEnvelope_nonneg (j : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 ≤ xiGaussianOrientationMonomialEnvelope j s t := by
  unfold xiGaussianOrientationMonomialEnvelope
  have hs := s.property
  positivity

theorem xiGaussianOrientationEnvelope_nonneg (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianOrientationEnvelope N s t :=
  Finset.sum_nonneg fun j _ => xiGaussianOrientationMonomialEnvelope_nonneg j s t

/-- Symbolic power-exponential control at every actual spectral coordinate. -/
theorem xiSpectralSq_norm_pow_heat_le_factorial (k : ℕ)
    (s : {s : ℝ // 0 < s}) (q : XiZeroCopy) :
    ‖xiSpectralPoint q ^ 2‖ ^ k * Real.exp (-((s : ℝ) * (xiSpectralPoint q ^ 2).re)) ≤
      (k.factorial : ℝ) * (2 / (s : ℝ)) ^ k := by
  let A := (xiSpectralPoint q ^ 2).re
  have hA : 0 < A := xiSpectralSq_re_pos q
  have hsector : ‖xiSpectralPoint q ^ 2‖ ≤ 2 * A := by
    rw [norm_pow]
    exact (by simpa only [Complex.sq_norm, A] using
      (xiSpectralPoint_normSq_lt_two_mul_sq_re q).le)
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hsector k) (Real.exp_pos (-((s : ℝ) * A))).le
  have hb := GaloisForLFunctions.HTGeometry.pow_mul_exp_neg_le
    (div_pos s.property (by positivity : (0 : ℝ) < 2)) k
    (show 0 ≤ 2 * A by positivity)
  rw [show (s : ℝ) / 2 * (2 * A) = (s : ℝ) * A by ring] at hb
  calc
    _ ≤ (2 * A) ^ k * Real.exp (-((s : ℝ) * A)) := hp
    _ ≤ (k.factorial : ℝ) / ((s : ℝ) / 2) ^ k := hb
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow, inv_div]

theorem xiSpectralSq_norm_pow_heat_le_residual_factorial (F : Finset XiZeroCopy) (k : ℕ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)})
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    ‖xiSpectralPoint q.1 ^ 2‖ ^ k * Real.exp (-((t.1 : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        ((k.factorial : ℝ) * (2 / (s : ℝ)) ^ k) := by
  let A := (xiSpectralPoint q.1 ^ 2).re
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  have he : Real.exp (-((t.1 : ℝ) * A)) ≤ e * Real.exp (-((s : ℝ) * A)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left (xiSpectralSq_re_gt_residualPhaseGap F q).le
      (sub_nonneg.mpr t.property)
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_left he (pow_nonneg (norm_nonneg (xiSpectralPoint q.1 ^ 2)) k)
  have hb := mul_le_mul_of_nonneg_left (xiSpectralSq_norm_pow_heat_le_factorial k s q.1)
    (show 0 ≤ e from (Real.exp_pos _).le)
  nlinarith only [h, hb]

/-- Each monomial's full phase is proportional to its actual transverse orientation. -/
theorem xiGaussianMonomial_im_sq_le_orientation_envelope
    (F : Finset XiZeroCopy) (j : ℕ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)})
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    (heatPhaseAmplitude ((xiSpectralPoint q.1 ^ 2) ^ j) t.1 (xiSpectralPoint q.1 ^ 2)).im ^ 2 ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianOrientationMonomialEnvelope j s t.1 * (xiZeroCopyReciprocalSquare q.1).im ^ 2 := by
  let z := xiSpectralPoint q.1 ^ 2
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  have hz : z ≠ 0 := pow_ne_zero _ (xiSpectralPoint_ne_zero q.1)
  have h := pow_heat_im_sq_le_reciprocal_orientation ⟨z, hz⟩ j t.1
  have hu : z⁻¹ = xiZeroCopyReciprocalSquare q.1 := by
    dsimp only [z, xiZeroCopyReciprocalSquare]
    rw [inv_pow]
  simp only [hu] at h
  have h₁ := mul_le_mul_of_nonneg_left
    (xiSpectralSq_norm_pow_heat_le_residual_factorial F (2 * j + 2) s t q)
    (show 0 ≤ 2 * (j : ℝ) ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left
    (xiSpectralSq_norm_pow_heat_le_residual_factorial F (2 * j + 4) s t q)
    (show 0 ≤ (t.1 : ℝ) ^ 2 / 2 by positivity)
  have hinner :
      (2 * (j : ℝ) ^ 2 * ‖z‖ ^ (2 * j + 2) + (t.1 : ℝ) ^ 2 / 2 * ‖z‖ ^ (2 * j + 4)) *
        Real.exp (-((t.1 : ℝ) * z.re)) ≤ e * xiGaussianOrientationMonomialEnvelope j s t.1 := by
    unfold xiGaussianOrientationMonomialEnvelope
    dsimp only [z, e]
    nlinarith only [h₁, h₂]
  have hb := mul_le_mul_of_nonneg_left hinner (sq_nonneg (xiZeroCopyReciprocalSquare q.1).im)
  nlinarith only [h, hb]

/-- Coefficient Cauchy--Schwarz is applied to the complete imaginary amplitude. -/
theorem xiGaussianImaginaryAtom_rangeSum_le_monomialPhase
    (N : ℕ) (a : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q ≤
        (∑ j ∈ Finset.range N, a j ^ 2) *
          ∑ j ∈ Finset.range N,
            (heatPhaseAmplitude ((xiSpectralPoint q ^ 2) ^ j) t (xiSpectralPoint q ^ 2)).im ^ 2 := by
  let Q := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let z := xiSpectralPoint q ^ 2
  let A := heatPhaseAmplitude (evalRealPolynomial Q z) t z
  have hsq : A ^ 2 = xiPolynomialGaussianHeatTerm Q t q := by
    rw [heatPhaseAmplitude_sq]
    rfl
  have hI : xiGaussianImaginaryChannelAtom Q t q = A.im ^ 2 := by
    rw [xiGaussianImaginaryChannelAtom, ← hsq, norm_pow, Complex.sq_norm,
      Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have him : A.im = ∑ j ∈ Finset.range N, a j * (heatPhaseAmplitude (z ^ j) t z).im := by
    dsimp only [A, Q]
    rw [evalRealPolynomial_rangeSum, heatPhaseAmplitude, Finset.sum_mul, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [heatPhaseAmplitude, mul_assoc, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  change xiGaussianImaginaryChannelAtom Q t q ≤ _
  rw [hI, him]
  exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) a
    (fun j => (heatPhaseAmplitude (z ^ j) t z).im)

/-- The whole polynomial is charged to the actual reciprocal orientation atom. -/
theorem xiGaussianImaginaryAtom_le_orientation_weight
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q ≤
        (Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianOrientationEnvelope N s t.1 * (∑ j ∈ Finset.range N, a j ^ 2)) *
            (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · rw [xiGaussianImaginaryChannelAtom_of_real _ t.1 ⟨q, hreal⟩]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (xiGaussianOrientationEnvelope_nonneg N s t.1))
      (Finset.sum_nonneg fun j _ => sq_nonneg (a j))) (sq_nonneg _)
  · have hcs := xiGaussianImaginaryAtom_rangeSum_le_monomialPhase N a t.1 q
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) =>
      xiGaussianMonomial_im_sq_le_orientation_envelope F j s t ⟨q, hreal⟩)
    have he : (∑ j ∈ Finset.range N,
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
          xiGaussianOrientationMonomialEnvelope j s t.1 * (xiZeroCopyReciprocalSquare q).im ^ 2) =
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianOrientationEnvelope N s t.1 * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
      simp only [xiGaussianOrientationEnvelope, Finset.mul_sum, Finset.sum_mul]
    rw [he] at hs
    have hb := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ ∑ j ∈ Finset.range N, a j ^ 2 from Finset.sum_nonneg fun j _ => sq_nonneg (a j))
    nlinarith only [hcs, hb]

end RHTower
