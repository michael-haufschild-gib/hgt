import GaloisForLFunctions.RHTower.ThetaQuantileFourierQuotient
import GaloisForLFunctions.RHTower.ThetaCdfFiniteRangeSymmetrizerNoGo
import GaloisForLFunctions.RHTower.ThetaQuantileResistanceNetwork
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Directed parity feedback in the literal theta quotient

The sine and cosine-defect CDF matrices are genuine positive Gram matrices. The exact quotient
Fourier coefficients split into their two parity channels, with a directed rank-one feedback in
the cosine channel. No symmetrizer or spectral-placement hypothesis is used.

The existing theta conductance Green law and unit capacity normalize that channel as P minus r:
P is nonnegative with row sum one and detailed balance, while r is a positive probability
sequence independent of the row. The final theorem identifies this feedback with the even/odd
matrix coefficient of the literal quotient operator. All-frequency row cancellation is exact.

This does not prove vanishing of transverse Schur charge. The frequency/conductance weights,
interaction with the sine sector, and singular infinite boundary remain part of GTA's problem.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace RHTower
open HedenmalmThetaSource
noncomputable section


private def angle (n : ℤ) (x : ℝ) : ℝ :=
  2 * Real.pi * n * thetaSource.cdfFun x

private def sine (n : ℤ) (x : ℝ) : ℝ := Real.sin (angle n x)
private def cosine (n : ℤ) (x : ℝ) : ℝ := 1 - Real.cos (angle n x)

private theorem angle_add (m n : ℤ) (x : ℝ) :
    angle (m + n) x = angle m x + angle n x := by
  simp only [angle, Int.cast_add]
  ring

private theorem angle_sub (m n : ℤ) (x : ℝ) :
    angle (m - n) x = angle m x - angle n x := by
  simp only [angle, Int.cast_sub]
  ring

private theorem sine_product (m n : ℤ) (x : ℝ) :
    sine m x * sine n x = (cosine (m + n) x - cosine (m - n) x) / 2 := by
  simp only [sine, cosine, angle_add, angle_sub, Real.cos_add, Real.cos_sub]
  ring

private theorem cosine_product (m n : ℤ) (x : ℝ) :
    cosine m x * cosine n x =
      cosine m x + cosine n x - (cosine (m + n) x + cosine (m - n) x) / 2 := by
  simp only [cosine, angle_add, angle_sub, Real.cos_add, Real.cos_sub]
  ring

private theorem integrable_cosine (n : ℤ) : Integrable (cosine n) :=
  integrable_cdfAction_integrand n

private theorem integrable_sine_product (m n : ℤ) :
    Integrable (fun x => sine m x * sine n x) := by
  simp_rw [sine_product]
  exact ((integrable_cosine (m + n)).sub (integrable_cosine (m - n))).div_const 2

private theorem integrable_cosine_product (m n : ℤ) :
    Integrable (fun x => cosine m x * cosine n x) := by
  simp_rw [cosine_product]
  exact ((integrable_cosine m).add (integrable_cosine n)).sub
    (((integrable_cosine (m + n)).add (integrable_cosine (m - n))).div_const 2)

/-- Sine Gram in exact theta CDF-action coordinates. -/
def thetaCdfSineGram (m n : ℤ) : ℝ := (cdfAction (m + n) - cdfAction (m - n)) / 2

/-- Cosine-defect Gram in exact theta CDF-action coordinates. -/
def thetaCdfCosineGram (m n : ℤ) : ℝ :=
  cdfAction m + cdfAction n - (cdfAction (m + n) + cdfAction (m - n)) / 2

/-- The sine matrix is a literal source Gram integral. -/
theorem thetaCdfSineGram_eq_integral (m n : ℤ) :
    thetaCdfSineGram m n =
      ∫ x, Real.sin (2 * Real.pi * m * thetaSource.cdfFun x) *
        Real.sin (2 * Real.pi * n * thetaSource.cdfFun x) := by
  change thetaCdfSineGram m n = ∫ x, sine m x * sine n x
  simp_rw [sine_product]
  rw [integral_div, integral_sub (integrable_cosine _) (integrable_cosine _)]
  rfl

/-- The cosine matrix is a literal source Gram integral. -/
theorem thetaCdfCosineGram_eq_integral (m n : ℤ) :
    thetaCdfCosineGram m n =
      ∫ x, (1 - Real.cos (2 * Real.pi * m * thetaSource.cdfFun x)) *
        (1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x)) := by
  change thetaCdfCosineGram m n = ∫ x, cosine m x * cosine n x
  simp_rw [cosine_product]
  change thetaCdfCosineGram m n =
    ∫ x, (cosine m + cosine n) x - (cosine (m + n) + cosine (m - n)) x / 2
  rw [integral_sub ((integrable_cosine m).add (integrable_cosine n))
    (((integrable_cosine (m + n)).add (integrable_cosine (m - n))).div_const 2),
    integral_div, integral_add' (integrable_cosine m) (integrable_cosine n),
    integral_add' (integrable_cosine (m + n)) (integrable_cosine (m - n))]
  rfl

private theorem real_integral_gram_posSemidef
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hint : ∀ i j, Integrable (fun x => f i x * f j x)) :
    Matrix.PosSemidef (fun i j => ∫ x, f i x * f j x) := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  · intro v
    have hterm (i j : ι) :
        Integrable (fun x => v i * v j * (f i x * f j x)) :=
      (hint i j).const_mul _
    have heq : star v ⬝ᵥ ((fun i j => ∫ x, f i x * f j x) *ᵥ v) =
        ∫ x, (∑ i, v i * f i x) ^ 2 := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      calc
        (∑ i, ∑ j, v i * ((∫ x, f i x * f j x) * v j)) =
            ∑ i, ∑ j, ∫ x, v i * v j * (f i x * f j x) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
          ring
        _ = ∫ x, ∑ i, ∑ j, v i * v j * (f i x * f j x) := by
          rw [integral_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun j _ => hterm i j]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum _ fun j _ => hterm i j]
        _ = ∫ x, (∑ i, v i * f i x) ^ 2 := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro x
          dsimp only
          rw [pow_two, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    rw [heq]
    exact integral_nonneg fun x => sq_nonneg _

/-- Every finite sine Gram is positive semidefinite, without a spectral premise. -/
theorem thetaCdfSineGram_posSemidef {ι : Type*} [Fintype ι] (freq : ι → ℤ) :
    Matrix.PosSemidef (fun i j => thetaCdfSineGram (freq i) (freq j)) := by
  simp_rw [thetaCdfSineGram_eq_integral]
  exact real_integral_gram_posSemidef (fun i => sine (freq i))
    (fun i j => integrable_sine_product (freq i) (freq j))

/-- Every finite cosine-defect Gram is positive semidefinite. -/
theorem thetaCdfCosineGram_posSemidef {ι : Type*} [Fintype ι] (freq : ι → ℤ) :
    Matrix.PosSemidef (fun i j => thetaCdfCosineGram (freq i) (freq j)) := by
  simp_rw [thetaCdfCosineGram_eq_integral]
  exact real_integral_gram_posSemidef (fun i => cosine (freq i))
    (fun i j => integrable_cosine_product (freq i) (freq j))

/-- Simultaneous Fourier reflection reverses the quotient coefficient. -/
theorem cdfQuotientMatrix_reflect (m n : ℤ) :
    cdfQuotientMatrix (-m) (-n) = -cdfQuotientMatrix m n := by
  rw [cdfQuotientMatrix, cdfQuotientMatrix, cdfAction_neg,
    show -n - -m = -(n - m) by ring, cdfAction_neg]
  push_cast
  ring

private theorem cdfQuotientMatrix_neg_left (m n : ℤ) :
    cdfQuotientMatrix (-m) n = -cdfQuotientMatrix m (-n) := by
  simpa only [neg_neg] using cdfQuotientMatrix_reflect m (-n)

private theorem fourier_entry {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    inner ℂ (unitFourierBasis m) (thetaQuotientOperator (unitFourierBasis n)) =
      (cdfQuotientMatrix m n : ℂ) := by
  simpa only [cdfQuotientMatrix] using
    inner_unitFourierBasis_thetaQuotientOperator hm hn

/-- Exact source pairing for arbitrary real combinations of the two Fourier parities. -/
theorem thetaQuotient_fourier_parity_pairing
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (e d : ℝ) :
    inner ℂ (unitFourierBasis m + (e : ℂ) • unitFourierBasis (-m))
      (thetaQuotientOperator (unitFourierBasis n + (d : ℂ) • unitFourierBasis (-n))) =
      (1 - (e : ℂ) * (d : ℂ)) * (cdfQuotientMatrix m n : ℂ) +
        ((d : ℂ) - (e : ℂ)) * (cdfQuotientMatrix m (-n) : ℂ) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [fourier_entry hm hn, fourier_entry hm (neg_ne_zero.mpr hn),
    fourier_entry (neg_ne_zero.mpr hm) hn,
    fourier_entry (neg_ne_zero.mpr hm) (neg_ne_zero.mpr hn),
    cdfQuotientMatrix_neg_left, cdfQuotientMatrix_reflect]
  push_cast
  ring

/-- One parity channel is the positive sine Gram with its column frequency weight. -/
theorem cdfQuotientMatrix_parity_sum (m n : ℤ) :
    cdfQuotientMatrix m n + cdfQuotientMatrix m (-n) =
      thetaCdfSineGram m n / (Real.pi * n) := by
  rw [cdfQuotientMatrix, cdfQuotientMatrix, thetaCdfSineGram,
    show -n - m = -(m + n) by ring, cdfAction_neg,
    show n - m = -(m - n) by ring, cdfAction_neg]
  push_cast
  ring

/-- The other parity channel retains its directed column feedback. -/
theorem cdfQuotientMatrix_parity_sub (m n : ℤ) :
    cdfQuotientMatrix m n - cdfQuotientMatrix m (-n) =
      (thetaCdfCosineGram m n - cdfAction n) / (Real.pi * n) := by
  rw [cdfQuotientMatrix, cdfQuotientMatrix, thetaCdfCosineGram,
    show -n - m = -(m + n) by ring, cdfAction_neg,
    show n - m = -(m - n) by ring, cdfAction_neg]
  push_cast
  ring

/-- Cosine-defect Gram entries are individually nonnegative. -/
theorem thetaCdfCosineGram_nonneg (m n : ℤ) : 0 ≤ thetaCdfCosineGram m n := by
  rw [thetaCdfCosineGram_eq_integral]
  exact integral_nonneg fun x => mul_nonneg
    (sub_nonneg.mpr (Real.cos_le_one _)) (sub_nonneg.mpr (Real.cos_le_one _))

/-- The underlying cosine-defect Gram is symmetric. -/
theorem thetaCdfCosineGram_symm (m n : ℤ) :
    thetaCdfCosineGram m n = thetaCdfCosineGram n m := by
  rw [thetaCdfCosineGram_eq_integral, thetaCdfCosineGram_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => mul_comm _ _

/-- Conductance normalization of the cosine Gram; index n denotes frequency n+1. -/
def thetaCdfParityTransition (m n : ℕ) : ℝ :=
  2 * thetaConductance (n + 1) * thetaCdfCosineGram (m + 1) (n + 1)

/-- The literal row-independent feedback distribution, fixed by unit capacity. -/
def thetaCdfBoundaryDistribution (n : ℕ) : ℝ :=
  2 * thetaConductance (n + 1) * cdfAction ((n + 1 : ℕ) : ℤ)

/-- The conductance-normalized transition has nonnegative entries. -/
theorem thetaCdfParityTransition_nonneg (m n : ℕ) :
    0 ≤ thetaCdfParityTransition m n := by
  exact mul_nonneg (mul_nonneg (by norm_num)
    (thetaConductance_pos (by omega)).le) (thetaCdfCosineGram_nonneg _ _)

/-- Every frequency has strictly positive boundary feedback weight. -/
theorem thetaCdfBoundaryDistribution_pos (n : ℕ) :
    0 < thetaCdfBoundaryDistribution n := by
  exact mul_pos (mul_pos (by norm_num) (thetaConductance_pos (by omega)))
    (cdfAction_pos (n := n + 1) (by omega))

/-- The boundary feedback has exactly unit total mass. -/
theorem hasSum_thetaCdfBoundaryDistribution : HasSum thetaCdfBoundaryDistribution 1 :=
  hasSum_theta_unitCapacity

/-- The full theta Green law gives unit mass in each transition row. -/
theorem hasSum_thetaCdfParityTransition (m : ℕ) :
    HasSum (thetaCdfParityTransition m) 1 := by
  have hm : ((m : ℤ) + 1) ≠ 0 := by omega
  have hg := hasSum_theta_green ((m : ℤ) + 1)
  simp only [hm, if_false, neg_zero] at hg
  have hs := hasSum_theta_unitCapacity.add hg
  convert hs using 1
  · funext n
    simp only [thetaCdfParityTransition, thetaCdfCosineGram]
    push_cast
    ring
  · norm_num

/-- The transition is reversible for the positive conductance weights. -/
theorem thetaCdfParityTransition_detailedBalance (m n : ℕ) :
    thetaConductance (m + 1) * thetaCdfParityTransition m n =
      thetaConductance (n + 1) * thetaCdfParityTransition n m := by
  rw [thetaCdfParityTransition, thetaCdfParityTransition, thetaCdfCosineGram_symm]
  ring

/-- The centered stochastic row is exactly the weighted quotient parity channel. -/
theorem thetaCdfParityTransition_sub_boundary (m n : ℕ) :
    thetaCdfParityTransition m n - thetaCdfBoundaryDistribution n =
      2 * Real.pi * (n + 1) * thetaConductance (n + 1) *
        (cdfQuotientMatrix (m + 1) (n + 1) -
          cdfQuotientMatrix (m + 1) (-(n + 1))) := by
  rw [cdfQuotientMatrix_parity_sub]
  unfold thetaCdfParityTransition thetaCdfBoundaryDistribution
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- All-frequency cancellation holds for the directed feedback, with convergent sums. -/
theorem hasSum_thetaCdfParityFeedback_zero (m : ℕ) :
    HasSum (fun n => thetaCdfParityTransition m n - thetaCdfBoundaryDistribution n) 0 := by
  simpa only [sub_self] using
    (hasSum_thetaCdfParityTransition m).sub hasSum_thetaCdfBoundaryDistribution

/-- The stochastic feedback is the actual even/odd source-operator matrix coefficient. -/
theorem thetaQuotient_even_odd_stochastic_feedback (m n : ℕ) :
    (Real.pi * (n + 1) * thetaConductance (n + 1) : ℂ) *
      inner ℂ (unitFourierBasis (m + 1) + unitFourierBasis (-(m + 1)))
        (thetaQuotientOperator
          (unitFourierBasis (n + 1) - unitFourierBasis (-(n + 1)))) =
      ((thetaCdfParityTransition m n - thetaCdfBoundaryDistribution n : ℝ) : ℂ) := by
  have hm : (m : ℤ) + 1 ≠ 0 := by omega
  have hn : (n : ℤ) + 1 ≠ 0 := by omega
  have h := thetaQuotient_fourier_parity_pairing hm hn 1 (-1)
  simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_one_smul,
    ← sub_eq_add_neg] at h
  rw [h, thetaCdfParityTransition_sub_boundary]
  push_cast
  ring

end
end RHTower
