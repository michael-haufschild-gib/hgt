import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.CommutatorGreen
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss

/-!
# Finite-width Bohr frequency filters

The Green response obeys an exact Hilbert--Schmidt sum rule. Moving
vertically off the real axis turns the pole coefficient into a
contractive frequency filter whose squared error is a Lorentzian sum
over the other Bohr frequencies.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- Parseval's identity in the orthonormal energy basis. -/
theorem hsSqRe_eq_sum_energyCoordinates (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    hsSqRe X = ∑ i, ∑ j, ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 := by
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  let E := hamiltonianEnergyCoordinates hH
  have he : hsSqRe (E X) = hsSqRe X := by
    unfold hsSqRe
    rw [← Matrix.star_eq_conjTranspose (E X), ← Matrix.star_eq_conjTranspose X,
      ← map_star, ← map_mul]
    change ((star U * (star X * X) * U).trace).re = _
    rw [Matrix.trace_mul_comm (star U * (star X * X)) U, ← Matrix.mul_assoc,
      show U * star U = 1 from Unitary.coe_mul_star_self hH.eigenvectorUnitary, Matrix.one_mul]
  rw [← he, hsSqRe_eq_sum, Finset.sum_comm]

/-- The shell Green-norm identity on the energy transitions of an actual
finite Hamiltonian commutator. -/
theorem hsSqRe_hamiltonianCommutatorGreen (hH : H.IsHermitian) (z : ℂ) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianCommutatorGreen hH z X) =
      ∑ i, ∑ j, ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 /
        ‖(hamiltonianGap hH i j : ℂ) - z‖ ^ 2 := by
  rw [hsSqRe_eq_sum_energyCoordinates hH]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [energyCoordinates_commutatorGreen_apply, norm_mul, norm_inv, mul_pow, inv_pow,
    div_eq_mul_inv, mul_comm]

/-- Filter centered at a real frequency, with positive damping width. -/
def hamiltonianDampedGapResponse (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ))
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  let z : ℂ := ⟨μ, (ε : ℝ)⟩
  ((μ : ℂ) - z) • hamiltonianCommutatorGreen hH z X

theorem energyCoordinates_dampedGapResponse_apply
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X) i j =
      ((μ : ℂ) - ⟨μ, (ε : ℝ)⟩) *
        (((hamiltonianGap hH i j : ℂ) - ⟨μ, (ε : ℝ)⟩)⁻¹ *
          hamiltonianEnergyCoordinates hH X i j) := by
  simp only [hamiltonianDampedGapResponse, map_smul, Matrix.smul_apply, smul_eq_mul,
    energyCoordinates_commutatorGreen_apply]

private theorem norm_sq_real_sub_dampedFrequency (r μ ε : ℝ) :
    ‖(r : ℂ) - ⟨μ, ε⟩‖ ^ 2 = (r - μ) ^ 2 + ε ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  change (r - μ) * (r - μ) + (0 - ε) * (0 - ε) = _
  ring

private theorem norm_sq_energyCoordinates_dampedGapResponse_apply
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) (i j : ι) :
    ‖hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X) i j‖ ^ 2 =
      (ε : ℝ) ^ 2 * ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 /
        ((hamiltonianGap hH i j - μ) ^ 2 + (ε : ℝ) ^ 2) := by
  rw [energyCoordinates_dampedGapResponse_apply]
  simp only [norm_mul, norm_inv, mul_pow, inv_pow, norm_sq_real_sub_dampedFrequency]
  rw [sub_self, zero_pow two_ne_zero, zero_add, div_eq_mul_inv]
  ring

/-- Each energy transition is attenuated by a factor of modulus at most
one. The bound holds even when the filtered frequency is degenerate. -/
theorem hsSqRe_hamiltonianDampedGapResponse_le
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianDampedGapResponse hH μ ε X) ≤ hsSqRe X := by
  rw [hsSqRe_eq_sum_energyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X),
    hsSqRe_eq_sum_energyCoordinates hH X]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [norm_sq_energyCoordinates_dampedGapResponse_apply]
  have hpos : 0 < (hamiltonianGap hH i j - μ) ^ 2 + (ε : ℝ) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ε.2.ne')
  apply (div_le_iff₀ hpos).mpr
  let w := ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2
  calc
    _ ≤ w * (hamiltonianGap hH i j - μ) ^ 2 + (ε : ℝ) ^ 2 * w :=
      le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by dsimp only [w]; ring

/-- The error separates exactly into the nonresonant Bohr frequencies. -/
theorem hsSqRe_hamiltonianDampedGapResponse_sub
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianDampedGapResponse hH μ ε X - hamiltonianGapComponent hH μ X) =
      ∑ i, ∑ j, if hamiltonianGap hH i j = μ then 0 else
        (ε : ℝ) ^ 2 * ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 /
          ((hamiltonianGap hH i j - μ) ^ 2 + (ε : ℝ) ^ 2) := by
  rw [hsSqRe_eq_sum_energyCoordinates hH]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, Matrix.sub_apply, energyCoordinates_gapComponent_apply]
  by_cases hg : hamiltonianGap hH i j = μ
  · have hn : (μ : ℂ) - ⟨μ, (ε : ℝ)⟩ ≠ 0 := by
      intro he
      have him := congrArg Complex.im he
      change 0 - (ε : ℝ) = 0 at him
      rw [zero_sub, neg_eq_zero] at him
      exact (show 0 < (ε : ℝ) from ε.2).ne' him
    rw [energyCoordinates_dampedGapResponse_apply, if_pos hg, if_pos hg, hg,
      mul_inv_cancel_left₀ hn, sub_self, norm_zero]
    exact zero_pow two_ne_zero
  · rw [if_neg hg, if_neg hg, sub_zero, norm_sq_energyCoordinates_dampedGapResponse_apply]

/-- A quadratic bound in damping width, with the inverse squared
frequency distances of the nonresonant forcing as its coefficient. -/
theorem hsSqRe_hamiltonianDampedGapResponse_sub_le
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianDampedGapResponse hH μ ε X - hamiltonianGapComponent hH μ X) ≤
      (ε : ℝ) ^ 2 * ∑ i, ∑ j, if hamiltonianGap hH i j = μ then 0 else
        ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 / (hamiltonianGap hH i j - μ) ^ 2 := by
  rw [hsSqRe_hamiltonianDampedGapResponse_sub, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hg : hamiltonianGap hH i j = μ
  · simp only [hg, if_true, mul_zero, le_refl]
  · rw [if_neg hg, if_neg hg, ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hg)) (le_add_of_nonneg_right (sq_nonneg _))

#print axioms hsSqRe_hamiltonianCommutatorGreen
#print axioms hsSqRe_hamiltonianDampedGapResponse_le
#print axioms hsSqRe_hamiltonianDampedGapResponse_sub
#print axioms hsSqRe_hamiltonianDampedGapResponse_sub_le

end

end GaloisForLFunctions.HTGeometry
