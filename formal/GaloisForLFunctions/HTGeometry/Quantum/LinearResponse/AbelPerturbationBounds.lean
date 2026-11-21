import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelResponsePerturbation
import GaloisForLFunctions.HTGeometry.CommutatorOperatorBound

/-!
# Quantitative Abel linearization

Cauchy–Schwarz bounds commutator forcing by its Hilbert–Schmidt
energy. Contractivity bounds the error after one or two applications
of the perturbation forcing.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] {H K : Matrix ι ι ℂ}

private theorem mulVec_energy_le_hsSqRe (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    (∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ hsSqRe A * ∑ j, ‖v j‖ ^ 2 := by
  rw [hsSqRe_eq_sum, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have htri : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simpa only [Matrix.mulVec, dotProduct, norm_mul] using
      (norm_sum_le Finset.univ (fun j => A i j * v j))
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖v j‖))

/-- The unconditional Hilbert–Schmidt commutator bound. -/
theorem hsSqRe_commutator_le_hsSqRe (T A : Matrix ι ι ℂ) :
    hsSqRe (T * A - A * T) ≤ (4 * hsSqRe T) * hsSqRe A := by
  let c := Real.sqrt (hsSqRe T)
  have hc : c ^ 2 = hsSqRe T := Real.sq_sqrt (hsSqRe_nonneg T)
  have hT (v : ι → ℂ) : (∑ i, ‖(T *ᵥ v) i‖ ^ 2) ≤ c ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    rw [hc]
    exact mulVec_energy_le_hsSqRe T v
  have hTH (v : ι → ℂ) : (∑ i, ‖(Tᴴ *ᵥ v) i‖ ^ 2) ≤ c ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    rw [hc, ← hsSqRe_conjTranspose T]
    exact mulVec_energy_le_hsSqRe Tᴴ v
  calc
    _ ≤ (2 * c) ^ 2 * hsSqRe A := hsSqRe_commutator_le_of_opBound T A hT hTH
    _ = _ := by rw [mul_pow, hc]; ring

/-- Hilbert–Schmidt energy scales by the squared modulus. -/
theorem hsSqRe_complex_smul (s : ℂ) (X : Matrix ι ι ℂ) :
    hsSqRe (s • X) = ‖s‖ ^ 2 * hsSqRe X := by
  simp only [hsSqRe_eq_sum, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

private theorem norm_hamiltonianAbelShift (ε : Ioi (0 : ℝ)) :
    ‖hamiltonianAbelShift ε‖ = (ε : ℝ) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  change √(0 * 0 + (ε : ℝ) * (ε : ℝ)) = _
  rw [zero_mul, zero_add, ← pow_two, Real.sqrt_sq ε.2.le]

variable [DecidableEq ι]

theorem hsSqRe_abelPerturbationForcing_le (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (T X : Matrix ι ι ℂ) :
    hsSqRe (abelPerturbationForcing hH ε T X) ≤
      (4 * hsSqRe T / (ε : ℝ) ^ 2) * hsSqRe X := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  rw [abelPerturbationForcing, hsSqRe_complex_smul, norm_inv, norm_hamiltonianAbelShift, inv_pow]
  change ((ε : ℝ) ^ 2)⁻¹ * hsSqRe (T * Y - Y * T) ≤ _
  calc
    _ ≤ ((ε : ℝ) ^ 2)⁻¹ * ((4 * hsSqRe T) * hsSqRe Y) :=
      mul_le_mul_of_nonneg_left (hsSqRe_commutator_le_hsSqRe T Y)
        (inv_nonneg.mpr (sq_nonneg (ε : ℝ)))
    _ = (4 * hsSqRe T / (ε : ℝ) ^ 2) * hsSqRe Y := by rw [div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsSqRe_hamiltonianDampedGapResponse_le hH 0 ε X)
      (div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ)))

/-- The response is Lipschitz in the Hamiltonian, with constant controlled
by the inverse damping width. -/
theorem hsSqRe_abelResponse_sub_le (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianDampedGapResponse hK 0 ε X -
      hamiltonianDampedGapResponse hH 0 ε X) ≤
      (4 * hsSqRe (K - H) / (ε : ℝ) ^ 2) * hsSqRe X := by
  rw [abelResponse_sub hH hK ε X]
  exact (hsSqRe_hamiltonianDampedGapResponse_le hK 0 ε _).trans
    (hsSqRe_abelPerturbationForcing_le hH ε (K - H) X)

/-- The squared error after subtracting the first variation is fourth
order in the Hilbert–Schmidt norm of the perturbation. -/
theorem hsSqRe_abelResponse_sub_variation_le (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hsSqRe (hamiltonianDampedGapResponse hK 0 ε X -
      hamiltonianDampedGapResponse hH 0 ε X - abelResponseVariation hH ε (K - H) X) ≤
      (4 * hsSqRe (K - H) / (ε : ℝ) ^ 2) ^ 2 * hsSqRe X := by
  let T := K - H
  let Y := abelPerturbationForcing hH ε T X
  let b := 4 * hsSqRe T / (ε : ℝ) ^ 2
  have hb : 0 ≤ b :=
    div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ))
  rw [abelResponse_sub_variation hH hK ε X]
  calc
    _ ≤ hsSqRe (abelPerturbationForcing hH ε T Y) :=
      hsSqRe_hamiltonianDampedGapResponse_le hK 0 ε _
    _ ≤ b * hsSqRe Y := hsSqRe_abelPerturbationForcing_le hH ε T Y
    _ ≤ b * (b * hsSqRe X) :=
      mul_le_mul_of_nonneg_left (hsSqRe_abelPerturbationForcing_le hH ε T X) hb
    _ = _ := by change b * (b * hsSqRe X) = b ^ 2 * hsSqRe X; rw [pow_two, mul_assoc]

#print axioms hsSqRe_commutator_le_hsSqRe
#print axioms hsSqRe_abelResponse_sub_le
#print axioms hsSqRe_abelResponse_sub_variation_le

end

end GaloisForLFunctions.HTGeometry
