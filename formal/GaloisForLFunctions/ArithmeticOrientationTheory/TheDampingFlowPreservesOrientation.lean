import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ResidueModesAndBackwardContinuation

/-!
# The damping flow preserves orientation

The centred damping operators `C_η` act on the residue modes `v_d` by the scalars `d^{−η}`
(`centeredOperator_normalizedResidueMode`).  A finite signed combination of residue modes,
`b = Σ_{d ∈ S} a_d v_d`, is therefore transported to `Σ_d a_d d^{−η} v_d`
(`centeredOperator_residueCombination`): the magnitudes decay, the **sign pattern** of the
coefficients is unchanged (`sign_coeff_centeredOperator`).

In the language of the field: on residue-mode combinations the damping flow is
orientation-preserving.  The damped Möbius source is the infinite combination with
coefficients `μ(d) d^{−η}`; its orientation is the Möbius sign pattern, transported exactly, and
the open question of the receiver is not where the orientation goes under the flow but whether
the magnitudes are square summable in the pronic norm.
-/

open Finset
open scoped ZeroAtInfty

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open BezoutValuationIncidence SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- A finite signed combination of residue modes. -/
def residueCombination (S : Finset ℕ) (a : ℕ → ℝ) : C₀(ℕ, ℝ) :=
  ∑ d ∈ S, a d • normalizedResidueMode d

/-- **Transport of a residue combination**: `C_η (Σ a_d v_d) = Σ a_d d^{−η} v_d`. -/
theorem centeredOperator_residueCombination {η : ℝ} (hη : 0 < η) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    arithmeticDampingCenteredOperator hη (residueCombination S a) =
      residueCombination S (fun d => a d * (d : ℝ) ^ (-η)) := by
  unfold residueCombination
  rw [map_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [map_smul, centeredOperator_normalizedResidueMode hη (hS d hd), smul_smul]

/-- **Orientation is preserved**: the transported coefficient has the sign of the original. -/
theorem sign_coeff_centeredOperator (η : ℝ) {d : ℕ} (hd : 0 < d) (a : ℝ) :
    Real.sign (a * (d : ℝ) ^ (-η)) = Real.sign a := by
  have hpos : 0 < (d : ℝ) ^ (-η) := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, Real.sign_of_neg (mul_neg_of_neg_of_pos ha hpos)]
  · rw [zero_mul]
  · rw [Real.sign_of_pos ha, Real.sign_of_pos (mul_pos ha hpos)]

/-- The transported coefficients are nonzero exactly where the original ones are. -/
theorem coeff_centeredOperator_ne_zero_iff (η : ℝ) {d : ℕ} (hd : 0 < d) (a : ℝ) :
    a * (d : ℝ) ^ (-η) ≠ 0 ↔ a ≠ 0 := by
  have hpos : (d : ℝ) ^ (-η) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hd) _).ne'
  simp [hpos]

/-- Iterating the flow multiplies the decay and keeps the orientation: the semigroup law on
residue combinations. -/
theorem centeredOperator_residueCombination_twice {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η')
    {S : Finset ℕ} (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    arithmeticDampingCenteredOperator hη
        (arithmeticDampingCenteredOperator hη' (residueCombination S a)) =
      residueCombination S (fun d => a d * (d : ℝ) ^ (-(η + η'))) := by
  rw [centeredOperator_residueCombination hη' hS, centeredOperator_residueCombination hη hS]
  unfold residueCombination
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hS d hd
  show (a d * (d : ℝ) ^ (-η') * (d : ℝ) ^ (-η)) • normalizedResidueMode d =
    (a d * (d : ℝ) ^ (-(η + η'))) • normalizedResidueMode d
  rw [mul_assoc, ← Real.rpow_add hd0, ← neg_add, add_comm]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
