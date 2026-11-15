import GaloisForLFunctions.HTGeometry.LinearAlgebra.PositiveMatrixForcing
import GaloisForLFunctions.SelbergClass.Primon.KestenFiniteGreen

/-!
# Correction heights for finite Kesten Green kernels

For every prime and every finite section, the Green response uniquely maximizes
the quadratic value forced by a signed charge. The error is exactly a sum of
positive squares: one boundary term and the causal differences of the response
error. This specializes finite negative-definite correction to the prime tree.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.SelbergClass.Primon
open GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Charge forcing minus the inverse Green energy of the candidate correction. -/
def kestenCorrectionValue (p : Nat.Primes) (n : ℕ) (b x : Fin (n + 1) → ℝ) : ℝ :=
  matrixForcedValue (kestenFiniteGreen p n)⁻¹ b x

/-- The loss from the maximal height is the inverse Green energy of the response error. -/
theorem kestenCorrectionValue_gap (p : Nat.Primes) (n : ℕ) (b x : Fin (n + 1) → ℝ) :
    b ⬝ᵥ (kestenFiniteGreen p n *ᵥ b) - kestenCorrectionValue p n b x =
      (x - kestenFiniteGreen p n *ᵥ b) ⬝ᵥ
        ((kestenFiniteGreen p n)⁻¹ *ᵥ (x - kestenFiniteGreen p n *ᵥ b)) := by
  have h := matrix_forced_value_gap (kestenFiniteGreen p n)⁻¹
    (posDef_kestenFiniteGreen_inverse p n) b x
  rwa [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_kestenFiniteGreen p n).isUnit)] at h

/-- The height loss splits into a boundary square and local causal-difference squares. -/
theorem kestenCorrectionValue_gap_causal (p : Nat.Primes) (n : ℕ)
    (b x : Fin (n + 1) → ℝ) :
    let e := x - kestenFiniteGreen p n *ᵥ b
    b ⬝ᵥ (kestenFiniteGreen p n *ᵥ b) - kestenCorrectionValue p n b x =
      (1 + primeReciprocal p) / primeReciprocal p * e 0 ^ 2 +
        (primeReciprocal p)⁻¹ * ∑ i : Fin n,
          (e i.succ - primeReciprocal p * e i.castSucc) ^ 2 := by
  rw [kestenCorrectionValue_gap, kestenFiniteGreen_inverse_energy]

/-- The Green energy of the charge bounds every forced quadratic value. -/
theorem kestenCorrectionValue_le (p : Nat.Primes) (n : ℕ) (b x : Fin (n + 1) → ℝ) :
    kestenCorrectionValue p n b x ≤ b ⬝ᵥ (kestenFiniteGreen p n *ᵥ b) := by
  have h := matrix_forced_value_le (kestenFiniteGreen p n)⁻¹
    (posDef_kestenFiniteGreen_inverse p n) b x
  rwa [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_kestenFiniteGreen p n).isUnit)] at h

/-- The Green response is the unique maximizing correction. -/
theorem kestenCorrectionValue_eq_iff (p : Nat.Primes) (n : ℕ) (b x : Fin (n + 1) → ℝ) :
    kestenCorrectionValue p n b x = b ⬝ᵥ (kestenFiniteGreen p n *ᵥ b) ↔
      x = kestenFiniteGreen p n *ᵥ b := by
  have h := matrix_forced_value_eq_iff (kestenFiniteGreen p n)⁻¹
    (posDef_kestenFiniteGreen_inverse p n) b x
  rwa [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_kestenFiniteGreen p n).isUnit)] at h

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenCorrectionValue_gap_causal
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenCorrectionValue_le
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenCorrectionValue_eq_iff
