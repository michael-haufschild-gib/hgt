import GaloisForLFunctions.RHTower.MobiusReciprocalBalancedCore
import GaloisForLFunctions.RHTower.MobiusReciprocalGammaHankelBridge

/-!
# Identifying the balanced source with the reciprocal Gamma--Hankel moment

The exact balanced-only finite decomposition applies to the same quadratic
form used by the source-order comparison and the RH Gamma--Hankel endpoint.
-/

open Finset
namespace RHTower
noncomputable section

/-- The literal pair-product energy is exactly the coupled-order reciprocal moment. -/
theorem finiteGeneralReciprocalEnergy_three_add_delta_eq_coupledFull
    (δ : ℝ) (N : ℕ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      coupledReciprocalFullEnergy δ N := by
  unfold finiteGeneralReciprocalEnergy coupledReciprocalFullEnergy
  let S := Finset.Icc 1 N
  change (∑ m ∈ S, ∑ n ∈ S,
      mobiusRealCoefficient m * mobiusRealCoefficient n *
        generalReciprocalMomentKernel (3 + δ) δ m n) =
    ∑ nm ∈ S.product S, coupledReciprocalSignedAtom δ nm.2 nm.1
  calc
    _ = ∑ m ∈ S, ∑ n ∈ S, coupledReciprocalSignedAtom δ n m := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [generalReciprocalMomentKernel_three_add_delta]
      unfold coupledReciprocalSignedAtom
      rw [show (n : ℝ) + m = (m : ℝ) + n by ring]
      ring
    _ = _ := (Finset.sum_product S S
      (fun nm : ℕ × ℕ => coupledReciprocalSignedAtom δ nm.2 nm.1)).symm

/-- Exact finite reduction of the RH-scale coupled source to power-balanced pairs. -/
theorem finiteGeneralReciprocalEnergy_three_add_delta_eq_balanced
    (δ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      coupledReciprocalBalancedEnergy δ N +
        2 * unbalancedReciprocalSignedEnergy δ N -
          (2 : ℝ) ^ (-(5 + δ)) := by
  rw [finiteGeneralReciprocalEnergy_three_add_delta_eq_coupledFull]
  exact coupledReciprocalFullEnergy_eq_balanced_add_two_unbalanced δ N hN

end
end RHTower
