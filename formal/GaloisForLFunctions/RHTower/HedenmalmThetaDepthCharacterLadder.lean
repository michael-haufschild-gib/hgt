import GaloisForLFunctions.RHTower.HedenmalmThetaSourceGlobalConormalCurrentSewing
import GaloisForLFunctions.RHTower.WeightMismatchRefutation
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Theta-source depth character criterion for the first RH ladder rung

The terminal conormal current of a fixed theta-source root block transforms under functional
equation reflection by `(-1)^(m-1)`, where `m` is exact Xi multiplicity.  Since `m` is positive,
this character is `-1` exactly when `m` is even.  Thus the base multiplicity rung is equivalent
to one explicit source-native sign law at every right-half divisor point.

This theorem isolates the missing arithmetic input.  Existing reflection and prime-modular
covariance compute the character but do not force its value.
-/

open Complex Set

namespace RHTower.HedenmalmThetaSource

noncomputable section

private theorem neg_one_pow_pred_eq_neg_one_iff_even {m : ℕ} (hm : 0 < m) :
    (-1 : ℂ) ^ (m - 1) = -1 ↔ Even m := by
  rw [neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)]
  constructor
  · intro hodd
    have h := hodd.add_one
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using h
  · intro heven
    exact Nat.Even.sub_odd (by omega : 1 ≤ m) heven odd_one

/-- The terminal theta reflection character is negative exactly at even-multiplicity Xi
divisor points. -/
theorem thetaDepthCharacter_eq_neg_one_iff_even_multiplicity
    (rho : XiDivisorSupport) :
    thetaDepthCharacter (thetaSpectrumOfXiSupport rho) = -1 ↔
      Even (xiSupportMultiplicity rho) := by
  rw [thetaDepthCharacter_at_XiSupport]
  exact neg_one_pow_pred_eq_neg_one_iff_even (xiSupportMultiplicity_pos rho)

/-- Exact fixed-source replacement for the report's proposed Kramers step: rung one holds iff
every right-half theta root current transforms with depth character `-1`. -/
theorem rhLadder_one_iff_thetaDepthCharacter_eq_neg_one_rightHalf :
    RHLadder 1 ↔ ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
      thetaDepthCharacter (thetaSpectrumOfXiSupport rho) = -1 := by
  rw [rhLadder_one_iff_even_order]
  constructor
  · intro h rho hright
    rw [thetaDepthCharacter_eq_neg_one_iff_even_multiplicity,
      xiSupportMultiplicity_eq_analyticOrderAt_toNat]
    exact h (rho : ℂ) (mem_rightHalf.mpr hright)
      (xi_eq_zero_of_mem_divisor_support rho)
  · intro h rho hright hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hs := (thetaDepthCharacter_eq_neg_one_iff_even_multiplicity support).mp
      (h support (mem_rightHalf.mp hright))
    simpa only [support, xiSupportMultiplicity_eq_analyticOrderAt_toNat] using hs

end

end RHTower.HedenmalmThetaSource
