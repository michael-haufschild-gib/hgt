/-
# The third Böttcher parameter velocity as a formal series

The third logarithmic parameter jet `C` of the normalized Böttcher deformation obeys

`C(t²) = 2C(t) + 3t² θB(t) + 3t⁴ θA(t) + (3/2)t⁴ θ²A(t) - 2t⁶`.

This module constructs the uniquely normalized formal solution by binary coefficient descent and
proves the exact mixed parameter--spatial jet relation.
-/
import GaloisForLFunctions.U0.SecondVelocityJet

namespace GaloisForLFunctions

open PowerSeries

noncomputable section

/-- The lower-jet value in the third parameter-jet Mahler equation. -/
def thirdJetRhs : PowerSeries ℂ :=
  3 * (X ^ (2 : ℕ) * thetaSeries secondJet) +
    3 * (X ^ (4 : ℕ) * thetaSeries velocityJet) +
    (3 / 2 : ℂ) • (X ^ (4 : ℕ) * thetaSeries (thetaSeries velocityJet)) -
    2 * X ^ (6 : ℕ)

/-- Coefficients of the normalized third parameter jet, determined by binary descent. -/
noncomputable def thirdCoeff : ℕ → ℂ
  | 0 => 0
  | (k + 1) =>
    ((if 2 ∣ (k + 1) then thirdCoeff ((k + 1) / 2) else 0) -
      (coeff (k + 1)) thirdJetRhs) / 2
decreasing_by exact Nat.div_lt_self (Nat.succ_pos k) one_lt_two

/-- The third logarithmic Böttcher parameter jet. -/
def thirdJet : PowerSeries ℂ := PowerSeries.mk thirdCoeff

theorem coeff_thirdJet (n : ℕ) : (coeff n) thirdJet = thirdCoeff n :=
  coeff_mk n thirdCoeff

/-- The coefficient descent identity defining the third jet. -/
theorem thirdCoeff_key (k : ℕ) :
    (if 2 ∣ k then thirdCoeff (k / 2) else 0) =
      2 * thirdCoeff k + (coeff k) thirdJetRhs := by
  classical
  rcases k with _ | k
  · rw [if_pos ⟨0, rfl⟩]
    simp [thirdCoeff, thirdJetRhs]
  · rw [show thirdCoeff (k + 1) =
      ((if 2 ∣ (k + 1) then thirdCoeff ((k + 1) / 2) else 0) -
        (coeff (k + 1)) thirdJetRhs) / 2 from by rw [thirdCoeff]]
    ring_nf

/-- The third jet's triangular mixed-jet equation in compressed form. -/
theorem dyadicSubst_thirdJet :
    dyadicSubst thirdJet = 2 * thirdJet + thirdJetRhs := by
  classical
  ext k
  rw [show (coeff k) (dyadicSubst thirdJet) =
    (if 2 ∣ k then (coeff (k / 2)) thirdJet else 0) from by
      rw [dyadicSubst, coeff_mk]]
  rw [coeff_thirdJet]
  rw [show 2 * thirdJet = thirdJet + thirdJet from two_mul _]
  rw [map_add, map_add, coeff_thirdJet]
  simpa [two_mul] using thirdCoeff_key k

/-- **Third Böttcher parameter--spatial jet law.** The dyadic transform of the third
logarithmic parameter jet exposes the Euler derivative of the second jet and the first two Euler
derivatives of the first jet with exact coefficients. -/
theorem dyadicSubst_thirdJet_explicit :
    dyadicSubst thirdJet =
      2 * thirdJet + 3 * (X ^ (2 : ℕ) * thetaSeries secondJet) +
        3 * (X ^ (4 : ℕ) * thetaSeries velocityJet) +
        (3 / 2 : ℂ) • (X ^ (4 : ℕ) * thetaSeries (thetaSeries velocityJet)) -
        2 * X ^ (6 : ℕ) := by
  rw [dyadicSubst_thirdJet, thirdJetRhs]
  abel

end

end GaloisForLFunctions
