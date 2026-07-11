/-
# The second Böttcher parameter velocity as a formal series

The second logarithmic parameter jet `B` of the Böttcher deformation satisfies the
triangular Mahler equation `B(t²) = 2·B(t) + 2t²·θA(t) − t⁴`, which exposes the Euler
derivative of the first jet through the dyadic substitution.  This module constructs `B`
by binary coefficient descent, proves the equation at the formal-series level, and pushes
both into the graded Mahler carrier.
-/
import Mathlib
import GaloisForLFunctions.U0.VelocityJetSeries
import GaloisForLFunctions.U0.MahlerHahnCarrier

namespace GaloisForLFunctions

open PowerSeries

noncomputable section

/-! ## The Euler operator on formal series -/

/-- The Euler operator `θ = t·d/dt` on formal power series. -/
def thetaSeries (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n : ℂ) * (coeff n) f

theorem coeff_thetaSeries (f : PowerSeries ℂ) (n : ℕ) :
    (coeff n) (thetaSeries f) = (n : ℂ) * (coeff n) f :=
  coeff_mk n _

open scoped Classical in
/-- The Euler jet of the velocity is the dyadic-power indicator series. -/
theorem coeff_thetaSeries_velocityJet (n : ℕ) :
    (coeff n) (thetaSeries velocityJet) = if IsDyadicPow n then 1 else 0 := by
  classical
  rw [coeff_thetaSeries, coeff_velocityJet, velocityCoeff]
  by_cases h : IsDyadicPow n
  · rw [if_pos h, if_pos h]
    have hn : (n : ℂ) ≠ 0 := by
      obtain ⟨j, rfl⟩ := h
      exact_mod_cast (Nat.two_pow_pos (j + 1)).ne'
    rw [mul_inv_cancel₀ hn]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ## The second velocity: coefficients by binary descent -/

/-- The inhomogeneous coefficient data of the second-jet Mahler equation. -/
def secondRhsCoeff (k : ℕ) : ℂ :=
  open scoped Classical in
  (if 2 ≤ k ∧ IsDyadicPow (k - 2) then 2 else 0) - (if k = 4 then 1 else 0)

/-- The coefficients of the second velocity, determined by descent along binary digits. -/
noncomputable def secondCoeff : ℕ → ℂ
  | 0 => 0
  | (k + 1) =>
    ((if 2 ∣ (k + 1) then secondCoeff ((k + 1) / 2) else 0) - secondRhsCoeff (k + 1)) / 2
decreasing_by exact Nat.div_lt_self (Nat.succ_pos k) one_lt_two

/-- The second velocity jet. -/
def secondJet : PowerSeries ℂ := PowerSeries.mk secondCoeff

theorem coeff_secondJet (n : ℕ) : (coeff n) secondJet = secondCoeff n :=
  coeff_mk n secondCoeff

/-- The defining descent identity of the second-jet coefficients. -/
theorem secondCoeff_key (k : ℕ) :
    (if 2 ∣ k then secondCoeff (k / 2) else 0) =
      2 * secondCoeff k + secondRhsCoeff k := by
  classical
  rcases k with _ | k
  · rw [if_pos ⟨0, rfl⟩]
    rw [show (0 : ℕ) / 2 = 0 from rfl]
    rw [show secondCoeff 0 = 0 from by simp [secondCoeff]]
    rw [show secondRhsCoeff 0 = 0 from by
      rw [secondRhsCoeff, if_neg (by omega), if_neg (by omega), sub_zero]]
    ring
  · rw [show secondCoeff (k + 1) =
      ((if 2 ∣ (k + 1) then secondCoeff ((k + 1) / 2) else 0) -
        secondRhsCoeff (k + 1)) / 2 from by rw [secondCoeff]]
    ring_nf

/-- **The triangular second-velocity Mahler equation**:
`B(t²) = 2·B + 2·t²·θA − t⁴`. -/
theorem dyadicSubst_secondJet :
    dyadicSubst secondJet =
      2 * secondJet + 2 * (X ^ 2 * thetaSeries velocityJet) - X ^ 4 := by
  classical
  ext k
  rw [map_sub, two_mul secondJet, two_mul (X ^ 2 * thetaSeries velocityJet), map_add,
    map_add, map_add, coeff_secondJet, coeff_X_pow]
  rw [show (coeff k) (dyadicSubst secondJet) =
    (if 2 ∣ k then (coeff (k / 2)) secondJet else 0) from by
    rw [dyadicSubst, coeff_mk]]
  rw [coeff_secondJet]
  have hs : (coeff k) (X ^ 2 * thetaSeries velocityJet) =
      if 2 ≤ k ∧ IsDyadicPow (k - 2) then 1 else 0 := by
    rw [mul_comm, coeff_mul_X_pow', coeff_thetaSeries_velocityJet]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2]
      by_cases hd : IsDyadicPow (k - 2)
      · rw [if_pos hd, if_pos ⟨h2, hd⟩]
      · rw [if_neg hd, if_neg (fun hc => hd hc.2)]
    · rw [if_neg h2, if_neg (fun hc => h2 hc.1)]
  rw [hs, secondCoeff_key k]
  rw [show secondRhsCoeff k = (if 2 ≤ k ∧ IsDyadicPow (k - 2) then 2 else 0) -
    (if k = 4 then 1 else 0) from by rw [secondRhsCoeff]]
  split_ifs <;> ring

/-! ## The second velocity inside the graded carrier -/

theorem eulerDeriv_toMahlerCarrier (f : PowerSeries ℂ) :
    eulerDeriv (toMahlerCarrier f) = toMahlerCarrier (thetaSeries f) := by
  classical
  ext q
  by_cases hq : ∃ n : ℕ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [eulerDeriv_coeff, toMahlerCarrier_coeff_natCast, toMahlerCarrier_coeff_natCast,
      coeff_thetaSeries, map_mul, map_natCast, map_natCast]
  · push Not at hq
    rw [eulerDeriv_coeff, toMahlerCarrier_coeff_of_ne f hq,
      toMahlerCarrier_coeff_of_ne _ hq, mul_zero]

theorem toMahlerCarrier_X_sq :
    toMahlerCarrier (X ^ 2 : PowerSeries ℂ) = mahlerT * mahlerT := by
  rw [sq, map_mul, toMahlerCarrier_X]

/-- **The second velocity's Mahler equation in the carrier**:
`σ(B) = 2·B + 2·t²·θ(A) − t⁴`. -/
theorem mahlerSigma_secondJet :
    mahlerSigma (toMahlerCarrier secondJet) =
      2 * toMahlerCarrier secondJet +
        2 * ((mahlerT * mahlerT) * eulerDeriv (toMahlerCarrier velocityJet)) -
        (mahlerT * mahlerT) * (mahlerT * mahlerT) := by
  rw [mahlerSigma_toMahlerCarrier, dyadicSubst_secondJet, map_sub, map_add]
  congr 1
  · congr 1
    · rw [show (2 : PowerSeries ℂ) * secondJet = secondJet + secondJet from two_mul _,
        map_add, two_mul]
    · rw [show (2 : PowerSeries ℂ) * (X ^ 2 * thetaSeries velocityJet) =
        X ^ 2 * thetaSeries velocityJet + X ^ 2 * thetaSeries velocityJet from two_mul _,
        map_add, two_mul]
      congr 1 <;>
      · rw [map_mul, toMahlerCarrier_X_sq, eulerDeriv_toMahlerCarrier]
  · rw [show (X ^ 4 : PowerSeries ℂ) = X ^ 2 * X ^ 2 from by ring, map_mul,
      toMahlerCarrier_X_sq]

end

end GaloisForLFunctions
