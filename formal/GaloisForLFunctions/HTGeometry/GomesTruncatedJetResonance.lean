import GaloisForLFunctions.HTGeometry.GomesTruncatedJetClockCovariance
import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact resonance selection by existing geometric jet clocks

The additional diagonal structure retains exactly those finite clock-symbol
coefficients whose phase power is one. No phase invertibility or periodicity
is assumed; the zero and nonperiodic cases remain part of the same statement.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Commutation with the actual geometric jet clock is exactly coefficientwise phase resonance. -/
theorem gomesTruncatedJetClock_formal_commute_iff (n : ℕ) (z : ℂ) (F : PowerSeries ℂ) :
    Commute (gomesFiniteFockFormalHom (n + 1) F) (RHTower.truncatedJetClock n z) ↔
      ∀ k : Fin (n + 1), PowerSeries.coeff k.val F = 0 ∨ z ^ k.val = 1 := by
  constructor
  · intro h k
    have he := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M 0 k) h.eq
    simp only [RHTower.truncatedJetClock, Matrix.mul_diagonal, Matrix.diagonal_mul,
      gomesFiniteFockFormalHom_apply, Fin.val_zero, Nat.sub_zero, pow_zero, one_mul] at he
    simp only [if_pos (Nat.zero_le k.val)] at he
    have hm : PowerSeries.coeff k.val F * (z ^ k.val - 1) = 0 := by
      rw [mul_sub, mul_one, he, sub_self]
    exact (mul_eq_zero.mp hm).imp_right sub_eq_zero.mp
  · intro h
    change gomesFiniteFockFormalHom (n + 1) F * RHTower.truncatedJetClock n z =
      RHTower.truncatedJetClock n z * gomesFiniteFockFormalHom (n + 1) F
    ext i j
    simp only [RHTower.truncatedJetClock, Matrix.mul_diagonal, Matrix.diagonal_mul,
      gomesFiniteFockFormalHom_apply]
    by_cases hij : i.val ≤ j.val
    · rw [if_pos hij]
      rcases h ⟨j.val - i.val, (Nat.sub_le _ _).trans_lt j.isLt⟩ with hc | hz
      · rw [hc, zero_mul, mul_zero]
      · have hp : z ^ j.val = z ^ i.val := by
          calc
            z ^ j.val = z ^ (i.val + (j.val - i.val)) := by rw [Nat.add_sub_of_le hij]
            _ = z ^ i.val * z ^ (j.val - i.val) := pow_add _ _ _
            _ = z ^ i.val := by rw [hz, mul_one]
        rw [hp]
        exact mul_comm _ _
    · rw [if_neg hij, zero_mul, mul_zero]

/-- The phase-order divisibility law is valid even when the phase has order zero. -/
theorem gomesTruncatedJetClock_formal_commute_iff_order (n : ℕ) (z : ℂ) (F : PowerSeries ℂ) :
    Commute (gomesFiniteFockFormalHom (n + 1) F) (RHTower.truncatedJetClock n z) ↔
      ∀ k : Fin (n + 1), PowerSeries.coeff k.val F = 0 ∨ orderOf z ∣ k.val := by
  simp only [gomesTruncatedJetClock_formal_commute_iff, orderOf_dvd_iff_pow_eq_one]

/-- The same exact resonance criterion applies to the corpus's existing finite polynomial symbols. -/
theorem gomesTruncatedJetClock_polynomial_commute_iff (n : ℕ) (z : ℂ) (p : Polynomial ℂ) :
    Commute (gomesFiniteFockPolynomialHom (n + 1) p) (RHTower.truncatedJetClock n z) ↔
      ∀ k : Fin (n + 1), p.coeff k.val = 0 ∨ orderOf z ∣ k.val := by
  rw [← gomesFiniteFockFormalHom_coe, gomesTruncatedJetClock_formal_commute_iff_order]
  simp only [Polynomial.coeff_coe]

/-- The finite order power of the actual derivative clock always survives the geometric phase structure. -/
theorem gomesTruncatedJetClock_orderPower_commute (n : ℕ) (z : ℂ) :
    Commute (fockShiftMatrix (n + 1) ^ orderOf z) (RHTower.truncatedJetClock n z) := by
  rw [← gomesFiniteFockFormalHom_X, ← map_pow]
  apply (gomesTruncatedJetClock_formal_commute_iff n z _).mpr
  intro k
  rw [PowerSeries.coeff_X_pow]
  by_cases hk : k.val = orderOf z
  · exact Or.inr (hk ▸ pow_orderOf_eq_one z)
  · exact Or.inl (if_neg hk)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
