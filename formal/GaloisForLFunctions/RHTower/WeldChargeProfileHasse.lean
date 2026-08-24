import GaloisForLFunctions.RHTower.WeldChargeFaithfulness

/-!
# Hasse reconstruction from the two-power weld-charge tower

An integer deck index is determined by its residues at every two-power depth.  This file packages
that profinite faithfulness as a Hasse principle: simultaneous local congruence reconstructs the
global integer, global zero is detected locally, and distinct indices separate at a finite depth.

The result supplies an exact local-to-global interface for any route carrying an integer winding,
vanishing-order, or deck-charge index.  It does not identify such an index with an RH source term.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Complete tower of two-power deck charges of an integer index. -/
def twoPowerWChargeProfile (idx : ℤ) : (k : ℕ) → ZMod (2 ^ k) :=
  fun k ↦ _root_.RHTower.wCharge (2 ^ k) idx

@[simp]
theorem twoPowerWChargeProfile_apply (idx : ℤ) (k : ℕ) :
    twoPowerWChargeProfile idx k = _root_.RHTower.wCharge (2 ^ k) idx := rfl

/-- Simultaneous two-power deck charge is faithful. -/
theorem twoPowerWChargeProfile_injective :
    Function.Injective twoPowerWChargeProfile := by
  intro i j h
  apply wCharge_two_pow_profile_injective
  change (fun k : ℕ => _root_.RHTower.wCharge (2 ^ k) i) =
    (fun k : ℕ => _root_.RHTower.wCharge (2 ^ k) j) at h
  exact h

/-- Integer indices are equivalent to the two-power charge profiles they realize. -/
noncomputable def twoPowerWChargeProfileEquivRange :
    ℤ ≃ Set.range twoPowerWChargeProfile :=
  Equiv.ofInjective twoPowerWChargeProfile twoPowerWChargeProfile_injective

@[simp]
theorem twoPowerWChargeProfileEquivRange_apply (idx : ℤ) :
    (twoPowerWChargeProfileEquivRange idx : (k : ℕ) → ZMod (2 ^ k)) =
      twoPowerWChargeProfile idx := rfl

/-- Two integer indices agree exactly when all their two-power local charges agree. -/
theorem int_congr_twoPowerWCharge_hasse_iff (i j : ℤ) :
    i = j ↔ ∀ k : ℕ,
      _root_.RHTower.wCharge (2 ^ k) i = _root_.RHTower.wCharge (2 ^ k) j := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact twoPowerWChargeProfile_injective (funext h)

/-- Vanishing at every two-power local charge detects the zero integer index. -/
theorem int_eq_zero_twoPowerWCharge_hasse_iff (i : ℤ) :
    i = 0 ↔ ∀ k : ℕ, _root_.RHTower.wCharge (2 ^ k) i = 0 := by
  constructor
  · rintro rfl
    intro k
    simp
  · intro h
    exact (int_congr_twoPowerWCharge_hasse_iff i 0).2 (by simpa using h)

/-- Distinct integer indices are separated at one finite two-power depth. -/
theorem exists_twoPowerWCharge_ne_of_int_ne {i j : ℤ} (hij : i ≠ j) :
    ∃ k : ℕ,
      _root_.RHTower.wCharge (2 ^ k) i ≠ _root_.RHTower.wCharge (2 ^ k) j := by
  by_contra h
  push Not at h
  exact hij ((int_congr_twoPowerWCharge_hasse_iff i j).2 h)

end GaloisForLFunctions.RHTower
