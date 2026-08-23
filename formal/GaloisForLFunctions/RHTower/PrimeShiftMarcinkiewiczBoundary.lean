import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability

/-!
# Marcinkiewicz boundary of normalized prime-shift characters

The normalized prime character has exactly the unit Euler tail on the critical
line, while every strict right-half-plane character lies in the vanishing-tail
layer.  These are the rigorous finite-tail components of the logarithmic
Marcinkiewicz trichotomy.
-/

noncomputable section

namespace RHTower

open Finset Complex

/-- On the critical line, every prime coefficient of the normalized shift
character has absolute value one. -/
theorem absField_primeShiftCharacter_eq_one_on_primes
    (z : ℂ) (hz : z.re = 1 / 2) {n : ℕ} (hn : n.Prime) :
    absField (primeShiftCharacter z) n = 1 := by
  rw [absField, primeShiftCharacter, if_pos hn,
    Complex.norm_natCast_cpow_of_pos hn.pos]
  have hzero : ((1 : ℂ) / 2 - z).re = 0 := by
    simp [hz]
  rw [hzero, Real.rpow_zero]

/-- A critical-line normalized prime character and the unit field have equal
Marcinkiewicz mass at every cutoff. -/
theorem primeLogMass_absField_primeShiftCharacter_eq_unit
    (z : ℂ) (hz : z.re = 1 / 2) (X : ℕ) :
    primeLogMass (absField (primeShiftCharacter z)) X =
      primeLogMass (fun _ => (1 : ℝ)) X := by
  unfold primeLogMass
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [absField_primeShiftCharacter_eq_one_on_primes z hz hn.2]

/-- A critical-line normalized prime character and the unit field have equal
Marcinkiewicz tail mass after every finite cutoff. -/
theorem primeLogMass_tail_absField_primeShiftCharacter_eq_unit
    (z : ℂ) (hz : z.re = 1 / 2) (P X : ℕ) :
    primeLogMass (primeCoefficientTail (absField (primeShiftCharacter z)) P) X =
      primeLogMass (primeCoefficientTail (fun _ => (1 : ℝ)) P) X := by
  rw [primeLogMass_tail, primeLogMass_tail]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [absField_primeShiftCharacter_eq_one_on_primes z hz hn.2.1]

/-- Critical-line normalized prime characters lie in the logarithmic
Marcinkiewicz layer. -/
theorem memMarcinkiewiczLogLayer_absField_primeShiftCharacter_of_re_eq_half
    (z : ℂ) (hz : z.re = 1 / 2) :
    MemMarcinkiewiczLogLayer (absField (primeShiftCharacter z)) := by
  obtain ⟨C, hC⟩ := unitField_memMarcinkiewiczLogLayer
  refine ⟨C, fun X hX => ?_⟩
  unfold marcinkiewiczLogQuotient
  rw [primeLogMass_absField_primeShiftCharacter_eq_unit z hz]
  exact hC X hX

/-- Critical-line normalized prime characters do not have vanishing
Marcinkiewicz tails. -/
theorem not_memVanishingTailLayer_absField_primeShiftCharacter_of_re_eq_half
    (z : ℂ) (hz : z.re = 1 / 2) :
    ¬ MemVanishingTailLayer (absField (primeShiftCharacter z)) := by
  intro h
  apply unitField_not_memVanishingTailLayer
  intro ε hε
  obtain ⟨P, hP⟩ := h ε hε
  refine ⟨P, fun X hX => ?_⟩
  unfold marcinkiewiczLogQuotient at hP ⊢
  rw [← primeLogMass_tail_absField_primeShiftCharacter_eq_unit z hz P X]
  exact hP X hX

/-- Strict right-half-plane normalized prime characters have vanishing
Marcinkiewicz tails. -/
theorem memVanishingTailLayer_absField_primeShiftCharacter_of_half_lt_re
    {z : ℂ} (hz : 1 / 2 < z.re) :
    MemVanishingTailLayer (absField (primeShiftCharacter z)) :=
  memVanishingTailLayer_of_memCriticalSummableLayer
    (memCriticalSummableLayer_absField_primeShiftCharacter hz)

end RHTower

end
