import GaloisForLFunctions.RHTower.MertensPrimeSqrtWindow
import GaloisForLFunctions.RHTower.PrimeShiftCharacterBasic

/-!
# Left Marcinkiewicz boundary of normalized prime-shift characters

The explicit Mertens square-root window forces every normalized shift with
real part below one half to have unbounded logarithmic Marcinkiewicz mass.
Together with the critical-line and right-half-plane results, this supplies
the complete pointwise trichotomy for a single normalized prime shift.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

/-- On prime coordinates, the absolute normalized shift is the real prime
power with exponent `1 / 2 - Re z`. -/
theorem primeLogMass_absField_primeShiftCharacter_eq_rpow (z : ℂ) (X : ℕ) :
    primeLogMass_weightedEulerCoefficientSpaces (absField (primeShiftCharacter z)) X =
      primeLogMass_weightedEulerCoefficientSpaces (fun n => (n : ℝ) ^ ((1 : ℝ) / 2 - z.re)) X := by
  unfold primeLogMass_weightedEulerCoefficientSpaces
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  have hnorm : absField (primeShiftCharacter z) n =
      (n : ℝ) ^ ((1 : ℝ) / 2 - z.re) := by
    rw [absField, primeShiftCharacter, if_pos hn.2,
      Complex.norm_natCast_cpow_of_pos hn.2.pos]
    congr 1
    simp
  rw [hnorm, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- Below the critical line, a normalized prime-shift character is outside
the logarithmic Marcinkiewicz layer. -/
theorem not_memMarcinkiewiczLogLayer_absField_primeShiftCharacter_of_re_lt_half
    {z : ℂ} (hz : z.re < 1 / 2) :
    ¬ MemMarcinkiewiczLogLayer (absField (primeShiftCharacter z)) := by
  intro hmem
  obtain ⟨C, hC⟩ := hmem
  have hδ : 0 < (1 : ℝ) / 2 - z.re := by linarith
  have hlim : Tendsto
      (fun N : ℕ => marcinkiewiczLogQuotient (absField (primeShiftCharacter z)) N)
      atTop atTop := by
    refine (tendsto_marcinkiewiczLogQuotient_rpow_atTop hδ).congr'
      (Filter.Eventually.of_forall fun N => ?_)
    unfold marcinkiewiczLogQuotient
    rw [← primeLogMass_absField_primeShiftCharacter_eq_rpow]
  obtain ⟨N, hCgt, hN⟩ :=
    (hlim.eventually_gt_atTop C).and (Filter.eventually_ge_atTop 2) |>.exists
  exact (not_lt_of_ge (hC N hN)) hCgt

end RHTower

end
