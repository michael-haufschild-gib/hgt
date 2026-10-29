import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilTrialEnergiesAreSimpleAndProper

/-!
# Growing overlap changes every nonpolar reference energy

The separated Ramanujan reference energy at a conductor other than one is exactly
`E_m(1) - log c`. It crosses zero at `c = exp(E_m(1))`. Consequently every finite family
of nonpolar conductors has negative reference energy at a sufficiently large overlap.

This classifies the continuation of the reference formula. The identification of that formula
with actual complete-Weil quasimodes was proved in the separated regime; extending it to growing
overlap requires the new archimedean overlaps and non-ratio prime terms.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The self finite part loses exactly the logarithm of the overlap. -/
theorem completeWeilSelfFinitePart_eq_at_one_sub_log (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    completeWeilSelfFinitePart φ c = completeWeilSelfFinitePart φ 1 - Real.log c := by
  simp only [completeWeilSelfFinitePart, mul_one, one_div, Real.log_inv]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc.ne']
  ring

/-- The rank-one pole shift does not alter any nonpolar conductor's logarithmic loss. -/
theorem completeWeilAdjunctionEnergy_eq_at_one_sub_log (φ : ℝ → ℝ) {m : ℕ} (hm : m ≠ 1)
    {c : ℝ} (hc : 0 < c) :
    completeWeilAdjunctionEnergy φ c m = completeWeilAdjunctionEnergy φ 1 m - Real.log c := by
  simp only [completeWeilAdjunctionEnergy, if_neg hm, add_zero,
    completeWeilSelfFinitePart_eq_at_one_sub_log φ hc]
  ring

/-- Exact overlap where the continued nonpolar reference energy changes sign. -/
theorem completeWeilAdjunctionEnergy_neg_iff (φ : ℝ → ℝ) {m : ℕ} (hm : m ≠ 1)
    {c : ℝ} (hc : 0 < c) :
    completeWeilAdjunctionEnergy φ c m < 0 ↔
      Real.exp (completeWeilAdjunctionEnergy φ 1 m) < c := by
  rw [completeWeilAdjunctionEnergy_eq_at_one_sub_log φ hm hc, sub_lt_zero,
    ← Real.exp_lt_exp, Real.exp_log hc]

/-- Every finite set of nonpolar reference modes is negative at one overlap greater than one. -/
theorem exists_overlap_all_nonpolar_reference_energies_negative (φ : ℝ → ℝ) (S : Finset ℕ) :
    ∃ c : ℝ, 1 < c ∧ ∀ m ∈ S, m ≠ 1 → completeWeilAdjunctionEnergy φ c m < 0 := by
  classical
  let B : ℝ := ∑ m ∈ S, |completeWeilAdjunctionEnergy φ 1 m|
  have hB : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Real.exp (B + 1), ?_, ?_⟩
  · exact Real.one_lt_exp_iff.mpr (by linarith only [hB])
  · intro m hm hm1
    apply (completeWeilAdjunctionEnergy_neg_iff φ hm1 (Real.exp_pos _)).mpr
    apply Real.exp_lt_exp.mpr
    have hterm : |completeWeilAdjunctionEnergy φ 1 m| ≤ B :=
      single_le_sum (fun n _ => abs_nonneg (completeWeilAdjunctionEnergy φ 1 n)) hm
    linarith only [le_abs_self (completeWeilAdjunctionEnergy φ 1 m), hterm]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.completeWeilAdjunctionEnergy_neg_iff
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_overlap_all_nonpolar_reference_energies_negative
