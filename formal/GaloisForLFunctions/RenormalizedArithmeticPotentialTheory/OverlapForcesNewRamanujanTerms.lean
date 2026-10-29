import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilSelfEnergyHasItsFinitePart

/-!
# Growing overlap changes every nonpolar reference energy

The separated Ramanujan reference energy at a conductor other than one is exactly
`E_m(1) - log c`. It crosses zero at `c = exp(E_m(1))`. Consequently every finite family
of nonpolar conductors has negative reference energy at a sufficiently large overlap.

This classifies the continuation of the reference formula. The identification of that formula
with actual complete-Weil quasimodes was proved in the separated regime; extending it to growing
overlap requires the new archimedean overlaps and non-ratio prime terms.
The actual normalized diagonal retains this logarithmic loss whenever `c/N≤1`;
its Robin remainder is at most `(exp(1/2)/2)c/N` without a separation restriction.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis _root_.RHTower

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

/-- The complete diagonal's scalar finite part does not require separated atoms. -/
theorem completeWeil_self_scalar_identity_all_widths (φ : ℝ → ℝ) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    2 * gammaHardyPhaseRate 0 + Real.log (1 / (c / N)) + profileRobin φ - Real.log N =
      completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (1 / (c / N)) - Real.log N = -Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hs : completeWeilSelfFinitePart φ c =
      -Real.log (2 * Real.pi) - Real.log c + bumpRobin φ 1 / (∫ u, φ u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc.ne']
    ring
  rw [hs]
  linarith only [finitePart_profileRobin_eq φ, hlog]

/-- The actual complete self-error is `O(c/N)` throughout `0<c≤N`, including growing overlap. -/
theorem abs_completeWeilSelfError_le_of_width_le_one {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) :
    |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := by
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hφ (by norm_num)
  have hLip : ∀ u v, |φ u - φ v| ≤ (K : ℝ) * |u - v| := fun u v => by
    simpa only [Real.dist_eq] using hK.dist_le_mul u v
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have h := abs_levyEnergy_atomDilate_sub_le hφ hsupp hM hw
    ((div_le_one hN0).mpr hcN) hLip
  have heq : completeWeilSelfError φ c N =
      (levyEnergy (atomDilate φ (c / N)) -
        (Real.log (1 / (c / N)) + profileRobin φ) *
          ∫ u, atomDilate φ (c / N) u ^ 2) / (∫ u, atomDilate φ (c / N) u ^ 2) := by
    rw [completeWeilSelfError, ← completeWeil_self_scalar_identity_all_widths φ hc hN]
    field_simp [hG.ne']
    ring
  rw [heq, abs_div, abs_of_pos hG, div_le_iff₀ hG]
  exact h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.completeWeilAdjunctionEnergy_neg_iff
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_overlap_all_nonpolar_reference_energies_negative
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.abs_completeWeilSelfError_le_of_width_le_one
