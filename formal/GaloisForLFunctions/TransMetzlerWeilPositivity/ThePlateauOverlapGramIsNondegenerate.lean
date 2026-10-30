import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeEntersThroughNonRatioLags

/-!
# The plateau overlap Gram is nondegenerate at every width

The first nonzero coefficient can be isolated between its logarithmic center
and the next center. The plateau is positive immediately to the right of zero,
so no finite linear combination of its distinct translates vanishes identically.
Continuity turns this into strict positivity of the actual overlap Gram.
This supplies no lower bound uniform in width or horizon.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- At any positive width, a nonzero coefficient vector synthesizes a nonzero test. -/
theorem plateau_atomicTest_ne_zero {N : ℕ} {x : ℕ → ℝ}
    (hx : ∃ n ∈ Icc 1 N, x n ≠ 0) {w : ℝ} (hw : 0 < w) :
    ∃ u : ℝ, atomicTest N x (atomDilate transMetzlerProfile w) u ≠ 0 := by
  classical
  let n := Nat.find hx
  have hn : n ∈ Icc 1 N ∧ x n ≠ 0 := Nat.find_spec hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn.1).1
  have hgap : 0 < Real.log (n + 1 : ℕ) - Real.log n := by
    apply sub_pos.mpr
    apply Real.log_lt_log hn0
    exact_mod_cast Nat.lt_succ_self n
  let d := min w (Real.log (n + 1 : ℕ) - Real.log n) / 2
  have hd : 0 < d := half_pos (lt_min hw hgap)
  have hdw : d < w :=
    (half_lt_self (lt_min hw hgap)).trans_le (min_le_left _ _)
  have hdgap : d < Real.log (n + 1 : ℕ) - Real.log n :=
    (half_lt_self (lt_min hw hgap)).trans_le (min_le_right _ _)
  have heval : atomicTest N x (atomDilate transMetzlerProfile w) (Real.log n + d) =
      x n * transMetzlerProfile (d / w) := by
    change (∑ m ∈ Icc 1 N,
      x m * transMetzlerProfile ((Real.log n + d - Real.log m) / w)) = _
    rw [sum_eq_single_of_mem n hn.1]
    · rw [add_sub_cancel_left]
    · intro m hm hmn
      rcases lt_or_gt_of_ne hmn with hmn | hnm
      · have hxm : x m = 0 := by
          by_contra hxm
          exact Nat.find_min hx hmn ⟨hm, hxm⟩
        rw [hxm, zero_mul]
      · have hlog : Real.log (n + 1 : ℕ) ≤ Real.log m :=
          Real.log_le_log (by positivity) (by exact_mod_cast hnm)
        have harg : (Real.log n + d - Real.log m) / w < 0 :=
          div_neg_of_neg_of_pos (by linarith only [hdgap, hlog]) hw
        rw [transMetzlerProfile_eq_zero (fun h => (not_le_of_gt harg) h.1), mul_zero]
  refine ⟨Real.log n + d, ?_⟩
  rw [heval]
  exact mul_ne_zero hn.2 (transMetzlerProfile_pos
    ⟨div_pos hd hw, (div_lt_one hw).mpr hdw⟩).ne'

/-- The actual squared mass is strictly positive, even when neighboring atoms overlap. -/
theorem integral_plateau_atomicTest_sq_pos {N : ℕ} {x : ℕ → ℝ}
    (hx : ∃ n ∈ Icc 1 N, x n ≠ 0) {w : ℝ} (hw : 0 < w) :
    0 < ∫ u, atomicTest N x (atomDilate transMetzlerProfile w) u ^ 2 := by
  have hg : ContDiff ℝ 2 (atomDilate transMetzlerProfile w) :=
    contDiff_transMetzlerProfile.comp (contDiff_id.div_const w)
  have hsupp : ∀ u, u ∉ Set.Icc 0 w → atomDilate transMetzlerProfile w u = 0 := by
    intro u hu
    apply transMetzlerProfile_eq_zero
    intro h
    have hlo := (le_div_iff₀ hw).mp h.1
    rw [zero_mul] at hlo
    exact hu ⟨hlo, (div_le_one hw).mp h.2⟩
  obtain ⟨u, hu⟩ := plateau_atomicTest_ne_zero hx hw
  have hcont := (contDiff_atomicTest hg N x).continuous.pow 2
  have hcs : HasCompactSupport (fun u => atomicTest N x (atomDilate transMetzlerProfile w) u ^ 2) := by
    simp only [pow_two]
    exact (hasCompactSupport_atomicTest hsupp N x).mul_right
  apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hcs (fun _ => sq_nonneg _) (x := u)
  exact pow_ne_zero 2 hu

/-- The full autocorrelation Gram, rather than only its diagonal, is positive definite
on every finite plateau family at every positive width. -/
theorem plateau_overlap_gram_strictly_positive {N : ℕ} {x : ℕ → ℝ}
    (hx : ∃ n ∈ Icc 1 N, x n ≠ 0) {w : ℝ} (hw : 0 < w) :
    0 < ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      bumpCorr (atomDilate transMetzlerProfile w) (-(Real.log n - Real.log m)) := by
  obtain ⟨hg, _, hgc⟩ := RenormalizedArithmeticPotentialTheory.atomDilate_facts
    contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu) hw
  rw [← integral_atomicTest_sq_eq_gram hg.continuous hgc N x]
  exact integral_plateau_atomicTest_sq_pos hx hw

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateau_atomicTest_ne_zero
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.integral_plateau_atomicTest_sq_pos
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateau_overlap_gram_strictly_positive
