import GaloisForLFunctions.HTGeometry.FiniteExtremeSourceCapital
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredCompletedSourceLogDerivative

/-!
# Shifted-Xi centered completed-source capital across degree

At fixed mass, the literal de-resisted moving-apex-centered completed source is strict degree
capital: one next canonical Gauss node carries more residue than every current positive node.
This is a pre-aggregation source theorem; it does not assert monotonicity of a posterior Cauchy or
Poisson reporter.
-/

open Matrix

namespace RHTower

noncomputable section

/-- **Literal strict source-capital law.** At fixed shifted-Xi mass, one next-degree admitted node
carries strictly larger de-resisted centered completed-source residue than every current node. -/
theorem exists_xiShiftedCanonicalAdmissionCenteredSourceResidue_above_all_succ
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), 0 < x) :
    ∃ z ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) n, 0 < z ∧
      ∀ x ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) (n - 1),
        xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x <
          xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w (n + 1) z := by
  let s := xiShiftedRealMomentSequence w
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans (by norm_num) hw)
  have hHcurrent :
      (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodes ⊢
  obtain ⟨z, hzmem, hzpos, hzall⟩ :=
    HTGeometry.exists_gaussNode_apexCenteredResidue_above_all_below
      hbelow (m := m) (by omega)
        (sq_pos_of_pos (lt_trans (by norm_num) hw)) hnodes
  refine ⟨z, hzmem, hzpos, ?_⟩
  intro x hxmem
  have hPcurrent : HTGeometry.monicMomentAdmissionPolynomial s (m + 1) =
      HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHcurrent
  have hPnext : HTGeometry.monicMomentAdmissionPolynomial s (m + 2) =
      HTGeometry.monicOrtho s (m + 2) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hxroot :
      (HTGeometry.monicMomentAdmissionPolynomial s (m + 1)).eval x = 0 := by
    rw [hPcurrent]
    exact (HTGeometry.mem_gaussNodes_iff m x).mp hxmem
  have hzroot :
      (HTGeometry.monicMomentAdmissionPolynomial s (m + 2)).eval z = 0 := by
    rw [hPnext]
    exact (HTGeometry.mem_gaussNodes_iff (m + 1) z).mp hzmem
  rw [xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
      (n := m + 1) (by omega) hw0 hHcurrent (hnodes x hxmem).ne' hxroot,
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
      (n := m + 2) (by omega) hw0 hH hzpos.ne' hzroot]
  exact hzall x hxmem

/-- Every positive current centered source atom has a strictly larger positive successor atom. -/
theorem exists_xiShiftedCanonicalAdmissionCenteredSourceResidue_succ_gt_of_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hnodes : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), 0 < x)
    {x : ℝ} (hxmem : x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1))
    (hxsource : 0 <
      xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x) :
    ∃ z ∈ HTGeometry.gaussNodes (xiShiftedRealMomentSequence w) n,
      xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w n x <
        xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w (n + 1) z ∧
      0 < xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue w (n + 1) z := by
  obtain ⟨z, hzmem, _hzpos, hzall⟩ :=
    exists_xiShiftedCanonicalAdmissionCenteredSourceResidue_above_all_succ
      hw hn hH hnodes
  have hlt := hzall x hxmem
  exact ⟨z, hzmem, hlt, hxsource.trans hlt⟩

end

end RHTower

