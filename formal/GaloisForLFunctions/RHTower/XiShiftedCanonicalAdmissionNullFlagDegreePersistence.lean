import GaloisForLFunctions.HTGeometry.FiniteExtremeNodePersistence
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredCompletedSourceLogDerivative

/-!
# Shifted-Xi source null-flag persistence across degree

Finite outer interlacing transports the literal source-first completed-`P^sharp` super-apex null
flag across one degree step at fixed mass.  A positive defect cannot disappear by changing finite
admission while the containing positive block remains available.
-/

open Matrix

namespace RHTower

noncomputable section

/-- **Literal fixed-mass degree persistence.**  Positive completed-source null flag at degree `n`
forces positive flag at degree `n+1`. -/
theorem xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_succ_pos_of_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hnodesCurrent : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) (n - 1), 0 < x)
    (hnodesNext : ∀ x ∈ HTGeometry.gaussNodes
      (xiShiftedRealMomentSequence w) n, x ≠ 0)
    (a : ℝ) {eta : ℝ} (heta : 0 < eta)
    (hsource :
      0 < xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag w n a eta) :
    0 < xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag w (n + 1) a eta := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans (by norm_num) hw)
  have hHcurrent : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_eq_gauss
    hn hw0 hHcurrent (fun x hxmem => (hnodesCurrent x hxmem).ne') a eta] at hsource
  rw [xiShiftedCanonicalAdmissionSuperApexCompletedSourceNullFlag_eq_gauss
    (n := n + 1) (by omega) hw0 (by simpa only [show n + 1 + 2 = n + 3 by omega] using hH)
    (by simpa only [show n + 1 - 1 = n by omega] using hnodesNext) a eta]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one] at hnodesCurrent hsource ⊢
  exact HTGeometry.gaussSuperApexNullFlagPoissonSource_succ_pos_of_pos
    hbelow (m := m) (by omega)
      (sq_pos_of_pos (lt_trans (by norm_num) hw)) hnodesCurrent a heta hsource

end

end RHTower
