import GaloisForLFunctions.RHTower.XiShiftedHankelFirstContactCurvatureQuotient
import GaloisForLFunctions.RHTower.XiShiftedHankelDefectRecession

/-!
# Source-priced renewal on the actual shifted-Xi terminal frontier

The parity-complete curvature quotient applies to every positive flat face.  This module lands it
on the canonical terminal-frontier schedule itself.  Every occupied strict rung is a singular PSD
face with positive head, hence carries an exact adaptive negative-energy price.  Moreover, false
RH forces occupied frontiers, and therefore priced strict rungs, arbitrarily far to the right.

Thus producer existence and cofinal admission are unconditional.  Any remaining obstruction must
be quantitative inefficiency between priced Lipschitz persistence and unpriced positive-chamber
travel; no fixed orientation map or linear reporter enters.
-/

open Matrix

namespace RHTower

noncomputable section

/-- Failure of a shifted-Xi higher block persists under enlargement of admission degree. -/
theorem xiShiftedHigherBlockFailureSet_mono
    {n m : ℕ} (hnm : n ≤ m) :
    xiShiftedHigherBlockFailureSet n ⊆ xiShiftedHigherBlockFailureSet m := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  intro hlarge
  exact hy.2 (xiShiftedMomentHankel_posDef_of_le (by omega) hlarge)

/-- Occupied terminal frontiers are monotone under arbitrary finite degree enlargement. -/
theorem xiShiftedHigherBlockTerminalFrontier_mono_of_le
    {n m : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hnm : n ≤ m) :
    xiShiftedHigherBlockTerminalFrontier n ≤
      xiShiftedHigherBlockTerminalFrontier m := by
  apply csSup_le hne
  intro y hy
  exact le_xiShiftedHigherBlockTerminalFrontier_of_mem
    (xiShiftedHigherBlockFailureSet_mono hnm hy)

/-- Every actual occupied strict frontier rung carries the exact parity-complete adaptive source
price.  The witness is built from the null vector of the canonical singular face, not from an
auxiliary crossing or fixed reporter. -/
theorem exists_sourceAdaptive_frontierCertificate_of_strict_step
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ∃ k : ℕ, n + 2 ≤ k ∧ ∃ x : Fin (k + 2) → ℝ,
      0 < -xiShiftedMomentHankelQuadratic
        (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x ∧
      xiShiftedHigherBlockTerminalFrontier (n + 1) +
          (-xiShiftedMomentHankelQuadratic
            (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x) /
            xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
        xiShiftedHigherBlockTerminalFrontier k := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface :=
    xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdet : (xiShiftedMomentHankelMatrix y (n + 3)).det = 0 := by
    exact not_ne_iff.mp ((hface.2.1.posDef_iff_det_ne_zero).not.mp hface.2.2)
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hlast : c (Fin.last (n + 2)) ≠ 0 :=
    xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y (n + 2) c hface.1 hcne hc
  simpa only [y] using
    (exists_sourceAdaptive_frontierCertificate_of_flatFace hy c hface.1 hc hlast)

/-- Under false RH, occupied shifted-Xi terminal frontiers are unbounded above.  This is stronger
than pointwise defect existence: the defect is embedded into a canonical scalar frontier. -/
theorem exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) (A : ℝ) :
    ∃ n : ℕ, (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n := by
  let y : ℝ := |A| + 1
  have hy : 0 < y := by
    dsimp only [y]
    have habs : 0 ≤ |A| := abs_nonneg A
    linarith
  have hAy : A < y := by
    dsimp only [y]
    have hle : A ≤ |A| := le_abs_self A
    linarith
  have hfail : ∃ N : ℕ,
      ¬(xiShiftedMomentHankelMatrix y N).PosSemidef := by
    by_contra hnone
    push Not at hnone
    exact hnot
      ((xiShiftedMomentHankelMatrix_forall_posSemidef_iff_riemannHypothesis hy.le).mp hnone)
  obtain ⟨N, hN⟩ := hfail
  have hlarge : ¬(xiShiftedMomentHankelMatrix y (N + 2)).PosDef := by
    intro hpos
    exact hN (xiShiftedMomentHankel_posDef_of_le (by omega) hpos).posSemidef
  have hymem : y ∈ xiShiftedHigherBlockFailureSet N := ⟨hy.le, hlarge⟩
  exact ⟨N, ⟨y, hymem⟩,
    hAy.trans_le (le_xiShiftedHigherBlockTerminalFrontier_of_mem hymem)⟩

private theorem exists_strict_succ_of_lt
    {f : ℕ → ℝ} {a b : ℕ} (hab : a < b) (h : f a < f b) :
    ∃ j : ℕ, a ≤ j ∧ j < b ∧ f j < f (j + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases hlast : f b < f (b + 1)
      · exact ⟨b, by omega, by omega, hlast⟩
      · have hab' : a < b := by
          by_contra hnot
          have hba : b ≤ a := Nat.le_of_not_gt hnot
          have habLe : a ≤ b := by omega
          have habEq : a = b := Nat.le_antisymm habLe hba
          subst b
          exact hlast h
        have hback : f (b + 1) ≤ f b := le_of_not_gt hlast
        obtain ⟨j, haj, hjb, hj⟩ := ih hab' (h.trans_le hback)
        exact ⟨j, haj, by omega, hj⟩

/-- If RH is false, exact adaptive source prices occur on occupied strict terminal-frontier rungs
arbitrarily far to the right.  This closes cofinal producer admission; it does not assume a lower
bound on accumulated prices. -/
theorem exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) (A : ℝ) :
    ∃ n : ℕ, (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      ∃ k : ℕ, n + 2 ≤ k ∧ ∃ x : Fin (k + 2) → ℝ,
        0 < -xiShiftedMomentHankelQuadratic
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x ∧
        xiShiftedHigherBlockTerminalFrontier (n + 1) +
            (-xiShiftedMomentHankelQuadratic
              (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x) /
              xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
          xiShiftedHigherBlockTerminalFrontier k := by
  obtain ⟨a, hane, hAa⟩ :=
    exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis hnot A
  obtain ⟨b, hbne, habFront⟩ :=
    exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis
      hnot (xiShiftedHigherBlockTerminalFrontier a)
  have hab : a < b := by
    by_contra hnotab
    have hba : b ≤ a := Nat.le_of_not_gt hnotab
    have hle := xiShiftedHigherBlockTerminalFrontier_mono_of_le hbne hba
    exact (not_lt_of_ge hle) habFront
  obtain ⟨n, han, hnb, hstrict⟩ :=
    exists_strict_succ_of_lt hab habFront
  have hnne : (xiShiftedHigherBlockFailureSet n).Nonempty := by
    obtain ⟨y, hy⟩ := hane
    exact ⟨y, xiShiftedHigherBlockFailureSet_mono han hy⟩
  have hAn : A < xiShiftedHigherBlockTerminalFrontier n :=
    hAa.trans_le (xiShiftedHigherBlockTerminalFrontier_mono_of_le hane han)
  exact ⟨n, hnne, hAn, hstrict,
    exists_sourceAdaptive_frontierCertificate_of_strict_step hnne hstrict⟩

/-- **Closed curvature-renewal dichotomy.** Either RH holds, or the actual shifted-Xi terminal
frontier contains source-priced strict renewal events above every real mass threshold. -/
theorem riemannHypothesis_or_cofinal_sourceAdaptive_frontierCertificates :
    RiemannHypothesis ∨
      ∀ A : ℝ,
        ∃ n : ℕ, (xiShiftedHigherBlockFailureSet n).Nonempty ∧
          A < xiShiftedHigherBlockTerminalFrontier n ∧
          xiShiftedHigherBlockTerminalFrontier n <
            xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
          ∃ k : ℕ, n + 2 ≤ k ∧ ∃ x : Fin (k + 2) → ℝ,
            0 < -xiShiftedMomentHankelQuadratic
              (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x ∧
            xiShiftedHigherBlockTerminalFrontier (n + 1) +
                (-xiShiftedMomentHankelQuadratic
                  (xiShiftedHigherBlockTerminalFrontier (n + 1)) (k + 2) x) /
                  xiShiftedMomentHankelQuadraticLipschitzWeight x ≤
              xiShiftedHigherBlockTerminalFrontier k := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hRH)

end

end RHTower
