/-
# Chen--Gupta--Li Proposition 5.1 axial finite aggregation

Eliminates unequal-character row triples on one `S₁` axis, reindexes the
surviving finite carrier by certified equal-character off-diagonal triples,
and sums their closed punctured-frequency tail bounds.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialRowTail

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A fixed finite enumeration of the surviving equal-character off-diagonal
triples on a CGL fibre packet. -/
noncomputable instance cglProposition51FibreEqualCharacterOffDiagonalTripleFintype
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R) :
    Fintype (CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The axial filtered row sum retains exactly the triples whose three
characters agree; all other summands are killed by one of the two complete
zero-frequency character correlations. -/
theorem cglProposition51_axialFilteredRowSum_eq_equalCharacterSum
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (m : ℤ) :
    ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
        (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
      cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) rst m =
      ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m := by
  classical
  let A : Finset (Fin R × Fin R × Fin R) :=
    (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2))
  let E : Fin R × Fin R × Fin R → Prop := fun rst =>
    P.character rst.1 = P.character rst.2.1 ∧
      P.character rst.2.1 = P.character rst.2.2
  change (∑ rst ∈ A, cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
    (cglLemma45FibreRows P) rst m) = _
  have hreduce :
      ∑ rst ∈ A, cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) rst m =
      ∑ rst ∈ A.filter E, cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) rst m := by
    calc
      ∑ rst ∈ A, cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) rst m =
        ∑ rst ∈ A, if E rst then cglProposition51AxialRowTerm w N
          (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) rst m else 0 := by
          apply Finset.sum_congr rfl
          intro rst hrst
          by_cases h12 : P.character rst.1 = P.character rst.2.1
          · by_cases h23 : P.character rst.2.1 = P.character rst.2.2
            · simp [E, h12, h23]
            · have hzero : cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
                  (cglLemma45FibreRows P) rst m = 0 := by
                have h23rows : (cglLemma45FibreRows P rst.2.1).character ≠
                    (cglLemma45FibreRows P rst.2.2).character := by
                  intro h
                  apply h23
                  simpa only [cglLemma45FibreRows, cglLemma45FibreModulus] using h
                unfold cglProposition51AxialRowTerm
                rw [if_neg h23rows]
                ring
              simp [E, h12, h23, hzero]
          · have hzero : cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
                (cglLemma45FibreRows P) rst m = 0 := by
              have h12rows : (cglLemma45FibreRows P rst.1).character ≠
                  (cglLemma45FibreRows P rst.2.1).character := by
                intro h
                apply h12
                simpa only [cglLemma45FibreRows, cglLemma45FibreModulus] using h
              unfold cglProposition51AxialRowTerm
              rw [if_neg h12rows]
              ring
            simp [E, h12, hzero]
      _ = ∑ rst ∈ A.filter E, cglProposition51AxialRowTerm w N
          (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) rst m :=
        (Finset.sum_filter E fun rst => cglProposition51AxialRowTerm w N
          (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) rst m).symm
  rw [hreduce]
  apply Finset.sum_subtype
  intro rst
  simp [A, E, cglCharacterDyadicGramCubicIndexSet]

/-- Exact one-axis form of the CGL Proposition 5.1 residue reduction, now
indexed only by certified surviving equal-character triples. -/
theorem cglProposition51_axialFrequencyTerm_eq_equalCharacterRowSum
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (m : CGLProposition51PuncturedFrequency) :
    cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val) =
      ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val := by
  rw [cglProposition51_axialFrequencyTerm_eq_sum_rowTerm]
  exact cglProposition51_axialFilteredRowSum_eq_equalCharacterSum P w N m.val

/-- Absolute convergence of the full punctured coefficient series on the
third `S₁` ray.  This is the convergence input needed to reassemble the
three disjoint rays into the literal source carrier. -/
theorem cglProposition51_axialFrequencyTerm_norm_summable
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ := by
  have hrowNorm (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
      Summable fun m : CGLProposition51PuncturedFrequency =>
        ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val‖ :=
    cglProposition51_axialRowTerm_norm_summable P w N n u
  have hsumNorm : Summable fun m : CGLProposition51PuncturedFrequency =>
      ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val‖ := by
    exact summable_sum fun u _ => hrowNorm u
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hsumNorm
  rw [cglProposition51_axialFrequencyTerm_eq_equalCharacterRowSum P w N m]
  exact norm_sum_le _ _

/-- The absolute sum on one axial `S₁` ray is bounded by the finite sum of
the certified equal-character row-tail budgets. -/
theorem cglProposition51_axialFrequencyTerm_norm_tsum_le_equalCharacterTailBudget
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
          cglProposition51FibreAxialAnalyticBudget P w N n *
            cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
              (P.ordinate u.1.2.2 - P.ordinate u.1.1) := by
  have hrowNorm (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
      Summable fun m : CGLProposition51PuncturedFrequency =>
        ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val‖ :=
    cglProposition51_axialRowTerm_norm_summable P w N n u
  have hsumNorm : Summable fun m : CGLProposition51PuncturedFrequency =>
      ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val‖ := by
    exact summable_sum fun u _ => hrowNorm u
  have hleft : Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hsumNorm
    rw [cglProposition51_axialFrequencyTerm_eq_equalCharacterRowSum P w N m]
    exact norm_sum_le _ _
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      ∑' m : CGLProposition51PuncturedFrequency,
        ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
          ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
            (cglLemma45FibreRows P) u.1 m.val‖ :=
      hleft.tsum_le_tsum (fun m => by
        rw [cglProposition51_axialFrequencyTerm_eq_equalCharacterRowSum P w N m]
        exact norm_sum_le _ _) hsumNorm
    _ = ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        ∑' m : CGLProposition51PuncturedFrequency,
          ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
            (cglLemma45FibreRows P) u.1 m.val‖ :=
      Summable.tsum_finsetSum fun u _ => hrowNorm u
    _ ≤ ∑ u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P,
        ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
          cglProposition51FibreAxialAnalyticBudget P w N n *
            cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
              (P.ordinate u.1.2.2 - P.ordinate u.1.1) := by
      apply Finset.sum_le_sum
      intro u hu
      exact cglProposition51_axialRowTerm_tsum_le P w N n u

end RHTower
