import GaloisForLFunctions.CompletedArithmeticForms.GammaSuccessorReserve

/-!
# Relative comparison of complete successor reserves

Subtracting one terminal moment identifies the exact semidefinite boundary of a
strict Hankel head. Ordering full successor forms therefore orders their Schur
reserves, including when those reserves have either sign.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

private def terminalMomentDebit (m : ℕ → ℝ) (N : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  m k - if k = 2 * N then t else 0

private theorem terminalMomentDebit_head (m : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    finiteHankelMatrix (terminalMomentDebit m N t) N = finiteHankelMatrix m N := by
  ext i j
  simp only [finiteHankelMatrix, terminalMomentDebit,
    if_neg (show i.val + j.val ≠ 2 * N by omega), sub_zero]

private theorem terminalMomentDebit_tail (m : ℕ → ℝ) (N : ℕ) (t : ℝ) (i : Fin N) :
    terminalMomentDebit m N t (i.val + N) = m (i.val + N) := by
  simp only [terminalMomentDebit, if_neg (show i.val + N ≠ 2 * N by omega), sub_zero]

private theorem terminalMomentDebit_schur (m : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    finiteHankelSuccessorSchur (terminalMomentDebit m N t) N =
      finiteHankelSuccessorSchur m N - t := by
  simp only [finiteHankelSuccessorSchur, terminalMomentDebit_head, terminalMomentDebit_tail]
  simp only [terminalMomentDebit, ↓reduceIte]
  ring

/-- Ordering the complete successor forms orders their exact Schur reserves.
Only the preceding heads need be positive; the successors may have either sign. -/
theorem successorSchur_mono {N : ℕ} {m n : ℕ → ℝ}
    (hm : (finiteHankelMatrix m N).PosDef) (hn : (finiteHankelMatrix n N).PosDef)
    (hmn : (finiteHankelMatrix m (N + 1) - finiteHankelMatrix n (N + 1)).PosSemidef) :
    finiteHankelSuccessorSchur n N ≤ finiteHankelSuccessorSchur m N := by
  let t := finiteHankelSuccessorSchur n N
  have hmhead : (finiteHankelMatrix (terminalMomentDebit m N t) N).PosDef := by
    rwa [terminalMomentDebit_head]
  have hnhead : (finiteHankelMatrix (terminalMomentDebit n N t) N).PosDef := by
    rwa [terminalMomentDebit_head]
  have hnzero : (finiteHankelMatrix (terminalMomentDebit n N t) (N + 1)).PosSemidef := by
    apply (finiteHankelMatrix_succ_posSemidef_iff_schur_nonneg hnhead).mpr
    rw [terminalMomentDebit_schur]
    change 0 ≤ finiteHankelSuccessorSchur n N - finiteHankelSuccessorSchur n N
    exact sub_nonneg.mpr le_rfl
  have heq : finiteHankelMatrix (terminalMomentDebit m N t) (N + 1) =
      (finiteHankelMatrix m (N + 1) - finiteHankelMatrix n (N + 1)) +
        finiteHankelMatrix (terminalMomentDebit n N t) (N + 1) := by
    ext i j
    simp only [finiteHankelMatrix, terminalMomentDebit, Matrix.sub_apply, Matrix.add_apply]
    ring
  have hmzero : (finiteHankelMatrix (terminalMomentDebit m N t) (N + 1)).PosSemidef := by
    rw [heq]
    exact hmn.add hnzero
  have h := (finiteHankelMatrix_succ_posSemidef_iff_schur_nonneg hmhead).mp hmzero
  rw [terminalMomentDebit_schur] at h
  exact sub_nonneg.mp h

/-- Positive scaling preserves the exact reserve with the same scalar. -/
theorem successorSchur_const_mul {N : ℕ} {m : ℕ → ℝ}
    (hm : (finiteHankelMatrix m N).PosDef) {c : ℝ} (hc : 0 < c) :
    finiteHankelSuccessorSchur (fun k => c * m k) N =
      c * finiteHankelSuccessorSchur m N := by
  have hmat (K : ℕ) : finiteHankelMatrix (fun k => c * m k) K =
      c • finiteHankelMatrix m K := rfl
  have hcm : (finiteHankelMatrix (fun k => c * m k) N).PosDef := by
    rw [hmat]
    exact hm.smul hc
  have hd := finiteHankelMatrix_succ_det_eq_schur hcm
  rw [hmat (N + 1), hmat N, Matrix.det_smul, Matrix.det_smul,
    finiteHankelMatrix_succ_det_eq_schur hm] at hd
  simp only [Fintype.card_fin, pow_succ] at hd
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero N hc.ne') hm.det_pos.ne')
  calc
    _ = c ^ N * c * ((finiteHankelMatrix m N).det * finiteHankelSuccessorSchur m N) := hd.symm
    _ = _ := by ring

/-- A relative sandwich of complete successor forms preserves its constants
in the exact Schur reserve. -/
theorem successorSchur_relative_bounds {N : ℕ} {m g : ℕ → ℝ}
    (hm : (finiteHankelMatrix m N).PosDef) (hg : (finiteHankelMatrix g N).PosDef)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hlo : (finiteHankelMatrix m (N + 1) - α • finiteHankelMatrix g (N + 1)).PosSemidef)
    (hhi : (β • finiteHankelMatrix g (N + 1) - finiteHankelMatrix m (N + 1)).PosSemidef) :
    α * finiteHankelSuccessorSchur g N ≤ finiteHankelSuccessorSchur m N ∧
      finiteHankelSuccessorSchur m N ≤ β * finiteHankelSuccessorSchur g N := by
  have hαg : (finiteHankelMatrix (fun k => α * g k) N).PosDef := hg.smul hα
  have hβg : (finiteHankelMatrix (fun k => β * g k) N).PosDef := hg.smul hβ
  have hl := successorSchur_mono hm hαg hlo
  have hu := successorSchur_mono hβg hm hhi
  rw [successorSchur_const_mul hg hα] at hl
  rw [successorSchur_const_mul hg hβ] at hu
  exact ⟨hl, hu⟩

/-- Relative control in the full comparison norm transfers to the successor
reserve with exactly the same error factor. -/
theorem successorSchur_relative_error {N : ℕ} {m g : ℕ → ℝ}
    (hg : (finiteHankelMatrix g (N + 1)).PosDef) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (herror : ∀ v : Fin (N + 1) → ℝ,
      |v ⬝ᵥ (finiteHankelMatrix m (N + 1) - finiteHankelMatrix g (N + 1)) *ᵥ v| ≤
        ε * (v ⬝ᵥ finiteHankelMatrix g (N + 1) *ᵥ v)) :
    |finiteHankelSuccessorSchur m N - finiteHankelSuccessorSchur g N| ≤
      ε * finiteHankelSuccessorSchur g N := by
  have hα : 0 < 1 - ε := sub_pos.mpr hε1
  have hβ : 0 < 1 + ε := by linarith only [hε]
  have hlo : (finiteHankelMatrix m (N + 1) -
      (1 - ε) • finiteHankelMatrix g (N + 1)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsHermitian]
      ext i j
      simp [finiteHankelMatrix, Nat.add_comm]
    · intro v
      have he := (abs_le.mp (herror v)).1
      simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul] at he ⊢
      nlinarith only [he]
  have hhi : ((1 + ε) • finiteHankelMatrix g (N + 1) -
      finiteHankelMatrix m (N + 1)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsHermitian]
      ext i j
      simp [finiteHankelMatrix, Nat.add_comm]
    · intro v
      have he := (abs_le.mp (herror v)).2
      simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul] at he ⊢
      nlinarith only [he]
  have hmfull : (finiteHankelMatrix m (N + 1)).PosDef := by
    have h := (hg.smul hα).add_posSemidef hlo
    have he : (1 - ε) • finiteHankelMatrix g (N + 1) +
        (finiteHankelMatrix m (N + 1) - (1 - ε) • finiteHankelMatrix g (N + 1)) =
          finiteHankelMatrix m (N + 1) := by abel
    rwa [he] at h
  have hi : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) h)
  have hmhead : (finiteHankelMatrix m N).PosDef := hmfull.submatrix hi
  have hghead : (finiteHankelMatrix g N).PosDef := hg.submatrix hi
  obtain ⟨hl, hu⟩ := successorSchur_relative_bounds hmhead hghead hα hβ hlo hhi
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu]

#print axioms successorSchur_mono
#print axioms successorSchur_const_mul
#print axioms successorSchur_relative_bounds
#print axioms successorSchur_relative_error

end GaloisForLFunctions.CompletedArithmeticForms
