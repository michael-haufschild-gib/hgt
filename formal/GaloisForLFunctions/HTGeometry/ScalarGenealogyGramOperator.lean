import GaloisForLFunctions.HTGeometry.FiniteGenealogyFredholm
import GaloisForLFunctions.HTGeometry.NormalizedGenealogyGram
import Mathlib.Tactic.NoncommRing

/-! # The actual normalized Gram perturbation of a scalar genealogy

The genealogy acts by the columns `e_j-c_(j-1)e_(j-1)`. Its deviation from the
identity is Hilbert–Schmidt exactly at the square-summability threshold. The
normalized Gram perturbation has a canonical finite diagonal trace, and its
literal finite block determinant is the normalized genealogy Gram determinant.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def genealogyGramPerturbation (G : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (G.adjoint ∘L G - 1)

theorem genealogyGramPerturbation_eq_weight (G : H →L[ℂ] H) :
    genealogyGramPerturbation G = (1 / 2 : ℂ) •
      (-(1 - G) - (1 - G).adjoint + (1 - G).adjoint ∘L (1 - G)) := by
  simp only [genealogyGramPerturbation, map_sub, adjoint_one]
  congr 1
  change G.adjoint * G - 1 = -(1 - G) - (1 - G.adjoint) + (1 - G.adjoint) * (1 - G)
  noncomm_ring

theorem genealogyGramPerturbation_isHilbertSchmidt {G : H →L[ℂ] H}
    (hW : IsHilbertSchmidt (1 - G)) : IsHilbertSchmidt (genealogyGramPerturbation G) := by
  rw [genealogyGramPerturbation_eq_weight]
  exact ((hW.neg.sub hW.adjoint).add (hW.comp_left _)).smul _

end Hilbert

variable {G : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2} {w : ℕ → ℂ}

theorem fullScalarGenealogy_basis_of_apply
    (hG : ∀ (f : lp (fun _ : ℕ => ℂ) 2) n, G f n = f n - w n * f (n + 1)) (j : ℕ) :
    G (lpBasisVec j) = finiteGenealogyColumn w j := by
  ext i
  rw [hG, finiteGenealogyColumn_coordinate]
  by_cases h : i = j <;> by_cases hs : i + 1 = j <;>
    simp [lpBasisVec, lp.single_apply, h, hs]

theorem fullGenealogyWeight_basis_zero
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) :
    (1 - G) (lpBasisVec 0) = 0 := by
  change lpBasisVec 0 - G (lpBasisVec 0) = 0
  rw [hG, finiteGenealogyColumn_zero, sub_self]

theorem fullGenealogyWeight_basis_succ
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (n : ℕ) :
    (1 - G) (lpBasisVec (n + 1)) = w n • lpBasisVec n := by
  change lpBasisVec (n + 1) - G (lpBasisVec (n + 1)) = _
  rw [hG, finiteGenealogyColumn_succ]
  abel

theorem fullGenealogyWeight_isHilbertSchmidt_iff
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) :
    IsHilbertSchmidt (1 - G) ↔ Summable (fun n => ‖w n‖ ^ 2) := by
  rw [isHilbertSchmidt_iff_summable (lpBasis ℕ), ← summable_nat_add_iff 1]
  simp only [lpBasis_apply]
  change Summable (fun n => ‖(1 - G) (lpBasisVec (n + 1))‖ ^ 2) ↔ _
  simp_rw [fullGenealogyWeight_basis_succ hG]
  simp [norm_smul, lpBasisVec, lp.norm_single]

theorem coordMatrix_genealogyGramPerturbation
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (i j : ℕ) :
    RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (i, j) =
      (1 / 2 : ℂ) * (⟪finiteGenealogyColumn w i, finiteGenealogyColumn w j⟫_ℂ -
        (if i = j then 1 else 0)) := by
  rw [RHTower.coordMatrix_apply, lpBasis_apply, lpBasis_apply]
  change ⟪lpBasisVec i, (1 / 2 : ℂ) •
    (G.adjoint (G (lpBasisVec j)) - lpBasisVec j)⟫_ℂ = _
  rw [inner_smul_right, inner_sub_right, adjoint_inner_right, hG, hG,
    inner_lpBasisVec_lpBasisVec]

theorem coordMatrix_genealogyGramPerturbation_diag_zero
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) :
    RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (0, 0) = 0 := by
  rw [coordMatrix_genealogyGramPerturbation hG, inner_finiteGenealogyColumn]
  norm_num

theorem coordMatrix_genealogyGramPerturbation_diag_succ
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (n : ℕ) :
    RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (n + 1, n + 1) =
      (1 / 2 : ℂ) * (‖w n‖ ^ 2 : ℂ) := by
  rw [coordMatrix_genealogyGramPerturbation hG, inner_finiteGenealogyColumn]
  simp

theorem trace_blockMatrix_genealogyGramPerturbation
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (N : ℕ) :
    (blockMatrix (RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G))
      (Finset.range (N + 1))).trace =
        (1 / 2 : ℂ) * ∑ n ∈ Finset.range N, (‖w n‖ ^ 2 : ℂ) := by
  rw [Matrix.trace]
  change (∑ i : Finset.range (N + 1),
    RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (i, i)) = _
  rw [Finset.sum_coe_sort (Finset.range (N + 1))
    (fun i => RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (i, i)),
    Finset.sum_range_succ']
  simp only [coordMatrix_genealogyGramPerturbation_diag_zero hG,
    coordMatrix_genealogyGramPerturbation_diag_succ hG, add_zero, Finset.mul_sum]

theorem det_one_add_blockMatrix_genealogyGramPerturbation
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (N : ℕ) :
    (1 + blockMatrix (RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G))
      (Finset.range N)).det = (normalizedGenealogyGram w N : ℂ) := by
  have heq : 1 + blockMatrix (RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G))
      (Finset.range N) = (1 / 2 : ℂ) •
      (1 + blockMatrix (RHTower.coordMatrix (lpBasis ℕ)
        ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N)) (Finset.range N)) := by
    ext i j
    have hi := Finset.mem_range.mp i.property
    have hj := Finset.mem_range.mp j.property
    change (if i = j then (1 : ℂ) else 0) +
      RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G) (i, j) =
      (1 / 2 : ℂ) * ((if i = j then (1 : ℂ) else 0) +
        RHTower.coordMatrix (lpBasis ℕ)
          ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) (i, j))
    rw [coordMatrix_genealogyGramPerturbation hG, coordMatrix_finiteScalarGenealogy_gram,
      if_pos (show (i : ℕ) < N ∧ (j : ℕ) < N from ⟨hi, hj⟩)]
    by_cases h : i = j
    · subst i; simp only [ite_true]; ring
    · have hv : (i : ℕ) ≠ (j : ℕ) := fun hv => h (Subtype.ext hv)
      simp only [if_neg h, if_neg hv]
      ring
  rw [heq, Matrix.det_smul]
  have hd := fredholmDetOp_finiteScalarGenealogy_gram w N
  rw [fredholmDetOp_eq_det_block_of_support (lpBasis ℕ)
    (finiteScalarGenealogy_gram_traceClass w N) (Finset.range N)
    (finiteScalarGenealogy_gram_coordinate_support w N)] at hd
  rw [hd]
  simp only [Fintype.card_coe, Finset.card_range, normalizedGenealogyGram]
  push_cast
  rw [div_pow, one_pow]
  ring

end
end GaloisForLFunctions.HTGeometry
