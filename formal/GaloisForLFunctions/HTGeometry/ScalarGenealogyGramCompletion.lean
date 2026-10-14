import GaloisForLFunctions.HTGeometry.ScalarGenealogyGramOperator
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity

/-! # Canonical regularized completion of the actual genealogy Gram operator

The normalized finite determinants converge exactly at the square-summability
threshold. Their limit is the regularized determinant of `(G*G-I)/2`, multiplied
by the exponential of the canonical diagonal trace correction. No ordinary trace
of a merely Hilbert–Schmidt perturbation is used.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap Filter Topology

variable {G : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2} {w : ℕ → ℂ}

def scalarGenealogyGramKernel (G : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    ℕ × ℕ → ℂ := RHTower.coordMatrix (lpBasis ℕ) (genealogyGramPerturbation G)

def scalarGenealogyGramCompletion
    (G : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) (w : ℕ → ℂ) : ℂ :=
  RHTower.det2Op (lpBasis ℕ) (genealogyGramPerturbation G) *
    Complex.exp ((1 / 2 : ℂ) * ((∑' n, ‖w n‖ ^ 2 : ℝ) : ℂ))

private theorem truncation_support (K : ℕ × ℕ → ℂ) (s : Finset ℕ)
    (p : ℕ × ℕ) (hp : p ∉ s ×ˢ s) : truncKernel K s p = 0 := by
  apply if_neg
  simpa only [Finset.mem_product] using hp

private theorem blockMatrix_truncation (K : ℕ × ℕ → ℂ) (s : Finset ℕ) :
    blockMatrix (truncKernel K s) s = blockMatrix K s := by
  ext i j
  simp [blockMatrix, truncKernel]

theorem hsTraceDiag_truncKernel_genealogyGram
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (N : ℕ) :
    hsTraceDiag (truncKernel (scalarGenealogyGramKernel G) (Finset.range (N + 1))) =
      (1 / 2 : ℂ) * ∑ n ∈ Finset.range N, (‖w n‖ ^ 2 : ℂ) := by
  rw [← trace_blockMatrix_eq_hsTraceDiag
    (truncation_support (scalarGenealogyGramKernel G) (Finset.range (N + 1))),
    blockMatrix_truncation]
  exact trace_blockMatrix_genealogyGramPerturbation hG N

theorem normalizedGenealogyGram_eq_regularized_prefix
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) (N : ℕ) :
    (normalizedGenealogyGram w (N + 1) : ℂ) =
      entireDet2 (truncKernel (scalarGenealogyGramKernel G) (Finset.range (N + 1))) (-1) *
        Complex.exp ((1 / 2 : ℂ) * ∑ n ∈ Finset.range N, (‖w n‖ ^ 2 : ℂ)) := by
  have hsupp := truncation_support (scalarGenealogyGramKernel G) (Finset.range (N + 1))
  have hK := isHS_of_support_subset
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1)) hsupp
  have h := det_one_sub_smul_blockMatrix hK hsupp (-1)
  simp only [neg_one_smul, sub_neg_eq_add, completedDet2, neg_one_mul, neg_neg,
    blockMatrix_truncation] at h
  rw [show (1 + blockMatrix (scalarGenealogyGramKernel G) (Finset.range (N + 1))).det =
      (normalizedGenealogyGram w (N + 1) : ℂ) from
        det_one_add_blockMatrix_genealogyGramPerturbation hG (N + 1),
    hsTraceDiag_truncKernel_genealogyGram hG N] at h
  exact h

private theorem tendsto_normalizedGenealogyGram_completion
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j)
    (hs : Summable (fun n => ‖w n‖ ^ 2)) :
    Tendsto (fun N => (normalizedGenealogyGram w N : ℂ)) atTop
      (𝓝 (scalarGenealogyGramCompletion G w)) := by
  let K := scalarGenealogyGramKernel G
  have hK : IsHS K := RHTower.isHS_coordMatrix (lpBasis ℕ)
    (genealogyGramPerturbation_isHilbertSchmidt
      ((fullGenealogyWeight_isHilbertSchmidt_iff hG).mpr hs))
  have hlim0 : Tendsto (fun N => hsNorm (K - truncKernel K (Finset.range N))) atTop (𝓝 0) :=
    (tendsto_hsNorm_sub_truncKernel hK).comp tendsto_finset_range
  have hlim : Tendsto (fun N => hsNorm (truncKernel K (Finset.range (N + 1)) - K))
      atTop (𝓝 0) := by
    have ht := (tendsto_add_atTop_iff_nat 1).mpr hlim0
    refine ht.congr fun N => ?_
    rw [show truncKernel K (Finset.range (N + 1)) - K =
      -(K - truncKernel K (Finset.range (N + 1))) by abel, hsNorm_neg]
  have hdet := tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
    (fun N => truncKernel K (Finset.range (N + 1))) K
    (fun N => isHS_truncKernel hK (Finset.range (N + 1))) hK hlim (-1)
  have htrace : Tendsto (fun N => (1 / 2 : ℂ) * ∑ n ∈ Finset.range N, (‖w n‖ ^ 2 : ℂ))
      atTop (𝓝 ((1 / 2 : ℂ) * ((∑' n, ‖w n‖ ^ 2 : ℝ) : ℂ))) := by
    have h := ((Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat).const_mul
      (1 / 2 : ℂ)
    simpa only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_pow] using h
  have hp := hdet.mul ((Complex.continuous_exp.tendsto _).comp htrace)
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact hp.congr fun N => (normalizedGenealogyGram_eq_regularized_prefix hG N).symm

theorem scalarGenealogyGramCompletion_spec_iff
    (hG : ∀ j, G (lpBasisVec j) = finiteGenealogyColumn w j) :
    ((scalarGenealogyGramCompletion G w).im = 0 ∧
      1 ≤ (scalarGenealogyGramCompletion G w).re ∧
      Tendsto (fun N => (normalizedGenealogyGram w N : ℂ)) atTop
        (𝓝 (scalarGenealogyGramCompletion G w))) ↔ Summable (fun n => ‖w n‖ ^ 2) := by
  constructor
  · intro h
    have hr : Tendsto (normalizedGenealogyGram w) atTop
        (𝓝 (scalarGenealogyGramCompletion G w).re) := by
      simpa only [Function.comp_def, Complex.ofReal_re] using
        (Complex.continuous_re.tendsto _).comp h.2.2
    exact (normalizedGenealogyGram_bddAbove_iff w).mp hr.bddAbove_range
  · intro hs
    have h := tendsto_normalizedGenealogyGram_completion hG hs
    obtain ⟨L, hL, hl⟩ := (normalizedGenealogyGram_finite_limit_iff w).mpr hs
    have hc := (Complex.continuous_ofReal.tendsto L).comp hl
    have heq : scalarGenealogyGramCompletion G w = (L : ℂ) := tendsto_nhds_unique h hc
    refine ⟨?_, ?_, h⟩
    · rw [heq, Complex.ofReal_im]
    · rw [heq, Complex.ofReal_re]
      exact hL

end
end GaloisForLFunctions.HTGeometry
