import GaloisForLFunctions.HTGeometry.JetShiftPolynomial

/-!
# The gradients of the phase jets span a bounded space

A polynomial relation among the first `M + 1` phase jets differentiates to a
linear relation among their gradients, whose top coefficient is the separant.
Where the separant does not vanish, the top gradient therefore lies in the span
of the lower ones.

Applying this to every iterate of a relation of order `n` — all of which have
the same nonvanishing leading coefficient — puts *every* jet gradient in the
span of the first `n`.  The differential rank of the whole jet family is
therefore at most `n` wherever the separant is nonzero.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The span of the gradients of the first `n` phase jets at a point. -/
def jetGradientSpan (omega : d → ℝ) (F : (d → ℂ) → ℂ) (n : ℕ) (z : d → ℂ) :
    Submodule ℂ (d → ℂ) :=
  Submodule.span ℂ
    (Set.range fun i : Fin n => gradientVec (phaseJet omega F (i : ℕ)) z)

theorem gradientVec_mem_jetGradientSpan (omega : d → ℝ) (F : (d → ℂ) → ℂ)
    {n : ℕ} (z : d → ℂ) (i : Fin n) :
    gradientVec (phaseJet omega F (i : ℕ)) z ∈ jetGradientSpan omega F n z :=
  Submodule.subset_span ⟨i, rfl⟩

/-- **One step: a relation with nonvanishing separant puts the top gradient in
the span of the lower ones.** -/
theorem gradientVec_top_mem_jetGradientSpan {U : Set (d → ℂ)} (hU : IsOpen U)
    (omega : d → ℝ) {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {M : ℕ}
    (R : MvPolynomial (Fin (M + 1)) ℂ)
    (hR : ∀ z ∈ U, jetRelationEval omega F R z = 0) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ U)
    (hsep : MvPolynomial.eval (fun i : Fin (M + 1) => phaseJet omega F (i : ℕ) z₀)
      (MvPolynomial.pderiv (Fin.last M) R) ≠ 0) :
    gradientVec (phaseJet omega F M) z₀ ∈ jetGradientSpan omega F M z₀ := by
  classical
  set c : Fin (M + 1) → ℂ := fun i =>
    MvPolynomial.eval (fun j : Fin (M + 1) => phaseJet omega F (j : ℕ) z₀)
      (MvPolynomial.pderiv i R) with hc
  have hsum : ∑ i : Fin (M + 1),
      c i • gradientVec (phaseJet omega F (i : ℕ)) z₀ = 0 :=
    sum_smul_gradientVec_eq_zero hU
      (fun i : Fin (M + 1) => analyticOnNhd_phaseJet omega hF (i : ℕ)) R hR hz₀
  rw [Fin.sum_univ_castSucc] at hsum
  simp only [Fin.val_last, Fin.val_castSucc] at hsum
  have hlast : c (Fin.last M) • gradientVec (phaseJet omega F M) z₀
      = -∑ i : Fin M,
          c i.castSucc • gradientVec (phaseJet omega F (i : ℕ)) z₀ :=
    (add_eq_zero_iff_neg_eq.1 hsum).symm
  have hmem : c (Fin.last M) • gradientVec (phaseJet omega F M) z₀
      ∈ jetGradientSpan omega F M z₀ := by
    rw [hlast]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem _ _ (gradientVec_mem_jetGradientSpan omega F z₀ i)
  have hinv := Submodule.smul_mem (jetGradientSpan omega F M z₀)
    (c (Fin.last M))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hsep, one_smul] at hinv

/-- **Every jet gradient lies in the span of the first `n`.** -/
theorem gradientVec_mem_jetGradientSpan_of_relation {U : Set (d → ℂ)}
    (hU : IsOpen U) (omega : d → ℝ) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F U) {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (hQ : ∀ z ∈ U, jetRelationEval omega F Q z = 0) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ U)
    (hsep : MvPolynomial.eval (fun i : Fin (n + 1) => phaseJet omega F (i : ℕ) z₀)
      (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0) (k : ℕ) :
    gradientVec (phaseJet omega F k) z₀ ∈ jetGradientSpan omega F n z₀ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases hk : k < n
      · exact gradientVec_mem_jetGradientSpan omega F z₀ ⟨k, hk⟩
      · obtain ⟨m, rfl⟩ : ∃ m, k = n + m := ⟨k - n, by omega⟩
        have hsepIter : MvPolynomial.eval
            (fun i : Fin (n + m + 1) => phaseJet omega F (i : ℕ) z₀)
            (MvPolynomial.pderiv (Fin.last (n + m)) (jetShiftIter m Q)) ≠ 0 := by
          rw [eval_pderiv_last_jetShiftIter]
          exact hsep
        have hstep := gradientVec_top_mem_jetGradientSpan hU omega hF
          (jetShiftIter m Q)
          (jetRelationEval_jetShiftIter_eq_zero hU omega hF hQ m) hz₀ hsepIter
        refine Submodule.span_le.2 ?_ hstep
        rintro v ⟨i, rfl⟩
        exact ih (i : ℕ) (by omega)

end

end GaloisForLFunctions.HTGeometry
