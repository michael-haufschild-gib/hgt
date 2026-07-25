import GaloisForLFunctions.RHTower.XiPoissonCutOnLine
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

/-!
# Boundedness on one vertical line implies the Riemann Hypothesis

The minimal-counterexample wrapper.  Suppose the Poisson trace is bounded on the vertical line
`Re t = sigma` and some copy is off the critical line.  Among such copies take one of least height
`g`; then every copy below `g` is on the line, so its contribution to the line value has constant
modulus and the trace above the cut `g` is bounded on the same line.  The cut assembly then puts the
cut's bottom shell -- which contains the chosen copy -- on the critical line, a contradiction.

No induction over shells is used: `exists_min_xiPoissonPoint_re_of_nonempty` supplies the minimal
counterexample directly, and `finite_xiPoissonShell` makes the removed part finite.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

theorem le_xiPoissonCutHeight {g : ℝ} (h : (xiPoissonCut g).Nonempty) :
    g ≤ xiPoissonCutHeight g := by
  classical
  rw [xiPoissonCutHeight, dif_pos h]
  exact (Classical.choose_spec (exists_min_xiPoissonPoint_re_of_nonempty h)).1

/-- **A bounded vertical line forces the Riemann Hypothesis.** -/
theorem riemannHypothesis_of_xiPoissonTrace_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    RiemannHypothesis := by
  classical
  have hall : ∀ q : XiZeroCopy, (xiPoissonPoint q).im = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q₁, hq₁⟩ := hcon
    obtain ⟨qs, hqs, hmin⟩ := exists_min_xiPoissonPoint_re_of_nonempty
      (s := {q : XiZeroCopy | (xiPoissonPoint q).im ≠ 0}) ⟨q₁, hq₁⟩
    set g : ℝ := (xiPoissonPoint qs).re with hgdef
    have hqscut : qs ∈ xiPoissonCut g := mem_xiPoissonCut.mpr (le_refl _)
    have hgheight : xiPoissonCutHeight g = g :=
      le_antisymm (xiPoissonCutHeight_le hqscut) (le_xiPoissonCutHeight ⟨qs, hqscut⟩)
    -- every copy strictly below `g` lies on the critical line
    have hlow : ∀ q ∈ xiPoissonStrictLower g, (xiPoissonPoint q).im = 0 := by
      intro q hq
      by_contra hne
      have hmem : q ∈ {q : XiZeroCopy | (xiPoissonPoint q).im ≠ 0} := hne
      have hge : g ≤ (xiPoissonPoint q).re := hmin q hmem
      have hlt : (xiPoissonPoint q).re < g := by
        simpa [xiPoissonStrictLower, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
      linarith
    -- the cut trace inherits the line bound
    set C' : ℝ := C + ∑ q ∈ xiPoissonStrictLower g, xiPoissonWeight σ q with hC'
    have hline' : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C' := by
      intro x
      have hre : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by rw [re_vertical]; exact hσ
      have hsplit := xiPoissonTraceC_split_strictLower hre g
      have hcut : xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I) =
          xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I) -
            ∑ q ∈ xiPoissonStrictLower g, xiPoissonTerm ((σ : ℂ) + (x : ℂ) * I) q := by
        rw [hsplit]; ring
      have hlowbound : ‖∑ q ∈ xiPoissonStrictLower g,
          xiPoissonTerm ((σ : ℂ) + (x : ℂ) * I) q‖ ≤
            ∑ q ∈ xiPoissonStrictLower g, xiPoissonWeight σ q := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q hq => ?_)
        rw [norm_xiPoissonTerm, re_vertical, im_vertical, hlow q hq, xiPoissonWeight]
        simp
      rw [hcut]
      refine le_trans (norm_sub_le _ _) ?_
      rw [hC']
      exact add_le_add (hline x) hlowbound
    have hshell : qs ∈ xiPoissonCutBottomShell g :=
      mem_xiPoissonCutBottomShell.mpr ⟨hqscut, by rw [hgheight]⟩
    exact hqs (xiPoissonPoint_im_eq_zero_of_cut_line_bound hσ hgheight hline' qs hshell)
  refine riemannHypothesis_of_xiSpectralPoint_real fun q => ⟨(xiSpectralPoint q).re, ?_⟩
  have him : (xiSpectralPoint q).im = 0 := by
    have h := hall q
    rw [xiPoissonPoint] at h
    split_ifs at h with hc
    · exact h
    · rw [Complex.neg_im, neg_eq_zero] at h
      exact h
  conv_lhs => rw [← Complex.re_add_im (xiSpectralPoint q)]
  rw [him]
  simp

/-- **The vertical-line criterion, both directions.**  The Riemann Hypothesis holds if and only if
the Poisson zero trace is bounded on some vertical line of the open right half-plane. -/
theorem riemannHypothesis_iff_exists_xiPoissonTrace_line_bound :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro hRH
    refine ⟨1, xiPoissonTraceReal 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertical]; exact one_pos
    have h := norm_xiPoissonTraceC_le_of_rh hRH hre
    rwa [re_vertical] at h
  · rintro ⟨σ, C, hσ, hline⟩
    exact riemannHypothesis_of_xiPoissonTrace_line_bound hσ hline

end

end RHTower
