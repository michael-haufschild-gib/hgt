import Mathlib
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Entire functions have entire differential-polynomial evaluations

For an entire function every iterated derivative is entire (complex differentiability
propagates through `deriv` by analyticity), and hence every differential-polynomial
evaluation `z ↦ P(z, f(z), f'(z), …, f⁽ⁿ⁾(z))` is entire
(`differentiable_jetEval`), in particular analytic and continuous
(`analyticOnNhd_jetEval`).  This is the analytic substrate of the jet-relation loci: the set
where a differential polynomial vanishes on the jets of an entire function is the zero set of
an entire function — closed, and either everything or discrete.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- Iterated derivatives of an entire function are entire. -/
theorem differentiable_iteratedDeriv_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) : Differentiable ℂ (iteratedDeriv j f) := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have h1 : AnalyticOnNhd ℂ (iteratedDeriv j f) Set.univ :=
      ih.differentiableOn.analyticOnNhd isOpen_univ
    exact fun z => ((h1.deriv) z (Set.mem_univ z)).differentiableAt

/-- **Differential-polynomial evaluations of entire functions are entire.** -/
theorem differentiable_jetEval {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    Differentiable ℂ (fun z => MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [eval_C]
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    refine hp.mul ?_
    induction i using Fin.cases with
    | zero => simp [Fin.cons_zero]
    | succ j =>
      simpa [Fin.cons_succ] using differentiable_iteratedDeriv_of_entire hf (j : ℕ)

/-- Differential-polynomial evaluations of entire functions are analytic everywhere. -/
theorem analyticOnNhd_jetEval {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P) Set.univ :=
  (differentiable_jetEval hf n P).differentiableOn.analyticOnNhd isOpen_univ

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Relation-locus dichotomy.**  For an entire function, a differential-polynomial relation
on its jets either holds identically or holds only on a set of isolated points: no jet
relation of an entire function can accumulate without holding everywhere. -/
theorem jetEval_identically_zero_or_isolated {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (∀ z, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0)
      ∨ ∀ z₀, ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0) := by
  by_cases h : ∃ z₀, ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0
  · left
    obtain ⟨z₀, hz₀⟩ := h
    have hEq := (analyticOnNhd_jetEval hf n P).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z₀) hz₀
    intro z
    exact hEq (Set.mem_univ z)
  · right
    push Not at h
    exact fun z₀ => Filter.not_frequently.mpr (h z₀)

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- **Hypertranscendental entire functions have isolated relation loci**: every nonzero
differential polynomial vanishes on the jets of such a function only at isolated points —
identical vanishing would be a differential-algebraic relation. -/
theorem Hypertranscendental.jetEval_isolated {f : ℂ → ℂ} (hht : Hypertranscendental f)
    (hf : Differentiable ℂ f) {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    ∀ z₀, ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0) := by
  rcases jetEval_identically_zero_or_isolated hf n P with h | h
  · exact absurd ⟨n, P, hP, h⟩ hht
  · exact h

end GaloisForLFunctions
