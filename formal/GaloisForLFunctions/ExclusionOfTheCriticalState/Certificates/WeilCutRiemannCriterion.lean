import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.WeilProbeSignBellman
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.RealProbeNodesDecideTheRiemannHypothesis

/-!
# The Riemann hypothesis as an exact family of positive cut budgets

The integer probe uniqueness theorem turns the finite cut decomposition
into an unconditional equivalence with RH. Every graph uses strictly
positive actual Weil probe entries. Its sharp budget is one quarter of
the aligned quadratic energy. Failure is equivalently witnessed by a
strict finite Bellman residual certificate. This is a characterization,
not a proof that all the budgets hold.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick DecisionBellman
noncomputable section

/-- All safe real probe forms are nonnegative exactly when RH holds. -/
theorem riemannHypothesis_iff_safe_probe_nonnegative :
    RiemannHypothesis ↔ ∀ (n : ℕ) (p c : Fin n → ℝ), 0 ≤ sourceQuadratic n p c := by
  constructor
  · intro h n p c
    exact probe_forms_nonneg_of_riemannHypothesis h (fun i => node (p i)) c
      (fun i => by unfold node; linarith only [abs_nonneg (p i)])
  · intro h
    apply riemannHypothesis_iff_integer_pick_nonneg.mpr
    intro n k c hk
    have hnode (i : Fin n) : node ((k i : ℝ) - 5) = (k i : ℝ) := by
      have hi : (5 : ℝ) ≤ k i := by exact_mod_cast hk i
      rw [node, abs_of_nonneg (sub_nonneg.mpr hi)]
      ring
    have hp (i : Fin n) : (1 / 2 : ℝ) < k i := by
      have hi : (5 : ℝ) ≤ k i := by exact_mod_cast hk i
      linarith only [hi]
    have hs := h n (fun i => (k i : ℝ) - 5) c
    refine hs.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [hnode i, hnode j, bareMixedEnergy_probe (hp i) (hp j)]

/-- RH is equivalent to every positive probe cut staying within its exact capacity. -/
theorem riemannHypothesis_iff_probe_cut_budgets :
    RiemannHypothesis ↔ ∀ (n : ℕ) (p a : Fin n → ℝ) (σ : Fin n → Bool),
      cutWeight p a σ ≤ alignedEnergy p a / 4 := by
  rw [riemannHypothesis_iff_safe_probe_nonnegative]
  constructor
  · intro h n p
    exact (probe_form_nonnegative_iff_cut_budget n p).mp (h n p)
  · intro h n p
    exact (probe_form_nonnegative_iff_cut_budget n p).mpr (h n p)

/-- Failure of RH has an exact finite Bellman certificate in the safe probe family. -/
theorem not_riemannHypothesis_iff_probe_sign_certificate :
    ¬ RiemannHypothesis ↔ ∃ (n : ℕ) (p a : Fin n → ℝ)
      (W : DecisionBellman.Tree (Fin n → Bool) → ℝ),
      W (choices n id) + certificate (signPayoff p a) W (choices n id) < 0 := by
  rw [riemannHypothesis_iff_safe_probe_nonnegative]
  push_neg
  constructor
  · rintro ⟨n, p, c, hc⟩
    obtain ⟨a, W, hW⟩ := (negative_probe_form_iff_sign_certificate n p).mp ⟨c, hc⟩
    exact ⟨n, p, a, W, hW⟩
  · rintro ⟨n, p, a, W, hW⟩
    obtain ⟨c, hc⟩ := (negative_probe_form_iff_sign_certificate n p).mpr ⟨a, W, hW⟩
    exact ⟨n, p, c, hc⟩

#print axioms riemannHypothesis_iff_safe_probe_nonnegative
#print axioms riemannHypothesis_iff_probe_cut_budgets
#print axioms not_riemannHypothesis_iff_probe_sign_certificate
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
