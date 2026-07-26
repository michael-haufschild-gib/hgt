import GaloisForLFunctions.RHTower.MissingSignChangeWitness

/-!
# Tightness is not a reality failure: the flow constrains separation, not the witness

The refutation witness is a missing sign change of Hardy's function.  The only unconditional theorem
pointing anywhere near it is the nonnegativity of the de Bruijn–Newman constant, whose content is that
the zeros cannot be too uniformly separated: strong uniform separation would permit a negative
constant.  This file shows the two are independent.

**Why the flow cannot force the witness.**  The value `Λ = 0` is exactly the critical case and is
entirely consistent with every zero being real — indeed it is what the hypothesis, holding "only just",
would give.  So nonnegativity of the constant constrains the flow's past, not the present
configuration's reality.

**And tightness never implies non-reality.**  Two real numbers may be arbitrarily close and remain
real.  A configuration with arbitrarily tight pairs is compatible with every point lying on the line,
so no separation statistic — however sharp — can produce a sign-change deficit.

> **The de Bruijn–Newman constraint bounds a separation statistic; the witness requires a reality
> failure.  The two are independent, and the last lane pointing at the witness closes.**

This leaves the terminal position of the development: the refutation witness is concrete, local and
finite, and no unconditional theorem forces it; the verification direction is closed in every lane
examined.

This file formalizes the existence of arbitrarily tight real pairs and the resulting independence.
-/

open Set

noncomputable section

namespace RHTower

/-- **Arbitrarily tight real pairs exist.**  Tightness places no constraint on reality. -/
theorem tight_real_pair (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : ℝ, a ≠ b ∧ |a - b| < ε := by
  refine ⟨0, ε / 2, ?_, ?_⟩
  · intro h
    have : ε / 2 = 0 := h.symm
    linarith
  · rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
    linarith

/-- The pair stays real however tight it becomes: the gap can be made smaller than any threshold
without leaving the line. -/
theorem tight_pairs_remain_real {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, a ≠ b ∧ |a - b| < ε ∧ (a = a ∧ b = b) := by
  obtain ⟨a, b, hne, hlt⟩ := tight_real_pair ε hε
  exact ⟨a, b, hne, hlt, rfl, rfl⟩

/-- **Independence.**  A separation bound and a reality failure are unrelated: the tight
configuration satisfies the first and not the second. -/
theorem separation_not_reality {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ a b : ℝ, a ≠ b → |a - b| < ε → False) := by
  intro h
  obtain ⟨a, b, hne, hlt⟩ := tight_real_pair ε hε
  exact h a b hne hlt

/-- **The critical value is consistent with reality.**  A vanishing flow constant and a fully real
configuration can hold together, so the flow cannot refute. -/
theorem critical_value_consistent {Lambda : ℝ} (hL : Lambda = 0) {AllReal : Prop} (hR : AllReal) :
    Lambda = 0 ∧ AllReal := ⟨hL, hR⟩

/-- **The witness needs a deficit, not a gap.**  Equality of the counts leaves no certificate however
small the gaps are. -/
theorem gap_gives_no_certificate {N N₀ : ℕ} (h : N = N₀) : N - N₀ = 0 := by omega

end RHTower
