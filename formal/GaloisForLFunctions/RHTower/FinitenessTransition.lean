import GaloisForLFunctions.RHTower.TouchingComparison

/-!
# Conditional bookkeeping for an extended-natural count

Every declaration below concerns an arbitrary `M : ℝ → ℕ∞`. Monotonicity is supplied as `hsturm`,
and the finite-count branch is supplied as `hcollide`. The dichotomy combines those assumptions;
it does not prove them for a zero count. Likewise, `transition_at_zero` takes both one-sided
conclusions as premises, and `criterion_vacuous` assumes infinitude at negative times.

This module defines neither the de Bruijn–Newman flow nor its non-real zero count. It supplies no
Sturm persistence theorem, small-gap collision estimate, or Ki–Kim–Lee theorem for that flow.
Its declarations therefore do not establish an unconditional finiteness transition or retire a
negative-time falsification route. The historical name `count_zero_of_rh` also uses only the
abstract assumption `M 0 = 0`, not the proposition `RiemannHypothesis`.
-/

open Set

noncomputable section

namespace RHTower

/-- Specialize assumed antitonicity of an arbitrary count to times `t ≤ 0`. -/
theorem nonreal_count_mono {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    {t : ℝ} (ht : t ≤ 0) : M 0 ≤ M t := hsturm ht

/-- An antitone extended-natural count infinite at zero is infinite at every nonpositive time. -/
theorem caseA {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    (h0 : M 0 = ⊤) {t : ℝ} (ht : t ≤ 0) : M t = ⊤ :=
  top_unique (h0 ▸ nonreal_count_mono hsturm ht)

/-- Apply the assumed finite-count implication; no collision estimate is proved here. -/
theorem caseB {M : ℝ → ℕ∞} {t : ℝ}
    (hcollide : M 0 ≠ ⊤ → M t = ⊤) (h0 : M 0 ≠ ⊤) : M t = ⊤ := hcollide h0

/-- Combine assumed antitonicity and the assumed finite-count implication by a dichotomy at zero. -/
theorem infinite_of_neg {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    {t : ℝ} (ht : t < 0) (hcollide : M 0 ≠ ⊤ → M t = ⊤) : M t = ⊤ := by
  by_cases h0 : M 0 = ⊤
  · exact caseA hsturm h0 (le_of_lt ht)
  · exact hcollide h0

/-- Package two assumed one-sided count statements at a given time. -/
theorem transition_at_zero {M : ℝ → ℕ∞}
    (hpos : ∀ t : ℝ, 0 < t → M t ≠ ⊤) (hneg : ∀ t : ℝ, t < 0 → M t = ⊤)
    (t : ℝ) : (0 < t → M t ≠ ⊤) ∧ (t < 0 → M t = ⊤) :=
  ⟨hpos t, hneg t⟩

/-- Assumed infinitude at every negative time contradicts finiteness at one such time. -/
theorem criterion_vacuous {M : ℝ → ℕ∞} (hneg : ∀ t : ℝ, t < 0 → M t = ⊤)
    {t : ℝ} (ht : t < 0) (hfin : M t ≠ ⊤) : False := hfin (hneg t ht)

/-- An arbitrary extended-natural count equal to zero at time zero is not infinite there. -/
theorem count_zero_of_rh {M : ℝ → ℕ∞} (hRH : M 0 = 0) : M 0 ≠ ⊤ := by
  rw [hRH]; exact fun h => by simp at h

end RHTower
