import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated Rolle: a high derivative vanishes between many zeros

If a real function with continuous derivatives of all orders vanishes at
`k + 1` strictly increasing points, then its `k`-th derivative vanishes
somewhere in the closed interval they span.  This is the classical iterated
Rolle theorem, the mean-value engine behind the Lagrange interpolation
remainder: applied to `f - P - λW` (interpolant `P`, nodal polynomial `W`) it
converts nodal agreement into a factorial-divided derivative bound.

The proof inducts on `k`: Rolle produces a zero of the derivative strictly
between each consecutive pair of zeros, and the new zeros are again strictly
increasing.
-/

noncomputable section

namespace HTGeometry

open Set

/-- **Iterated Rolle**: a function with continuous iterated derivatives
vanishing at `k + 1` strictly increasing points has a vanishing `k`-th
derivative in the closed span of the points. -/
theorem exists_iteratedDeriv_eq_zero_of_zeros :
    ∀ (k : ℕ) (g : ℝ → ℝ), (∀ j : ℕ, Continuous (iteratedDeriv j g)) →
    ∀ (pts : Fin (k + 1) → ℝ), StrictMono pts → (∀ i, g (pts i) = 0) →
    ∃ ξ ∈ Set.Icc (pts 0) (pts (Fin.last k)), iteratedDeriv k g ξ = 0 := by
  intro k
  induction k with
  | zero =>
    intro g _hg pts _hmono hz
    exact ⟨pts 0, ⟨le_rfl, le_rfl⟩, by
      rw [iteratedDeriv_zero]
      exact hz 0⟩
  | succ k ih =>
    intro g hg pts hmono hz
    -- Rolle between consecutive zeros
    have hcont : Continuous g := by
      have := hg 0
      rwa [iteratedDeriv_zero] at this
    have hR : ∀ i : Fin (k + 1),
        ∃ c ∈ Ioo (pts i.castSucc) (pts i.succ), deriv g c = 0 := by
      intro i
      apply exists_deriv_eq_zero (hmono Fin.castSucc_lt_succ)
        hcont.continuousOn
      rw [hz i.castSucc, hz i.succ]
    choose qts hqmem hqz using hR
    -- the Rolle points are strictly increasing
    have hqmono : StrictMono qts := by
      intro i j hij
      have h1 : qts i < pts i.succ := (hqmem i).2
      have h2 : pts j.castSucc < qts j := (hqmem j).1
      have h3 : pts i.succ ≤ pts j.castSucc := by
        apply hmono.monotone
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt hij
      linarith
    -- continuity hypotheses descend to the derivative
    have hg' : ∀ j : ℕ, Continuous (iteratedDeriv j (deriv g)) := by
      intro j
      have := hg (j + 1)
      rwa [iteratedDeriv_succ'] at this
    have hz' : ∀ i, deriv g (qts i) = 0 := hqz
    obtain ⟨ξ, hξmem, hξ⟩ :=
      ih (deriv g) hg' qts hqmono hz'
    refine ⟨ξ, ⟨le_of_lt ?_, le_of_lt ?_⟩, ?_⟩
    · calc pts 0 ≤ pts (Fin.castSucc 0) := by
            apply hmono.monotone
            rw [Fin.le_def]
            simp
        _ < qts 0 := (hqmem 0).1
        _ ≤ ξ := hξmem.1
    · calc ξ ≤ qts (Fin.last k) := hξmem.2
        _ < pts (Fin.last k).succ := (hqmem (Fin.last k)).2
        _ ≤ pts (Fin.last (k + 1)) := by
            apply hmono.monotone
            rw [Fin.le_def]
            simp
    · rwa [iteratedDeriv_succ']

end HTGeometry
