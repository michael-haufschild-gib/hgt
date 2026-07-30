import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Finite certification of bounded-degree operational horizons

A complex polynomial response of degree at most `D` vanishes identically if
and only if it vanishes at any `D + 1` distinct coupling settings.  If a
nonzero response vanishes at the disconnected setting, its first unlocking
order is positive and at most `D`.

This turns the analytic all-jet horizon criterion into a finite exact
protocol whenever a physical response model supplies a degree bound.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A degree-`D` response is identically zero exactly when any `D + 1`
distinct coupling samples all vanish. -/
theorem polynomialResponse_eq_zero_iff_finiteSamples
    {D : ℕ} (p : Polynomial ℂ)
    (sample : Fin (D + 1) → ℂ)
    (hsample : Function.Injective sample)
    (hdegree : p.natDegree ≤ D) :
    p = 0 ↔ ∀ i, p.eval (sample i) = 0 := by
  constructor
  · rintro rfl
    simp
  · intro heval
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      p hsample heval
    simpa using Nat.lt_succ_of_le hdegree

/-- A nonzero bounded-degree response that vanishes at disconnection has a
positive first unlocking order no larger than its certified degree bound. -/
theorem polynomialResponse_unlockingOrder_pos_le
    {D : ℕ} {p : Polynomial ℂ}
    (hp : p ≠ 0)
    (hp0 : p.eval 0 = 0)
    (hdegree : p.natDegree ≤ D) :
    0 < p.rootMultiplicity 0 ∧ p.rootMultiplicity 0 ≤ D := by
  constructor
  · exact (Polynomial.rootMultiplicity_pos hp).2 hp0
  · apply le_trans _ hdegree
    rw [← Polynomial.count_roots]
    exact le_trans
      (Multiset.count_le_card 0 p.roots)
      (Polynomial.card_roots' p)

/-- **Finite bounded-degree horizon certificate.** Any `D + 1` distinct
coupling samples decide exact zero response, and every nonzero response
vanishing at disconnection unlocks at one order in `{1, ..., D}`. -/
theorem boundedDegreeOperationalHorizon_finiteCertificate
    {D : ℕ} (p : Polynomial ℂ)
    (sample : Fin (D + 1) → ℂ)
    (hsample : Function.Injective sample)
    (hdegree : p.natDegree ≤ D) :
    (p = 0 ↔ ∀ i, p.eval (sample i) = 0) ∧
    (p ≠ 0 → p.eval 0 = 0 →
      ∃ b : ℕ, 0 < b ∧ b ≤ D) := by
  refine
    ⟨polynomialResponse_eq_zero_iff_finiteSamples
      p sample hsample hdegree, ?_⟩
  intro hp hp0
  exact
    ⟨p.rootMultiplicity 0,
      polynomialResponse_unlockingOrder_pos_le hp hp0 hdegree⟩

end GaloisForLFunctions.HTGeometry
