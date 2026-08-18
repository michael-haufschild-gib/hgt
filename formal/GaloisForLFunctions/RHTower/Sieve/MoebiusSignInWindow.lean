import GaloisForLFunctions.RHTower.Sieve.RouteEMoebiusUnconditional
import GaloisForLFunctions.RHTower.Sieve.CoprimeProductSign

/-!
# Integers of a prescribed Möbius sign in a short interval
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- A coprime sign-class pair produces an integer of that Möbius sign inside the window. -/
theorem exists_moebius_eq_of_signClass_nonempty {x h : ℝ} {s : ℤ}
    (hne : (coprimeSignClass x h s).Nonempty) :
    ∃ m : ℕ, x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + h * Real.sqrt x ∧ moebius m = s := by
  classical
  obtain ⟨q, hq⟩ := hne
  rw [coprimeSignClass, Finset.mem_filter] at hq
  obtain ⟨hbal, hsign, hcop⟩ := hq
  rw [balancedPairs, Finset.mem_filter] at hbal
  refine ⟨q.1 * q.2, ?_, ?_, ?_⟩
  · exact_mod_cast hbal.2.1
  · exact_mod_cast hbal.2.2.1
  · rw [isMultiplicative_moebius.map_mul_of_coprime hcop]
    exact hsign

/-- **Both Möbius sign classes are eventually occupied in the short interval
`[x, x + √x·exp((log x)^{99/100})]`.**  Unconditional. -/
theorem exists_moebius_eq_in_window {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x : ℝ in atTop, ∃ m : ℕ,
      x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + cardLength (99 / 100) x * Real.sqrt x
        ∧ moebius m = s := by
  filter_upwards [route_e_signClass_nonempty_unconditional hs] with x hx
  exact exists_moebius_eq_of_signClass_nonempty hx

/-- **Both signs occur, in the same interval.** -/
theorem exists_moebius_pos_and_neg_in_window :
    ∀ᶠ x : ℝ in atTop,
      (∃ m : ℕ, x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + cardLength (99 / 100) x * Real.sqrt x
        ∧ moebius m = 1)
      ∧ (∃ m : ℕ, x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + cardLength (99 / 100) x * Real.sqrt x
        ∧ moebius m = -1) := by
  filter_upwards [exists_moebius_eq_in_window (s := 1) (Or.inl rfl),
    exists_moebius_eq_in_window (s := -1) (Or.inr rfl)] with x h1 h2
  exact ⟨h1, h2⟩

end RHTower.Sieve
