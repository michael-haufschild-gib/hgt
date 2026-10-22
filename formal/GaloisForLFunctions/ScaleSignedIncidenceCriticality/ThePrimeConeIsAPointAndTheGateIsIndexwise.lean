import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeSideScaleUnitAndItsUniversalFloor

/-!
# The prime cone is a point, and its gate is indexwise

The prime-window gate said that no bounded radius resolves the full Weil cone. It did not say what
*would* be needed. The answer follows from a rigidity the cone already has but which had not been
used as an admissibility statement: the cone is a single point.

A weight in the full Weil cone agrees with the von Mangoldt weight at every index `n ≥ 2`
(`eq_vonMangoldt_of_weilPositiveFull`), so any two members of the cone coincide there
(`eq_of_weilPositiveFull`) and *every* weight differing from `Λ` at one single index lies outside
it (`not_weilPositiveFull_of_ne_at_index`) — unconditionally, with no appeal to RH.

Therefore (`resolves_forces_index_separation`) under RH a reading that resolves cone membership must
separate `Λ` from each of its **single-index perturbations**: for every `n ≥ 2` and every value
`c ≠ Λ n`,

`r (Function.update Λ n c) ≠ r Λ`.

That is the complete list of separations the prime side demands, and it is indexed by one prime
power and one amplitude. `thePrimeSideGateIsIndexwise` collects it. Two uses:

* it is checkable — a proposed mechanism is tested one index at a time, no countermodel needed;
* it explains the radius gate rather than restating it. A radius-`R` reading is a function of the
  indices below `e^{2R}` (`radiusReading_congr_of_agree_below`), so it fails the separation at
  every index above that, and `not_resolves_of_index_blind` turns *any* index-blindness, not only a
  radius truncation, into failure.

The contrast with the zero side is the content. There the positive data form a vast family — every
on-line configuration — and a reading need only separate that family from its complement. Here the
positive datum is unique, so the gate is identification of one point, index by index.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The cone is a point -/

/-- **A weight in the cone is the von Mangoldt weight.** -/
theorem eq_vonMangoldt_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n : ℕ, 2 ≤ n → lam n = (ArithmeticFunction.vonMangoldt n : ℝ) :=
  (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW).2

/-- **Rigidity of the cone.** Any two members agree at every index that the Weil functional sees. -/
theorem eq_of_weilPositiveFull {lam lam' : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hW' : WeilPositiveFull lam') : ∀ n : ℕ, 2 ≤ n → lam n = lam' n := fun n hn =>
  (eq_vonMangoldt_of_weilPositiveFull hW n hn).trans
    (eq_vonMangoldt_of_weilPositiveFull hW' n hn).symm

/-- **One index suffices to leave the cone.** -/
theorem not_weilPositiveFull_of_ne_at_index {lam : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hne : lam n ≠ (ArithmeticFunction.vonMangoldt n : ℝ)) : ¬ WeilPositiveFull lam := fun hW =>
  hne (eq_vonMangoldt_of_weilPositiveFull hW n hn)

/-! ### 2. The indexwise gate -/

/-- The single-index perturbation of the von Mangoldt weight. -/
noncomputable def perturbVonMangoldt (n : ℕ) (c : ℝ) : ℕ → ℝ :=
  Function.update (fun m => (ArithmeticFunction.vonMangoldt m : ℝ)) n c

theorem perturbVonMangoldt_self (n : ℕ) (c : ℝ) : perturbVonMangoldt n c n = c := by
  simp [perturbVonMangoldt]

/-- A single-index perturbation at a nontrivial amplitude lies outside the cone. -/
theorem not_weilPositiveFull_perturbVonMangoldt {n : ℕ} (hn : 2 ≤ n) {c : ℝ}
    (hc : c ≠ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ¬ WeilPositiveFull (perturbVonMangoldt n c) :=
  not_weilPositiveFull_of_ne_at_index hn (by rw [perturbVonMangoldt_self]; exact hc)

/-- **The indexwise gate.** Under RH a reading that resolves cone membership separates `Λ` from
every single-index perturbation of it. -/
theorem resolves_forces_index_separation (hRH : RiemannHypothesis) {O : Type*}
    {r : (ℕ → ℝ) → O} (hres : Resolves r WeilPositiveFull) {n : ℕ} (hn : 2 ≤ n) {c : ℝ}
    (hc : c ≠ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    r (perturbVonMangoldt n c) ≠ (r fun m => (ArithmeticFunction.vonMangoldt m : ℝ)) := by
  intro heq
  have hpos : WeilPositiveFull (fun m => (ArithmeticFunction.vonMangoldt m : ℝ)) :=
    WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
      ⟨hRH, fun _ _ => rfl⟩
  exact not_weilPositiveFull_perturbVonMangoldt hn hc ((hres _ _ heq).mpr hpos)

/-- **Index blindness is failure.** A reading that cannot see the index `n` does not resolve the
cone, whatever else it reads: this covers radius truncations, tail averages and any statistic that
ignores one prime power. -/
theorem not_resolves_of_index_blind (hRH : RiemannHypothesis) {O : Type*} {r : (ℕ → ℝ) → O}
    {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc : c ≠ (ArithmeticFunction.vonMangoldt n : ℝ))
    (hblind : r (perturbVonMangoldt n c) =
      (r fun m => (ArithmeticFunction.vonMangoldt m : ℝ))) :
    ¬ Resolves r WeilPositiveFull := fun hres =>
  resolves_forces_index_separation hRH hres hn hc hblind

/-! ### 3. The gate in one statement -/

/-- **The prime-side gate is indexwise.** The cone is rigid, one index leaves it, and under RH an
admissible reading must separate `Λ` from each single-index perturbation — one prime power and one
amplitude at a time. -/
theorem thePrimeSideGateIsIndexwise (hRH : RiemannHypothesis) :
    (∀ lam lam' : ℕ → ℝ, WeilPositiveFull lam → WeilPositiveFull lam' →
        ∀ n : ℕ, 2 ≤ n → lam n = lam' n) ∧
      (∀ (n : ℕ) (c : ℝ), 2 ≤ n → c ≠ (ArithmeticFunction.vonMangoldt n : ℝ) →
        ¬ WeilPositiveFull (perturbVonMangoldt n c)) ∧
      ∀ (O : Type) (r : (ℕ → ℝ) → O), Resolves r WeilPositiveFull →
        ∀ (n : ℕ) (c : ℝ), 2 ≤ n → c ≠ (ArithmeticFunction.vonMangoldt n : ℝ) →
          r (perturbVonMangoldt n c) ≠ (r fun m => (ArithmeticFunction.vonMangoldt m : ℝ)) :=
  ⟨fun _ _ hW hW' => eq_of_weilPositiveFull hW hW',
    fun _ _ hn hc => not_weilPositiveFull_perturbVonMangoldt hn hc,
    fun _ _ hres _ _ hn hc => resolves_forces_index_separation hRH hres hn hc⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
