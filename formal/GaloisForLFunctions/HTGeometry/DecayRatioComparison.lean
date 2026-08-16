import Mathlib
import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative

/-!
# Comparing decay ratios of two positive solutions

For two positive solutions of the same second-order equation `v'' = P v` the Wronskian
`W = Φ'Ψ − ΦΨ'` is constant, and

```text
(Φ/Ψ)' = W / Ψ² ,
```

so its sign decides which of the two falls faster.  When `W ≤ 0` the quotient is antitone and

```text
Φ(b)/Φ(y) ≤ Ψ(b)/Ψ(y)     for y ≤ b :
```

`Φ` decays at least as fast as `Ψ` across the whole interval.

This is the bridge from a Liouville–Green estimate — which describes one distinguished solution, the
one normalized to the approximant at an endpoint — to an arbitrary solution of the same equation.
Only the *sign* of the Wronskian is usable: on a barrier the two branches differ by a factor
exponential in the action, so a merely small `W` says nothing.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

variable {Φ Φ' Ψ Ψ' P : ℝ → ℝ} {a b : ℝ}

/-- The Wronskian of two solutions of the same linear second-order equation. -/
def solutionWronskian (Φ Φ' Ψ Ψ' : ℝ → ℝ) (y : ℝ) : ℝ := Φ' y * Ψ y - Φ y * Ψ' y

/-- It is constant along the equation. -/
theorem hasDerivAt_solutionWronskian
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (P x * Φ x) x)
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hΨ' : ∀ x, HasDerivAt Ψ' (P x * Ψ x) x) (y : ℝ) :
    HasDerivAt (solutionWronskian Φ Φ' Ψ Ψ') 0 y := by
  have h := ((hΦ' y).mul (hΨ y)).sub ((hΦ y).mul (hΨ' y))
  refine h.congr_deriv ?_
  ring

theorem solutionWronskian_const
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (P x * Φ x) x)
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hΨ' : ∀ x, HasDerivAt Ψ' (P x * Ψ x) x) (y z : ℝ) :
    solutionWronskian Φ Φ' Ψ Ψ' y = solutionWronskian Φ Φ' Ψ Ψ' z := by
  have hconst : ∀ x : ℝ, HasDerivAt (solutionWronskian Φ Φ' Ψ Ψ') ((fun _ : ℝ => (0 : ℝ)) x) x :=
    hasDerivAt_solutionWronskian hΦ hΦ' hΨ hΨ'
  rcases le_total y z with h | h
  · have h1 := le_of_hasDerivAt_nonneg (F := solutionWronskian Φ Φ' Ψ Ψ')
      (F' := fun _ => (0 : ℝ)) h (fun t _ => hconst t) (fun _ _ => le_rfl)
    have h2 := le_of_hasDerivAt_nonneg (F := fun t => -solutionWronskian Φ Φ' Ψ Ψ' t)
      (F' := fun _ => (0 : ℝ)) h (fun t _ => (hconst t).neg.congr_deriv (by ring))
      (fun _ _ => le_rfl)
    linarith
  · have h1 := le_of_hasDerivAt_nonneg (F := solutionWronskian Φ Φ' Ψ Ψ')
      (F' := fun _ => (0 : ℝ)) h (fun t _ => hconst t) (fun _ _ => le_rfl)
    have h2 := le_of_hasDerivAt_nonneg (F := fun t => -solutionWronskian Φ Φ' Ψ Ψ' t)
      (F' := fun _ => (0 : ℝ)) h (fun t _ => (hconst t).neg.congr_deriv (by ring))
      (fun _ _ => le_rfl)
    linarith

/-- **The Wronskian sign is a comparison of logarithmic derivatives.** -/
theorem solutionWronskian_nonpos_iff {y : ℝ} (hΦ : 0 < Φ y) (hΨ : 0 < Ψ y) :
    solutionWronskian Φ Φ' Ψ Ψ' y ≤ 0 ↔ Φ' y / Φ y ≤ Ψ' y / Ψ y := by
  rw [solutionWronskian, div_le_div_iff₀ hΦ hΨ]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **Decay comparison.**  A nonpositive Wronskian makes the first solution fall at least as fast as
the second, across the whole interval. -/
theorem ratio_le_of_solutionWronskian_nonpos (hab : a ≤ b)
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : ∀ x, HasDerivAt Φ' (P x * Φ x) x)
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hΨ' : ∀ x, HasDerivAt Ψ' (P x * Ψ x) x)
    (hΦpos : ∀ x ∈ Icc a b, 0 < Φ x) (hΨpos : ∀ x ∈ Icc a b, 0 < Ψ x)
    (hW : solutionWronskian Φ Φ' Ψ Ψ' b ≤ 0) :
    Φ b / Φ a ≤ Ψ b / Ψ a := by
  -- the quotient is antitone
  have hQd : ∀ x ∈ Icc a b, HasDerivAt (fun t => Φ t / Ψ t)
      ((Φ' x * Ψ x - Φ x * Ψ' x) / Ψ x ^ 2) x := by
    intro x hx
    exact HasDerivAt.fun_div (hΦ x) (hΨ x) (hΨpos x hx).ne'
  have hanti : ∀ x ∈ Icc a b, 0 ≤ -((Φ' x * Ψ x - Φ x * Ψ' x) / Ψ x ^ 2) := by
    intro x hx
    have hWx : solutionWronskian Φ Φ' Ψ Ψ' x ≤ 0 := by
      rw [solutionWronskian_const hΦ hΦ' hΨ hΨ' x b]
      exact hW
    rw [solutionWronskian] at hWx
    have hpos : (0 : ℝ) < Ψ x ^ 2 := by
      have := hΨpos x hx
      positivity
    have : (Φ' x * Ψ x - Φ x * Ψ' x) / Ψ x ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hWx hpos.le
    linarith
  have hmono := le_of_hasDerivAt_nonneg (F := fun t => -(Φ t / Ψ t))
    (F' := fun x => -((Φ' x * Ψ x - Φ x * Ψ' x) / Ψ x ^ 2)) hab
    (fun x hx => (hQd x hx).neg) hanti
  have hstep : Φ b / Ψ b ≤ Φ a / Ψ a := by linarith
  have hΦa := hΦpos a (left_mem_Icc.2 hab)
  have hΨa := hΨpos a (left_mem_Icc.2 hab)
  have hΨb := hΨpos b (right_mem_Icc.2 hab)
  rw [div_le_div_iff₀ hΨb hΨa] at hstep
  rw [div_le_div_iff₀ hΦa hΨa]
  nlinarith [hstep, hΦa, hΨa, hΨb]

end GaloisForLFunctions.HTGeometry
