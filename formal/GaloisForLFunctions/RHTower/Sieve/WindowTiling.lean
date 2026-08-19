import Mathlib

/-!
# Tiling a window by consecutive sub-windows

A lower bound valid on every sub-window of a fixed length adds up over a tiling: the sub-windows
`(X + j·h, X + (j+1)·h]`, `j < N`, are disjoint and their union is `(X, X + N·h]`.  This is what
converts a marker construction that produces one window length into a bound for the longer window a
card prescribes.
-/

namespace RHTower.Sieve

open Finset

/-- **Consecutive half-open blocks tile a window.** -/
theorem card_filter_Ioc_tile {N h X : ℕ} (p : ℕ → Prop) [DecidablePred p] {c : ℝ}
    (hc : ∀ j, j < N → c ≤ ((((Finset.Ioc (X + j * h) (X + j * h + h)).filter p).card : ℕ) : ℝ)) :
    (N : ℝ) * c ≤ ((((Finset.Ioc X (X + N * h)).filter p).card : ℕ) : ℝ) := by
  classical
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep : X + N * h + h = X + (N + 1) * h := by ring
      have hle1 : X ≤ X + N * h := by omega
      have hle2 : X + N * h ≤ X + (N + 1) * h := by
        have : N * h ≤ (N + 1) * h := Nat.mul_le_mul_right h (by omega)
        omega
      have hunion : Finset.Ioc X (X + N * h) ∪ Finset.Ioc (X + N * h) (X + (N + 1) * h)
          = Finset.Ioc X (X + (N + 1) * h) := Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2
      have hdisj : Disjoint (Finset.Ioc X (X + N * h))
          (Finset.Ioc (X + N * h) (X + (N + 1) * h)) := by
        refine Finset.disjoint_left.2 fun a ha hb => ?_
        rw [Finset.mem_Ioc] at ha hb
        omega
      have hfilterunion : ((Finset.Ioc X (X + (N + 1) * h)).filter p)
          = ((Finset.Ioc X (X + N * h)).filter p)
            ∪ ((Finset.Ioc (X + N * h) (X + (N + 1) * h)).filter p) := by
        rw [← hunion, Finset.filter_union]
      have hdisjf : Disjoint ((Finset.Ioc X (X + N * h)).filter p)
          ((Finset.Ioc (X + N * h) (X + (N + 1) * h)).filter p) :=
        Finset.disjoint_filter_filter hdisj
      have hcard : ((Finset.Ioc X (X + (N + 1) * h)).filter p).card
          = ((Finset.Ioc X (X + N * h)).filter p).card
            + ((Finset.Ioc (X + N * h) (X + (N + 1) * h)).filter p).card := by
        rw [hfilterunion, Finset.card_union_of_disjoint hdisjf]
      have hlast : c ≤ ((((Finset.Ioc (X + N * h) (X + (N + 1) * h)).filter p).card : ℕ) : ℝ) := by
        have := hc N (by omega)
        rwa [hstep] at this
      have hih := ih (fun j hj => hc j (by omega))
      have hcardR : ((((Finset.Ioc X (X + (N + 1) * h)).filter p).card : ℕ) : ℝ)
          = ((((Finset.Ioc X (X + N * h)).filter p).card : ℕ) : ℝ)
            + ((((Finset.Ioc (X + N * h) (X + (N + 1) * h)).filter p).card : ℕ) : ℝ) := by
        rw [hcard]
        push_cast
        ring
      rw [hcardR]
      push_cast
      linarith [hih, hlast]

end RHTower.Sieve
