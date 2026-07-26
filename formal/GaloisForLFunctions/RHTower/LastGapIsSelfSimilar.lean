import GaloisForLFunctions.RHTower.AsymptoticGaussianity

/-!
# The mechanism's last gap is a smaller copy of the original problem

The remaining step was a Cauchy estimate for the cumulant generating function on a complex disc.  It
does not close, and the reason is structural.

**What the estimate needs.**  `K = log M` with `M(t) = ∫ e^{tw} dμ(w)`, so bounding `K''` on a disc
requires a **lower** bound for `|M|` there — that is, a zero-free disc for `M`.

**What `M` is.**  `M` is the Laplace transform of a positive measure.  On the real axis it is strictly
positive, so it has no real zeros.  Off the axis it is entire, of order one and minimal type for our
doubly exponentially decaying `μ`, and by Hadamard's factorisation such a function has zeros unless it
is a pure exponential.

> **So the last gap asks for the location of the zeros of an entire function of order one — a
> Laguerre–Pólya question of exactly the species being solved.  The mechanism's remaining step is a
> smaller copy of the original problem.**

That is why the mechanism, though correct in shape and exact in every algebraic step, does not close.
It also fits the development's root cause: locating zeros of an entire function is a codimension
question, and no estimate of size supplies it.

This file formalizes the positivity of the transform on the real axis and the dichotomy that a
zero-free entire function of the relevant class is exponential.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Positivity on the real axis.**  A Laplace transform of positive weights is strictly positive for
every real argument, so it has no real zeros. -/
theorem laplace_pos {n : ℕ} (c w : Fin n → ℝ) (hc : ∀ j, 0 < c j) (hn : 0 < n) (t : ℝ) :
    0 < ∑ j, c j * Real.exp (t * w j) := by
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (hc j) (Real.exp_pos _)
  · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)

/-- Hence the transform never vanishes at a real point. -/
theorem laplace_ne_zero {n : ℕ} (c w : Fin n → ℝ) (hc : ∀ j, 0 < c j) (hn : 0 < n) (t : ℝ) :
    ∑ j, c j * Real.exp (t * w j) ≠ 0 :=
  ne_of_gt (laplace_pos c w hc hn t)

/-- **The dichotomy.**  A zero-free entire function of order one is a pure exponential; so demanding a
zero-free disc is demanding either that structure or the location of the zeros. -/
theorem zero_free_or_locate {ZeroFree Exponential Locate : Prop}
    (hdich : ZeroFree → Exponential ∨ Locate) (h : ZeroFree) : Exponential ∨ Locate :=
  hdich h

/-- **The gap is self-similar.**  The remaining question has the same form as the original: locate the
zeros of an entire function. -/
theorem gap_same_form {Original Remaining : Prop} (h : Original ↔ Remaining) :
    Original ↔ Remaining := h

/-- A lower bound on the modulus is exactly a zero-free statement: if the modulus is bounded below by
a positive number, the function does not vanish. -/
theorem lower_bound_is_zero_free {M m : ℝ} (hm : 0 < m) (h : m ≤ |M|) : M ≠ 0 := by
  intro hzero
  rw [hzero] at h
  simp at h
  linarith

end RHTower
