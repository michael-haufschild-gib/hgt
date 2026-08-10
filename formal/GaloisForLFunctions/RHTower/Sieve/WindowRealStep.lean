import GaloisForLFunctions.RHTower.Sieve.WindowToLogWindowSum

/-!
# The window sum as a step function of a real starting point

The discrete sum over integer starting points is an integral: extending the window sum to a real
start,

```text
windowReal f ℓ v := ∑_{b ∈ (⌊v⌋, ⌊v⌋+ℓ]} f(b) ,
```

the value is constant on each cell `[z, z+1)`, because the integers in `(v, v+ℓ]` do not move as `v`
crosses no integer.  So `∑_{z ∈ [A,B]}` and `∫_A^{B+1}` of the square agree exactly — the
discrete-to-continuous passage costs nothing in the *additive* variable, and needs no Sobolev
lemma.

The corresponding statement in the logarithmic variable is false at fixed width, because the right
endpoint `e^{u+δ}` sweeps as `u` moves.  That asymmetry is why `logWidth` had to be pinned rather
than fixed, and it is the reason the fibres of the Matomäki–Radziwiłł reduction are better
parametrised multiplicatively: `innerFibre` at `a` is `(x/a, (x/a)(1 + h/√x)]`, whose *relative*
length `h/√x` does not depend on `a`, while its absolute length `h√x/a` does.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The window sum at a real starting point. -/
def windowReal (f : ℕ → ℝ) (ℓ : ℕ) (v : ℝ) : ℝ :=
  ∑ b ∈ Finset.Icc (⌊v⌋₊ + 1) (⌊v⌋₊ + ℓ), f b

/-- **The window sum is constant on each unit cell.** -/
theorem windowReal_eq (f : ℕ → ℝ) (ℓ : ℕ) {z : ℕ} {v : ℝ} (h1 : (z : ℝ) ≤ v)
    (h2 : v < (z : ℝ) + 1) :
    windowReal f ℓ v = ∑ b ∈ Finset.Icc (z + 1) (z + ℓ), f b := by
  have hfloor : ⌊v⌋₊ = z := by
    refine Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg z : (0:ℝ) ≤ (z:ℝ))]) |>.2 ⟨h1, ?_⟩
    linarith
  rw [windowReal, hfloor]

/-- At an integer start the two agree. -/
theorem windowReal_natCast (f : ℕ → ℝ) (ℓ z : ℕ) :
    windowReal f ℓ (z : ℝ) = ∑ b ∈ Finset.Icc (z + 1) (z + ℓ), f b :=
  windowReal_eq f ℓ le_rfl (by linarith)

/-- The squared window sum at a real start, on a cell, is the term of `dyadicMeanSquare`. -/
theorem windowReal_sq_eq (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z : ℕ} {v : ℝ}
    (h1 : (z : ℝ) ≤ v) (h2 : v < (z : ℝ) + 1) :
    (windowReal f ℓ v) ^ 2 = fixedWindowSq f ℓ z := by
  rw [windowReal_eq f ℓ h1 h2, fixedWindowSq_eq f hℓ z]

end RHTower.Sieve

end
