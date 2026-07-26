import GaloisForLFunctions.RHTower.SuzukiRectangularWardDefectBoundedness

/-!
# The source-energy freedom in the Ward-defect criterion is vacuous, and the prime second
# difference is a tent-weighted Chebyshev window

Two exact facts about the rectangular Ward criterion.

## The freedom adds nothing

The criterion asks for *some* nonnegative source energy `E` leaving the defect
`C(n) - E(n)` eventually bounded below.  Subtracting a nonnegative quantity can only lower a
function, so `C - E ≤ C`: a lower bound for `C - E` is a lower bound for `C`, and conversely `E = 0`
is always admissible.  Hence

```text
(∃ E ≥ 0, C - E eventually bounded below)   ⟺   C eventually bounded below ,
```

and `E = 0` is optimal.  The weakening is genuine against *exact* source isometry, but it is not a
weakening of the plain curvature criterion — it is literally the same statement.  Effort belongs on
bounding the curvature itself.

## What the prime side contributes, exactly

The central prime–arch form writes `2·Re(screw divisor)(t)` as `-2·P(t) + A(t)` with

```text
P(t) = Σ_k (Λ(k)/√k)·max(0, t - log k) ,
```

a sum of **ramps**.  The window curvature is the second difference at step `L`, and the second
difference of a ramp is a **tent**:

```text
max(0,u) - 2max(0,u-L) + max(0,u-2L) = max(0, L - |u - L|) ,
```

nonnegative, supported exactly on `[0,2L]`, of height `L` at `u = L`.  So the prime contribution to
the window curvature is

```text
-2 Σ_{log k ∈ [x-2L, x]} (Λ(k)/√k) · tent_L(x - log k) ≤ 0 ,
```

a **locally finite, sign-definite, tent-weighted Chebyshev window**: only the `k` with
`e^{x-2L} ≤ k ≤ e^x` contribute.  The tent is the autocorrelation of the indicator of `[0,L]`, which
is why this is the Weil form of a rectangular test function.

Consequently a lower bound for the curvature is exactly the statement that the archimedean second
difference dominates that windowed prime sum up to a constant.  That is where the difficulty sits, and
the source-energy device does not move it.

This file formalizes the vacuity of the freedom and the ramp-to-tent identity.
-/

open Real

noncomputable section

namespace RHTower

/-- **Subtracting a nonnegative energy only lowers the defect.** -/
theorem defect_le_curvature {C E : ℕ → ℝ} (hE : ∀ n, 0 ≤ E n) (n : ℕ) :
    C n - E n ≤ C n := by
  have := hE n; linarith

/-- **The freedom is vacuous, forward direction.**  A lower bound for the defect is a lower bound for
the curvature itself. -/
theorem curvature_bddBelow_of_defect {C E : ℕ → ℝ} (hE : ∀ n, 0 ≤ E n)
    {B : ℝ} {N₀ : ℕ} (h : ∀ n, N₀ ≤ n → B ≤ C n - E n) :
    ∀ n, N₀ ≤ n → B ≤ C n := fun n hn =>
  le_trans (h n hn) (defect_le_curvature hE n)

/-- **The freedom is vacuous, converse direction.**  The zero energy is admissible, so a lower bound
for the curvature is a lower bound for the defect with `E = 0`. -/
theorem defect_bddBelow_of_curvature {C : ℕ → ℝ} {B : ℝ} {N₀ : ℕ}
    (h : ∀ n, N₀ ≤ n → B ≤ C n) :
    (∀ n : ℕ, (0 : ℝ) ≤ (0 : ℕ → ℝ) n) ∧
      ∀ n : ℕ, N₀ ≤ n → B ≤ C n - (0 : ℕ → ℝ) n :=
  ⟨fun _ => le_refl 0, fun n hn => by simpa using h n hn⟩

/-- The tent of half-width `L`: the second difference of a ramp. -/
def tent (L u : ℝ) : ℝ := max 0 (L - |u - L|)

/-- **Ramp to tent.**  The step-`L` second difference of the ramp `max(0,·)` is the tent. -/
theorem ramp_secondDifference (L u : ℝ) (hL : 0 ≤ L) :
    max 0 u - 2 * max 0 (u - L) + max 0 (u - 2 * L) = tent L u := by
  unfold tent
  rcases le_or_gt u 0 with h0 | h0
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_left (by linarith)]
    rw [abs_of_nonpos (by linarith : u - L ≤ 0)]
    rw [max_eq_left (by linarith)]
    ring
  · rcases le_or_gt u L with h1 | h1
    · rw [max_eq_right (le_of_lt h0), max_eq_left (by linarith), max_eq_left (by linarith)]
      rw [abs_of_nonpos (by linarith : u - L ≤ 0)]
      rw [max_eq_right (by linarith)]
      ring
    · rcases le_or_gt u (2 * L) with h2 | h2
      · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
        rw [abs_of_nonneg (by linarith : 0 ≤ u - L)]
        rw [max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
        rw [abs_of_nonneg (by linarith : 0 ≤ u - L)]
        rw [max_eq_left (by linarith)]
        ring

/-- The tent is nonnegative. -/
theorem tent_nonneg (L u : ℝ) : 0 ≤ tent L u := le_max_left _ _

/-- The tent vanishes outside `[0, 2L]`: the prime window is locally finite. -/
theorem tent_eq_zero_of_le_zero {L u : ℝ} (hL : 0 ≤ L) (hu : u ≤ 0) : tent L u = 0 := by
  unfold tent
  rw [abs_of_nonpos (by linarith : u - L ≤ 0)]
  exact max_eq_left (by linarith)

theorem tent_eq_zero_of_ge {L u : ℝ} (hL : 0 ≤ L) (hu : 2 * L ≤ u) : tent L u = 0 := by
  unfold tent
  rw [abs_of_nonneg (by linarith : 0 ≤ u - L)]
  exact max_eq_left (by linarith)

/-- The tent peaks at `u = L` with height `L`. -/
theorem tent_peak {L : ℝ} (hL : 0 ≤ L) : tent L L = L := by
  unfold tent
  simp [abs_zero, max_eq_right hL]

/-- **The sign of the prime contribution.**  Each prime term enters the window curvature with a
nonpositive coefficient, since the tent and the von Mangoldt weight are nonnegative. -/
theorem prime_term_nonpos {L u w : ℝ} (hw : 0 ≤ w) :
    -2 * (w * tent L u) ≤ 0 := by
  have := tent_nonneg L u
  nlinarith [hw, this]

end RHTower
