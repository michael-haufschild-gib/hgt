import Mathlib

/-!
# A real window is an integer window

For a real start `x ≥ 0` the integers in `(x, x+L]` are exactly the integers in `(⌊x⌋, ⌊x⌋+L]`:

`n > x ↔ ⌊x⌋ < n` and `n ≤ x + L ↔ n ≤ ⌊x+L⌋ = ⌊x⌋ + L`.

So a short-interval sum with a real start is constant on each interval `[k, k+1)` and equals the
integer-start sum there.  This is the bridge between a mean square taken as an integral over real
starts and the discrete variance of the preceding modules.
-/

namespace RHTower.Sieve

open Finset

/-- The integers of `(x, x+L]` below a cutoff. -/
noncomputable def realWindow (x : ℝ) (L M : ℕ) : Finset ℕ :=
  (Finset.range M).filter (fun n => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L)

/-- **A real window is the integer window at `⌊x⌋`.** -/
theorem realWindow_eq_Ioc {x : ℝ} (hx : 0 ≤ x) {L M : ℕ} (hM : ⌊x⌋₊ + L < M) :
    realWindow x L M = Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + L) := by
  classical
  ext n
  simp only [realWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨(Nat.floor_lt hx).mpr h1, ?_⟩
    have h3 : n ≤ ⌊x + (L : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast h2)
    rwa [Nat.floor_add_natCast hx] at h3
  · rintro ⟨h1, h2⟩
    have h1' : x < (n : ℝ) := (Nat.floor_lt hx).mp h1
    have h2' : (n : ℝ) ≤ x + L := by
      have : n ≤ ⌊x + (L : ℝ)⌋₊ := by rwa [Nat.floor_add_natCast hx]
      exact Nat.floor_le (by positivity) |>.trans' (by exact_mod_cast Nat.cast_le.mpr this) |>.trans
        (le_refl _)
    exact ⟨by omega, h1', h2'⟩

/-- The real-start window sum is the integer-start window sum at `⌊x⌋`. -/
theorem sum_realWindow_eq {α : Type*} [AddCommMonoid α] (a : ℕ → α) {x : ℝ} (hx : 0 ≤ x)
    {L M : ℕ} (hM : ⌊x⌋₊ + L < M) :
    ∑ n ∈ realWindow x L M, a n = ∑ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + L), a n := by
  rw [realWindow_eq_Ioc hx hM]

end RHTower.Sieve
