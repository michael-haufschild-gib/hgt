import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AliasingIsFreeInsideAnyBackground

/-!
# The free regime ends exactly at the sub-lattice's Nyquist aperture

`AliasingIsFreeInsideAnyBackground` shows an off-line sub-lattice hides at no cost below half its
own spacing parameter, because the lattice ground energy at aliasing index one is zero. This module
shows the regime is sharp: at index two and beyond the ground energy is **strictly** negative, so
past `ℓ/2` on-line mass is strictly required, not merely allowed.

The mechanism is the strict superadditivity of `sinh`
(`natCast_mul_sinh_lt_sinh_of_two_le`): for `x > 0` and `n ≥ 2`,

`n sinh x < sinh (n x)`,

by induction from `sinh 2x = 2 sinh x cosh x` and `cosh ≥ 1`. Through the closed form
`latticeFloor ℓ δ n = n − sinh (n δ ℓ)/sinh (δ ℓ)` this gives
`latticeFloor_neg_of_two_le`: the ground energy is negative at every index above one, hence
(`ceil_two_le_of_half_lt`) at every aperture above `ℓ/2`.

`theFreeRegimeIsSharp` states both halves: zero cost at or below `ℓ/2`, strictly positive cost above
it. The dividing line is therefore an exact property of the off-line structure's own spacing, and
not an artefact of the estimates: a hypothetical counterexample hides for free precisely up to half
the spacing of its off-line lattice, and from that point on every further aperture must be bought
with exponentially more on-line mass.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Strict superadditivity of `sinh` -/

/-- `n sinh x < sinh (n x)` for `x > 0` and `n ≥ 2`. -/
theorem natCast_mul_sinh_lt_sinh_of_two_le {x : ℝ} (hx : 0 < x) :
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) * Real.sinh x < Real.sinh ((n : ℝ) * x) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- the base case `m + 1 = 2`
      have hm2 : m = 1 := by omega
      subst hm2
      have hs : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr hx
      have hc : (1 : ℝ) < Real.cosh x := Real.one_lt_cosh.mpr (ne_of_gt hx)
      have hid : ((1 : ℕ) + 1 : ℝ) * x = 2 * x := by push_cast; ring
      rw [show (((1 : ℕ) + 1 : ℕ) : ℝ) = 2 by push_cast; ring, Real.sinh_two_mul]
      nlinarith
    · -- the inductive step
      have hprev := ih hm
      have hs : (0 : ℝ) < Real.sinh x := Real.sinh_pos_iff.mpr hx
      have hcx : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
      have hcm : (1 : ℝ) ≤ Real.cosh ((m : ℝ) * x) := Real.one_le_cosh _
      have hsm : (0 : ℝ) ≤ Real.sinh ((m : ℝ) * x) :=
        Real.sinh_nonneg_iff.mpr (by positivity)
      have hid : (((m + 1 : ℕ)) : ℝ) * x = (m : ℝ) * x + x := by push_cast; ring
      rw [hid, Real.sinh_add]
      push_cast
      nlinarith [hprev, hcx, hcm, hsm, hs]

/-! ### 2. The ground energy is negative above index one -/

/-- **Above aliasing index one the lattice ground energy is strictly negative.** -/
theorem latticeFloor_neg_of_two_le {ℓ δ : ℝ} (hδℓ : 0 < δ * ℓ) {n : ℕ} (hn : 2 ≤ n) :
    latticeFloor ℓ δ n < 0 := by
  have hs : (0 : ℝ) < Real.sinh (δ * ℓ) := Real.sinh_pos_iff.mpr hδℓ
  have hlt := natCast_mul_sinh_lt_sinh_of_two_le hδℓ n hn
  rw [latticeFloor_eq hδℓ n, sub_neg]
  rw [lt_div_iff₀ hs]
  linarith

/-- Above half the spacing parameter the aliasing index is at least two. -/
theorem ceil_two_le_of_half_lt {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : ℓ / 2 < a) : 2 ≤ ⌈2 * a / ℓ⌉₊ := by
  have h1 : (1 : ℝ) < 2 * a / ℓ := by
    rw [lt_div_iff₀ hℓ]
    linarith
  have := Nat.lt_ceil.mpr (by exact_mod_cast h1 : ((1 : ℕ) : ℝ) < 2 * a / ℓ)
  omega

/-! ### 3. Sharpness -/

/-- **The free regime is sharp.** At or below half the sub-lattice spacing parameter the off-line
ground energy vanishes and hiding is free at every depth; above it the ground energy is strictly
negative, so every further aperture must be paid for with on-line mass. -/
theorem theFreeRegimeIsSharp {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, ℓ / 2 < a → latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ < 0 :=
  ⟨fun _ ha haℓ haL _ hf hfs =>
      dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha => latticeFloor_neg_of_two_le (by positivity) (ceil_two_le_of_half_lt hℓ ha)⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
