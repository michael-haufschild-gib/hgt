/-
The canonical center geometry of reflected saddle/grid collisions.

For a divisor-antidiagonal collision `(n,m)`, the ratio center

  `n / (n+m)`

lies in the open critical strip, factor-swap reflection sends it to `1-center`,
and diagonal collisions land at the FE fixed point `1/2`.  This is the geometric
center assignment consumed by `ReflectedGridCompletedCharge`: once local orders of
`completedGN N` are finite at these centers, the completed reflected-grid charge is even.
-/
import GaloisForLFunctions.RHTower.ReflectedGridCompletedCharge

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

/-- The real ratio center of a reflected grid collision `(n,m)`: `n/(n+m)`. -/
noncomputable def reflectedGridRatioCenterR (x : ℕ × ℕ) : ℝ :=
  (x.1 : ℝ) / ((x.1 + x.2 : ℕ) : ℝ)

/-- The ratio center as a point of the complex plane, on the real axis. -/
noncomputable def reflectedGridRatioCenter (x : ℕ × ℕ) : ℂ :=
  (reflectedGridRatioCenterR x : ℂ)

/-- The first factor of a reflected grid collision is positive. -/
theorem reflectedGridCollision_fst_pos {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) : 0 < x.1 := by
  rw [reflectedGridCollision_mem_iff] at hx
  exact Nat.pos_of_ne_zero fun h => hx.2 (by rw [← hx.1, h, zero_mul])

/-- The second factor of a reflected grid collision is positive. -/
theorem reflectedGridCollision_snd_pos {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) : 0 < x.2 := by
  rw [reflectedGridCollision_mem_iff] at hx
  exact Nat.pos_of_ne_zero fun h => hx.2 (by rw [← hx.1, h, mul_zero])

/-- Factor swap sends the real ratio center to `1-center`. -/
theorem reflectedGridRatioCenterR_swap {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    reflectedGridRatioCenterR (reflectedGridSwap x) = 1 - reflectedGridRatioCenterR x := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2 : 0 < (x.2 : ℝ) := by exact_mod_cast reflectedGridCollision_snd_pos hx
  have hden : (x.1 : ℝ) + (x.2 : ℝ) ≠ 0 := by positivity
  rw [reflectedGridRatioCenterR, reflectedGridRatioCenterR, reflectedGridSwap]
  simp only [Nat.cast_add]
  rw [add_comm (x.2 : ℝ) (x.1 : ℝ)]
  field_simp [hden]
  ring

/-- Factor swap sends the complex ratio center to `1-center`. -/
theorem reflectedGridRatioCenter_swap {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    reflectedGridRatioCenter (reflectedGridSwap x) = 1 - reflectedGridRatioCenter x := by
  rw [reflectedGridRatioCenter, reflectedGridRatioCenter,
    reflectedGridRatioCenterR_swap hx]
  norm_num

/-- Every reflected grid ratio center lies in the open critical strip. -/
theorem reflectedGridRatioCenter_strip {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) :
    0 < (reflectedGridRatioCenter x).re ∧ (reflectedGridRatioCenter x).re < 1 := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2 : 0 < (x.2 : ℝ) := by exact_mod_cast reflectedGridCollision_snd_pos hx
  have hdenpos : 0 < (x.1 : ℝ) + (x.2 : ℝ) := by positivity
  rw [reflectedGridRatioCenter, reflectedGridRatioCenterR]
  simp only [Nat.cast_add, Complex.ofReal_re]
  constructor
  · exact div_pos hx1 hdenpos
  · rw [div_lt_iff₀ hdenpos]
    linarith

/-- Diagonal reflected grid collisions have real ratio center `1/2`. -/
theorem reflectedGridRatioCenterR_diag {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) (hdiag : x.1 = x.2) :
    reflectedGridRatioCenterR x = 1 / 2 := by
  have hx1 : 0 < (x.1 : ℝ) := by exact_mod_cast reflectedGridCollision_fst_pos hx
  have hx2ne : (x.2 : ℝ) ≠ 0 := by
    rw [← hdiag]
    exact ne_of_gt hx1
  rw [reflectedGridRatioCenterR, hdiag]
  simp only [Nat.cast_add]
  field_simp [hx2ne]
  ring

/-- Diagonal reflected grid collisions land at the FE fixed point `1/2`. -/
theorem reflectedGridRatioCenter_diag {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) (hdiag : x.1 = x.2) :
    reflectedGridRatioCenter x = (1 / 2 : ℂ) := by
  rw [reflectedGridRatioCenter, reflectedGridRatioCenterR_diag hx hdiag]
  norm_num

/-- **Completed-carrier charge parity for the canonical ratio center.**  Once the local
orders of `completedGN N` are finite at the ratio centers, the reflected completed charge is
even. -/
theorem reflectedGridCompletedCharge_even_of_ratio_center {C N : ℕ}
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (reflectedGridRatioCenter x) ≠ ⊤) :
    Even (reflectedGridCompletedCharge C N reflectedGridRatioCenter) := by
  exact reflectedGridCompletedCharge_even_of_center_swap
    (fun x hx => reflectedGridRatioCenter_swap hx)
    (fun x hx => reflectedGridRatioCenter_strip hx)
    (fun x hx hdiag => reflectedGridRatioCenter_diag hx hdiag)
    hfinite

/-- Deck form for the canonical ratio center. -/
theorem reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center {C N : ℕ}
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (reflectedGridRatioCenter x) ≠ ⊤) :
    deckRed 2 (↑(reflectedGridCompletedCharge C N reflectedGridRatioCenter)) = 1 := by
  exact reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap
    (fun x hx => reflectedGridRatioCenter_swap hx)
    (fun x hx => reflectedGridRatioCenter_strip hx)
    (fun x hx hdiag => reflectedGridRatioCenter_diag hx hdiag)
    hfinite

end RHTower
