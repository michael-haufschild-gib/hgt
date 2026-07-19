import GaloisForLFunctions.HTGeometry.TunableAbsorption

/-!
# The Duhamel estimate with a tunable constant

`norm_monicOrthoC_duhamel_le_of_le` bounds `‖Qₙ(w)‖` by a sum of two terms, with no constant.
Squaring it is where the constant `2` enters and where the propagated bound acquires its doubling.
Squaring with `sq_add_le_tunable` instead gives leading constant `1 + ε` for any `ε > 0`.

Nothing in `ComplexSecondKind` is modified: the unsquared estimate there is reused as it stands.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The squared Duhamel estimate with tunable leading constant.** -/
theorem normSq_monicOrthoC_duhamel_le_tunable (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) {e : ℝ} (he : 0 < e) :
    ‖monicOrthoC s n w‖ ^ 2
      ≤ (1 + e) * ‖monicOrthoC s n z‖ ^ 2
        + (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => monicOrthoC s j w) N *
              (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
                + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2 := by
  have hle := norm_monicOrthoC_duhamel_le_of_le h hn z w
  have hsq : ‖monicOrthoC s n w‖ ^ 2
      ≤ (‖monicOrthoC s n z‖
          + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => monicOrthoC s j w) N *
              (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
                + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  exact le_trans hsq (sq_add_le_tunable he)

/-- With `ε = 1` this is the constant currently used in `ComplexSecondKind`. -/
theorem normSq_monicOrthoC_duhamel_le_two (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) :
    ‖monicOrthoC s n w‖ ^ 2
      ≤ 2 * ‖monicOrthoC s n z‖ ^ 2
        + 2 *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => monicOrthoC s j w) N *
              (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
                + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2 := by
  have h1 := normSq_monicOrthoC_duhamel_le_tunable h hn z w (by norm_num : (0:ℝ) < 1)
  rw [inv_one] at h1
  linarith

end HTGeometry
