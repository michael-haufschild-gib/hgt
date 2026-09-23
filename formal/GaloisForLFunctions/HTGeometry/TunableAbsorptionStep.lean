import GaloisForLFunctions.HTGeometry.ChainBalance

/-!
# The pointwise step of the tunable absorption

Dividing the tunable Duhamel bound by `hₙ` and expanding the inner square with the fixed constant
`2` — harmless there, since it multiplies the displacement term — gives the summand form the
absorption estimate needs.

The leading constant stays `1 + ε`; only the coefficient of the small term is affected.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The pointwise summand bound, with tunable leading constant.** -/
theorem normSq_duhamel_div_le_tunable (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) {e : ℝ} (he : 0 < e) :
    ‖monicOrthoC s n w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s n) (monicOrtho s n)
      ≤ (1 + e) * (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s n) (monicOrtho s n))
        + 2 * (1 + e⁻¹) *
            (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
            ((‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
              + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) /
              momentInner s (monicOrtho s n) (monicOrtho s n)) := by
  have hpos : 0 < momentInner s (monicOrtho s n) (monicOrtho s n) :=
    monicOrtho_inner_self_pos h n
  have hsq := normSq_monicOrthoC_duhamel_le_tunable h hn z w he
  -- expand the inner square with the fixed constant
  have hinner :
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
        (kernelRoot s (fun j => monicOrthoC s j w) N *
          (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
            + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ (2 : ℕ)
      ≤ 2 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
          (‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
            + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) := by
    have hab := sq_add_le_two (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N)
      (‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N)
    nlinarith [hab, sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      kernelRoot s (fun j => monicOrthoC s j w) N), sq_nonneg (‖w - z‖ *
      momentInner s (monicOrtho s 0) (monicOrtho s 0)),
      sq_nonneg (kernelRoot s (fun j => monicOrthoC s j w) N)]
  have hnum : ‖monicOrthoC s n w‖ ^ (2 : ℕ)
      ≤ (1 + e) * ‖monicOrthoC s n z‖ ^ (2 : ℕ)
        + 2 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
            (‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
              + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) := by
    have hepos : (0:ℝ) < 1 + e⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinner hepos.le
    linarith [hsq, hmul]
  have hcollect :
      (1 + e) * (‖monicOrthoC s n z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s n) (monicOrtho s n))
        + 2 * (1 + e⁻¹) *
            (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
            ((‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
              + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)) /
              momentInner s (monicOrtho s n) (monicOrtho s n))
      = ((1 + e) * ‖monicOrthoC s n z‖ ^ (2 : ℕ)
          + 2 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
              (‖monicOrthoC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
                + ‖secondKindC s n z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)))
        / momentInner s (monicOrtho s n) (monicOrtho s n) := by
    field_simp
  rw [hcollect]
  gcongr

end HTGeometry
