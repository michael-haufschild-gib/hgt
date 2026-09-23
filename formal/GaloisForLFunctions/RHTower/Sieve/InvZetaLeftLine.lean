import GaloisForLFunctions.RHTower.Sieve.InvZetaLeftEdge
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox

/-!
# The whole left edge, in one bound

The two halves of the left-edge estimate are proved at different heights and by different means:
compactness below height `1`, the zero-free region above it.  Merging them needs one compatibility
condition — the line `re s = 1 - c/(16 log⁹N)` must lie inside the compact box, which it does as
soon as `log⁹N` is large enough.  Since `log N → ∞`, that is eventually automatic.

The result is a single bound valid on the entire truncated left edge, with the truncation height
tied to `N` by `3 + 2|y| ≤ N`.
-/

namespace RHTower.Sieve

open Complex Filter Topology

/-- **The two halves merged.**  A single bound on the whole left edge, given that the line lies
inside the compact box supplied by `exists_bound_invZeta_low_box`. -/
theorem norm_invZeta_left_line_le {N : ℕ} {M₀ δ₀ : ℝ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N)
    (hlowbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → ‖invZeta s‖ ≤ M₀)
    (hfit : zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) ≤ δ₀)
    {y : ℝ} (hy : 3 + 2 * |y| ≤ (N : ℝ)) :
    ‖invZeta (((1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ max M₀ (2 / Real.exp ((-22
          - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log N) ^ (9 : ℕ))))
          - Real.log (5 / 2 + Real.log N)) / 4)) := by
  rcases le_or_gt (|y|) 1 with hy1 | hy1
  · refine le_trans ?_ (le_max_left _ _)
    have hre : (((1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) : ℝ) : ℂ)
        + (y : ℂ) * Complex.I).re = 1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      ring
    have him : (((1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) : ℝ) : ℂ)
        + (y : ℂ) * Complex.I).im = y := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re]
      ring
    have hA0 := zeroFreeConst_pos
    have hL0 : (0 : ℝ) < Real.log N := by linarith
    have hquot : (0 : ℝ) < zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) := by positivity
    refine hlowbox _ (by rw [hre]; linarith) (by rw [hre]; linarith) ?_
    rw [him]
    exact hy1
  · exact le_trans (norm_invZeta_left_le_explicit hlogN hN hy1.le hy) (le_max_right _ _)

/-- **The left edge bound, with the compatibility condition eliminated.**  For all large `N` the
line lies inside the box automatically, so a single constant and a single explicit function of `N`
bound `invZeta` on the whole truncated left edge. -/
theorem exists_bound_invZeta_left_line :
    ∃ (N₀ : ℕ) (M₀ : ℝ), 0 ≤ M₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ y : ℝ, 3 + 2 * |y| ≤ (N : ℝ) →
      ‖invZeta (((1 - zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ max M₀ (2 / Real.exp ((-22
            - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log N) ^ (9 : ℕ))))
            - Real.log (5 / 2 + Real.log N)) / 4)) := by
  obtain ⟨δ₀, hδ₀, M₀, hM₀, hbox⟩ := exists_bound_invZeta_low_box 2 (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ (9 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in atTop, zeroFreeConst / (16 * δ₀) ≤ (Real.log n) ^ (9 : ℕ) :=
    hpow.eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨max N₀ 2, M₀, hM₀, fun N hNle y hy => ?_⟩
  obtain ⟨hlogN, hfitpow⟩ := hN₀ N (le_trans (le_max_left _ _) hNle)
  have hN : 2 ≤ N := le_trans (le_max_right _ _) hNle
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hfit : zeroFreeConst / (16 * (Real.log N) ^ (9 : ℕ)) ≤ δ₀ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfitpow
    linarith
  exact norm_invZeta_left_line_le hlogN hN hbox hfit hy

end RHTower.Sieve
