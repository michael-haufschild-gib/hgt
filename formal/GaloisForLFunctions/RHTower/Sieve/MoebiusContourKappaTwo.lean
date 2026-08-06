import GaloisForLFunctions.RHTower.Sieve.PerronSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.MellinAbscissaDecay
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBound
import GaloisForLFunctions.RHTower.Sieve.InvZetaUniformStrip
import GaloisForLFunctions.RHTower.Sieve.ZetaUniformStripZeroFree

/-!
# The contour bound at a rectangle of width `log^{-2}`

The truncated rectangle of `exists_norm_tsum_moebius_smoothWeight_le_concrete_sharp` has half-width
`c₉ log^{-9}K`, inherited from the exponent-nine zero-free region.  The exponent-one region and the
strip estimate built on it support the far wider rectangle

```text
1 - log^{-2}K ≤ Re s ≤ 1 + log^{-2}K,      |Im s| ≤ (K-3)/2,
```

on which `‖1/ζ‖ ≪ log²K` uniformly — at every height, the compact box supplying the small heights.
Since the saving of the whole estimate is `(N+H)^{-(1 - width)}`, the width is the exponent that a
Möbius cancellation bound ultimately reports.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- The left abscissa of the width-`log^{-2}` rectangle. -/
noncomputable def leftAbscissaTwo (K : ℕ) : ℝ := 1 - 1 / (Real.log K) ^ 2

/-- The right abscissa of the width-`log^{-2}` rectangle. -/
noncomputable def rightAbscissaTwo (K : ℕ) : ℝ := 1 + 1 / (Real.log K) ^ 2

/-- The Euler-product bound on the right line of that rectangle. -/
noncomputable def invZetaRightBoundTwo (K : ℕ) : ℝ := Real.exp (22 / 4) * (1 + (Real.log K) ^ 2)

theorem invZetaRightBoundTwo_nonneg (K : ℕ) : 0 ≤ invZetaRightBoundTwo K := by
  rw [invZetaRightBoundTwo]
  positivity

/-- **The contour bound at the width-`log^{-2}` rectangle.**  Same four edges as the exponent-nine
version, with the left edge pushed out to `1 - log^{-2}K` and every `1/ζ` bound replaced by the
uniform strip estimate. -/
theorem exists_norm_tsum_moebius_smoothWeight_le_kappa_two {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C C' Ms : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ Ms ∧ ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBoundTwo K * (C * (N + H + 1) ^ rightAbscissaTwo K)) / truncHeight K
            + Ms * Real.log K ^ 2 * (C' * (N + H + 1) ^ rightAbscissaTwo K)
                / (truncHeight K) ^ (j + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
            + Ms * Real.log K ^ 2 * (C' * (N + H + 1) ^ rightAbscissaTwo K)
                / (truncHeight K) ^ (j + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
            + Ms * Real.log K ^ 2
                * (2 * ((N + H) ^ leftAbscissaTwo K / leftAbscissaTwo K)
                    + 2 * (C * (N + H + 1) ^ leftAbscissaTwo K)) := by
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_upto hN hH 1
  obtain ⟨C', hC', hdecj⟩ := exists_bound_mellin_smoothWeight_upto hN hH j
  obtain ⟨Ms, L₀, hMs0, hL₀1, hunif⟩ := exists_norm_invZeta_uniform_strip
  obtain ⟨L₁, hL₁1, hzfunif⟩ := exists_zeta_uniform_strip_zero_free
  refine ⟨C, C', Ms, max 5 ⌈Real.exp (max L₀ L₁ + 1)⌉₊, hC, hC', hMs0.le, fun K hKle => ?_⟩
  -- the threshold
  have hK5 : 5 ≤ K := le_trans (le_max_left _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hceil : (⌈Real.exp (max L₀ L₁ + 1)⌉₊ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast le_trans (le_max_right _ _) hKle
  have hKexp : Real.exp (max L₀ L₁ + 1) ≤ (K : ℝ) := le_trans (Nat.le_ceil _) hceil
  have hlogK : max L₀ L₁ + 1 ≤ Real.log K := (Real.le_log_iff_exp_le (by linarith)).mpr hKexp
  have hmax1 : (1 : ℝ) ≤ max L₀ L₁ := le_trans hL₀1 (le_max_left _ _)
  have hL2 : (2 : ℝ) ≤ Real.log K := by linarith
  have hL₀K : L₀ ≤ Real.log K := by linarith [le_max_left L₀ L₁]
  have hL₁K : L₁ ≤ Real.log K := by linarith [le_max_right L₀ L₁]
  have hLsq : (4 : ℝ) ≤ Real.log K ^ 2 := by nlinarith
  have hLsq0 : (0 : ℝ) < Real.log K ^ 2 := by linarith
  have hinv : 1 / Real.log K ^ 2 ≤ 1 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLsq
  have hinv0 : (0 : ℝ) < 1 / Real.log K ^ 2 := by positivity
  -- the rectangle
  have hd1 : (1 : ℝ) < rightAbscissaTwo K := by rw [rightAbscissaTwo]; linarith
  have hc0 : (0 : ℝ) < leftAbscissaTwo K := by rw [leftAbscissaTwo]; linarith
  have hc1 : leftAbscissaTwo K ≤ 1 := by rw [leftAbscissaTwo]; linarith
  have hcd : leftAbscissaTwo K ≤ rightAbscissaTwo K := by
    rw [leftAbscissaTwo, rightAbscissaTwo]; linarith
  have hT1 : (1 : ℝ) ≤ truncHeight K := by rw [truncHeight]; linarith
  have hTK : truncHeight K ≤ (K : ℝ) := by rw [truncHeight]; linarith
  -- zero-freeness on the rectangle
  have hzf : ∀ s ∈ Set.uIcc (leftAbscissaTwo K) (rightAbscissaTwo K) ×ℂ
      Set.uIcc (-truncHeight K) (truncHeight K), s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd,
      Set.uIcc_of_le (by linarith : -truncHeight K ≤ truncHeight K)] at hs
    refine hzfunif s (K : ℝ) hL₁K ?_ ?_ hne
    · exact le_trans (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) hTK
    · simpa [leftAbscissaTwo] using hs.1.1
  -- the right line
  have hFd : ∀ y : ℝ, ‖invZeta ((rightAbscissaTwo K : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ invZetaRightBoundTwo K := by
    intro y
    have h := norm_invZeta_right_le (d := rightAbscissaTwo K) (y := y) hd1
    have heq : Real.exp (22 / 4) * (1 + 1 / (rightAbscissaTwo K - 1)) = invZetaRightBoundTwo K := by
      rw [invZetaRightBoundTwo, rightAbscissaTwo]
      field_simp
      ring
    linarith [h, heq]
  -- the horizontal edges and the left edge
  have hFt : ∀ x ∈ Set.Ioc (leftAbscissaTwo K) (rightAbscissaTwo K),
      ‖invZeta ((x : ℂ) + ((truncHeight K : ℝ) : ℂ) * Complex.I)‖ ≤ Ms * Real.log K ^ 2 := by
    intro x hx
    rw [leftAbscissaTwo] at hx
    rw [rightAbscissaTwo] at hx
    exact hunif x (truncHeight K) (K : ℝ) hL₀K
      (by rw [abs_of_nonneg (by linarith)]; exact hTK) hx.1.le hx.2
  have hFb : ∀ x ∈ Set.Ioc (leftAbscissaTwo K) (rightAbscissaTwo K),
      ‖invZeta ((x : ℂ) + ((-truncHeight K : ℝ) : ℂ) * Complex.I)‖ ≤ Ms * Real.log K ^ 2 := by
    intro x hx
    rw [leftAbscissaTwo] at hx
    rw [rightAbscissaTwo] at hx
    exact hunif x (-truncHeight K) (K : ℝ) hL₀K
      (by rw [abs_of_nonpos (by linarith)]; linarith) hx.1.le hx.2
  have hFc : ∀ y ∈ Set.Icc (-truncHeight K) (truncHeight K),
      ‖invZeta ((leftAbscissaTwo K : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Ms * Real.log K ^ 2 := by
    intro y hy
    refine hunif (leftAbscissaTwo K) y (K : ℝ) hL₀K
      (le_trans (abs_le.mpr ⟨hy.1, hy.2⟩) hTK) ?_ ?_
    · rw [leftAbscissaTwo]
    · rw [leftAbscissaTwo]; linarith
  have hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((leftAbscissaTwo K : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-truncHeight K) (truncHeight K)) :=
    continuousOn_invZeta_left_line hc1 (by linarith) hzf
  exact norm_tsum_moebius_smoothWeight_le_sharp hN hH j hd1 hc0 hcd hT1
    (invZetaRightBoundTwo_nonneg K) (by positivity) (by positivity)
    hzf hFd hFt hFb hFc hFccont
    (hdec1 (rightAbscissaTwo K) (by linarith))
    (hdecj (rightAbscissaTwo K) (by linarith))
    (hdec1 (leftAbscissaTwo K) hc0)

end RHTower.Sieve
