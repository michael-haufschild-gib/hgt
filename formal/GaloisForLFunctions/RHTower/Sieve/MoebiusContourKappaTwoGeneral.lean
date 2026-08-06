import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourKappaTwo

/-!
# The width-`log^{-2}` contour bound, uniformly in the cutoff

`exists_norm_tsum_moebius_smoothWeight_le_kappa_two` fixes `N` and `H` before producing its
constants, so they may depend on the cutoff.  Replacing the Mellin decay input by its
cutoff-uniform form `exists_bound_mellin_smoothWeight_uniform_upto` moves the constants outside:
the cutoff then enters only through the explicit factors `H^{-(j+1)}(N+H+1)^{j+1}` and the trivial
sizes `(N+H)^{c(K)}`, `(N+H+1)^{d(K)}`.

This is the form in which the parameter `K` can be chosen as a function of the cutoff.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- **The width-`log^{-2}` contour bound with cutoff-uniform constants.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_kappa_two_general :
    ∃ (C C' Ms : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ Ms ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBoundTwo K
              * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ rightAbscissaTwo K))
            / truncHeight K
          + Ms * Real.log K ^ 2
              * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ rightAbscissaTwo K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
          + Ms * Real.log K ^ 2
              * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ rightAbscissaTwo K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
          + Ms * Real.log K ^ 2
              * (2 * ((N + H) ^ leftAbscissaTwo K / leftAbscissaTwo K)
                  + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ leftAbscissaTwo K)) := by
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdecj⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨Ms, L₀, hMs0, hL₀1, hunif⟩ := exists_norm_invZeta_uniform_strip
  obtain ⟨L₁, hL₁1, hzfunif⟩ := exists_zeta_uniform_strip_zero_free
  refine ⟨C, C', Ms, max 5 ⌈Real.exp (max L₀ L₁ + 1)⌉₊, hC, hC', hMs0.le,
    fun N H hN hH K hKle => ?_⟩
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
  exact norm_tsum_moebius_smoothWeight_le_sharp hN hH 0 hd1 hc0 hcd hT1
    (invZetaRightBoundTwo_nonneg K) (by positivity) (by positivity)
    hzf hFd hFt hFb hFc hFccont
    (fun s hs hsd => hdec1 N H hN hH (rightAbscissaTwo K) s hs hsd)
    (fun s hs hsd => hdecj N H hN hH (rightAbscissaTwo K) s hs hsd)
    (fun s hs hsc => hdec1 N H hN hH (leftAbscissaTwo K) s hs hsc)

end RHTower.Sieve
