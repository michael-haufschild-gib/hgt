import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization

/-!
# Polynomial bounds on compact windows next to a zero frontier

Factor an entire function into its finitely many zeros in a surrounding ball
and a nonvanishing analytic factor. To the right of the zero frontier, every
zero factor is at least the horizontal distance from that frontier.
-/

open Complex Set Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- On each bounded height window the reciprocal of an entire function grows
at most polynomially in the inverse distance from a zero-free half-plane. -/
theorem exists_compact_inverse_polynomial_bound {f : ℂ → ℂ} {Θ : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hzf : ∀ z : ℂ, Θ < z.re → f z ≠ 0) (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ,
      Θ < z.re → z.re ≤ Θ + 1 → |z.im| ≤ R →
      (z.re - Θ) ^ N * ‖(f z)⁻¹‖ ≤ C := by
  let A : ℝ := |Θ| + |R| + 3
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : ((Θ + 1 : ℝ) : ℂ) ∈ ball 0 (A + 1) := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_add_le Θ 1
    norm_num only [abs_one] at h
    dsimp [A]
    linarith [abs_nonneg R]
  obtain ⟨Z, m, g, hZball, _hm, hzeros, hg, hg0, hfac⟩ :=
    HTGeometry.exists_finset_zeroFree_factorization
      (fun z _ => hf z (mem_univ z)) ha
      (hzf _ (by simp only [ofReal_re]; linarith))
  have hZre : ∀ a ∈ Z, a.re ≤ Θ := by
    intro a ha
    by_contra h
    exact hzf a (not_le.mp h) ((hzeros a (hZball a ha)).mpr ha)
  have hsub : closedBall (0 : ℂ) A ⊆ ball 0 (A + 1) :=
    closedBall_subset_ball (by linarith)
  have hc : ContinuousOn (fun z => (g z)⁻¹) (closedBall 0 A) :=
    (hg.continuousOn.mono hsub).inv₀ (fun z hz => hg0 z (hsub hz))
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : ℂ) A).exists_bound_of_continuousOn hc
  refine ⟨∑ a ∈ Z, m a, max D 0, le_max_right _ _, fun z hz hz1 hzR => ?_⟩
  have hzA : z ∈ closedBall 0 A := by
    rw [mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |Θ| + 1 := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le Θ]
      · linarith [le_abs_self Θ]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ A := by dsimp [A]; linarith [le_abs_self R]
  have hdist : ∀ a ∈ Z, z.re - Θ ≤ ‖z - a‖ := by
    intro a ha
    have h := Complex.abs_re_le_norm (z - a)
    rw [sub_re] at h
    exact (by linarith [hZre a ha] : z.re - Θ ≤ z.re - a.re).trans
      ((le_abs_self _).trans h)
  have hp : (z.re - Θ) ^ (∑ a ∈ Z, m a) ≤ ∏ a ∈ Z, ‖z - a‖ ^ m a := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => by positivity)
      (fun a ha => pow_le_pow_left₀ (by linarith) (hdist a ha) (m a))
  have hp0 : 0 < ∏ a ∈ Z, ‖z - a‖ ^ m a :=
    (pow_pos (sub_pos.mpr hz) _).trans_le hp
  have hr : (z.re - Θ) ^ (∑ a ∈ Z, m a) * (∏ a ∈ Z, ‖z - a‖ ^ m a)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hp0]
    exact hp
  calc (z.re - Θ) ^ (∑ a ∈ Z, m a) * ‖(f z)⁻¹‖
      = ((z.re - Θ) ^ (∑ a ∈ Z, m a) * (∏ a ∈ Z, ‖z - a‖ ^ m a)⁻¹) * ‖(g z)⁻¹‖ := by
          rw [hfac (hsub hzA), norm_inv, norm_mul, norm_prod]
          simp only [norm_pow, mul_inv, norm_inv]
          ring
    _ ≤ ‖(g z)⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hr
    _ ≤ max D 0 := (hD z hzA).trans (le_max_left _ _)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
