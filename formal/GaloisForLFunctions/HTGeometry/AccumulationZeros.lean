import GaloisForLFunctions.HTGeometry.SturmWindowCount

/-!
# Accumulating zeros force all derivatives to vanish

If the zeros of a smooth real function accumulate at a point, every derivative vanishes there.  The
proof is Rolle alone: between the point and a nearby zero there is a zero of the derivative, strictly
closer, so the accumulation property propagates from `f` to `f'`, and continuity turns accumulation
into vanishing at each stage.

This is the structural input that the Sturm descent of `SturmWindowCount` needs and that the
real-analyticity route would have supplied at much greater cost.  Applied to an exponential
polynomial it gives an identity theorem: all derivatives at a point determine the coefficients
through a Vandermonde/Lagrange argument, so a nonzero exponential polynomial has isolated zeros.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

/-- `t₀` is an accumulation point of the zero set of `f`. -/
def AccumZero (f : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, s ≠ t₀ ∧ |s - t₀| < ε ∧ f s = 0

/-- An accumulation point of zeros is itself a zero. -/
theorem eq_zero_of_accumZero {f : ℝ → ℝ} (hf : Continuous f) {t₀ : ℝ}
    (h : AccumZero f t₀) : f t₀ = 0 := by
  by_contra hcon
  have hev : ∀ᶠ s in nhds t₀, f s ≠ 0 :=
    hf.continuousAt.eventually (eventually_ne_nhds hcon)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨s, _, hs2, hs3⟩ := h ε hε
  exact hball (by rw [Real.dist_eq]; exact hs2) hs3

/-- **Rolle propagation.**  Accumulation of zeros passes to the derivative. -/
theorem accumZero_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {t₀ : ℝ}
    (h : AccumZero f t₀) (h0 : f t₀ = 0) : AccumZero (deriv f) t₀ := by
  intro ε hε
  obtain ⟨s, hs1, hs2, hs3⟩ := h ε hε
  rcases lt_or_gt_of_ne hs1 with hlt | hgt
  · obtain ⟨v, hv, hv0⟩ :=
      exists_deriv_eq_zero hlt (hf.continuous.continuousOn) (by rw [hs3, h0])
    refine ⟨v, ne_of_lt hv.2, ?_, hv0⟩
    rw [abs_of_neg (by linarith [hv.2] : v - t₀ < 0)]
    rw [abs_of_neg (by linarith : s - t₀ < 0)] at hs2
    linarith [hv.1]
  · obtain ⟨v, hv, hv0⟩ :=
      exists_deriv_eq_zero hgt (hf.continuous.continuousOn) (by rw [h0, hs3])
    refine ⟨v, ne_of_gt hv.1, ?_, hv0⟩
    rw [abs_of_pos (by linarith [hv.1] : (0:ℝ) < v - t₀)]
    rw [abs_of_pos (by linarith : (0:ℝ) < s - t₀)] at hs2
    linarith [hv.2]

/-- **Every derivative vanishes at an accumulation point of zeros.** -/
theorem iteratedDeriv_eq_zero_of_accumZero {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {t₀ : ℝ}
    (h : AccumZero f t₀) : ∀ n : ℕ, iteratedDeriv n f t₀ = 0 := by
  have key : ∀ n : ℕ, AccumZero (iteratedDeriv n f) t₀ ∧ iteratedDeriv n f t₀ = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simpa [iteratedDeriv_zero] using h
      · rw [iteratedDeriv_zero]
        exact eq_zero_of_accumZero hf.continuous h
    | succ n ih =>
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n f) := by
        rw [iteratedDeriv_eq_iterate]
        exact hf.iterate_deriv n
      have hacc : AccumZero (iteratedDeriv (n + 1) f) t₀ := by
        rw [iteratedDeriv_succ]
        exact accumZero_deriv (hcd.differentiable (by simp)) ih.1 ih.2
      refine ⟨hacc, eq_zero_of_accumZero ?_ hacc⟩
      rw [iteratedDeriv_succ]
      exact (contDiff_deriv hcd).continuous
  exact fun n => (key n).2

end GaloisForLFunctions.HTGeometry
