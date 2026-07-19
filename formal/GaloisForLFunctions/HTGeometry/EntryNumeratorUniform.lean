import GaloisForLFunctions.HTGeometry.DenominatorUniform

/-!
# Uniform convergence of the numerator entries

The `A` and `C` series are the same bilinear objects as `B` and `D` with the second-kind family in the
varying slot, and both are already written with the constant factor first, so the uniform estimate
applies with no commutation.  The argument of the denominator entries then transfers verbatim.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The `A` series converges uniformly on every ball.** -/
theorem tendstoUniformlyOn_nevA_series (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (r : ℝ) :
    TendstoUniformlyOn
      (bilinearPartialSum s (fun k => secondKindC s k 0) (fun z k => secondKindC s k z))
      (fun z => ∑' k, secondKindC s k 0 * secondKindC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      atTop (Metric.ball 0 r) := by
  refine tendstoUniformlyOn_bilinearLimit (Kg := ballBoundR s S P r) h _ hP _ _ ?_
  intro z hz N
  have hnorm : ‖z‖ ≤ r := by
    have := Metric.mem_ball.mp hz
    rw [dist_zero_right] at this
    exact this.le
  exact kernelRoot_le_ballBoundR h hS hP hnorm N

/-- **The `C` series converges uniformly on every ball.** -/
theorem tendstoUniformlyOn_nevC_series (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (r : ℝ) :
    TendstoUniformlyOn
      (bilinearPartialSum s (fun k => monicOrthoC s k 0) (fun z k => secondKindC s k z))
      (fun z => ∑' k, monicOrthoC s k 0 * secondKindC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      atTop (Metric.ball 0 r) := by
  refine tendstoUniformlyOn_bilinearLimit (Kg := ballBoundR s S P r) h _ hS _ _ ?_
  intro z hz N
  have hnorm : ‖z‖ ≤ r := by
    have := Metric.mem_ball.mp hz
    rw [dist_zero_right] at this
    exact this.le
  exact kernelRoot_le_ballBoundR h hS hP hnorm N

/-- The truncated `A` entry is the complex partial sum along the real embedding. -/
theorem nevAreal_ofReal_partial (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ((nevAreal s n x : ℝ) : ℂ)
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * (x : ℂ) *
          bilinearPartialSum s (fun k => secondKindC s k 0)
            (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ) := by
  rw [bilinearPartialSum, nevAreal]
  push_cast [ofReal_bilinear_finsetSum]
  have hterm : ∀ k : ℕ,
      ((Polynomial.eval 0 (secondKind s k) : ℝ) : ℂ) *
          ((Polynomial.eval x (secondKind s k) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
        = secondKindC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro k
    rw [secondKindC_ofReal, secondKindC_at_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]

/-- The truncated `C` entry is the complex partial sum along the real embedding. -/
theorem nevCreal_ofReal_partial (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ((nevCreal s n x : ℝ) : ℂ)
      = 1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * (x : ℂ) *
          bilinearPartialSum s (fun k => monicOrthoC s k 0)
            (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ) := by
  rw [bilinearPartialSum, nevCreal]
  push_cast [ofReal_bilinear_finsetSum]
  have hterm : ∀ k : ℕ,
      ((Polynomial.eval 0 (monicOrtho s k) : ℝ) : ℂ) *
          ((Polynomial.eval x (secondKind s k) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
        = monicOrthoC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro k
    rw [secondKindC_ofReal, monicOrthoC_at_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]

theorem nevAinf_tsum (s : ℕ → ℝ) (z : ℂ) :
    nevAinf s z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
          ∑' k, secondKindC s k 0 * secondKindC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := rfl

theorem nevCinf_tsum (s : ℕ → ℝ) (z : ℂ) :
    nevCinf s z
      = 1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
          ∑' k, monicOrthoC s k 0 * secondKindC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := rfl

/-- **Uniform convergence of the truncated `A` entry** on `|x| < r`. -/
theorem eventually_nevAreal_close (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| < r → |nevAreal s n x - nevArealInf s x| < ε := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set c : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hcdef
  have hcr : 0 < c * r := mul_pos h0 hr
  have huni := tendstoUniformlyOn_nevA_series h hS hP r
  rw [Metric.tendstoUniformlyOn_iff] at huni
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (huni (ε / (c * r)) (div_pos hε hcr))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn x hx => ?_⟩
  have hmem : ((x : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hclose := hN₀ (n + 1) (by omega) ((x : ℝ) : ℂ) hmem
  rw [Complex.dist_eq] at hclose
  have hcast : |nevAreal s n x - nevArealInf s x|
      = ‖((nevAreal s n x : ℝ) : ℂ) - ((nevArealInf s x : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast, nevAreal_ofReal_partial, ← nevAinf_ofReal, nevAinf_tsum]
  have hfac : (c : ℂ) * ((x : ℝ) : ℂ) *
        bilinearPartialSum s (fun k => secondKindC s k 0)
          (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ)
      - (c : ℂ) * ((x : ℝ) : ℂ) * ∑' k, secondKindC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = -((c : ℂ) * ((x : ℝ) : ℂ)) *
          ((∑' k, secondKindC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => secondKindC s k 0)
              (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ)) := by
    ring
  rw [hfac, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0]
  calc c * |x| * ‖(∑' k, secondKindC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => secondKindC s k 0)
              (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ)‖
      < c * r * (ε / (c * r)) := by
        refine mul_lt_mul' ?_ hclose (norm_nonneg _) hcr
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) h0.le
    _ = ε := by field_simp

/-- **Uniform convergence of the truncated `C` entry** on `|x| < r`. -/
theorem eventually_nevCreal_close (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x| < r → |nevCreal s n x - nevCrealInf s x| < ε := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set c : ℝ := momentInner s (monicOrtho s 0) (monicOrtho s 0) with hcdef
  have hcr : 0 < c * r := mul_pos h0 hr
  have huni := tendstoUniformlyOn_nevC_series h hS hP r
  rw [Metric.tendstoUniformlyOn_iff] at huni
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (huni (ε / (c * r)) (div_pos hε hcr))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn x hx => ?_⟩
  have hmem : ((x : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hclose := hN₀ (n + 1) (by omega) ((x : ℝ) : ℂ) hmem
  rw [Complex.dist_eq] at hclose
  have hcast : |nevCreal s n x - nevCrealInf s x|
      = ‖((nevCreal s n x : ℝ) : ℂ) - ((nevCrealInf s x : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast, nevCreal_ofReal_partial, ← nevCinf_ofReal, nevCinf_tsum]
  have hfac : (1 + (c : ℂ) * ((x : ℝ) : ℂ) *
        bilinearPartialSum s (fun k => monicOrthoC s k 0)
          (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ))
      - (1 + (c : ℂ) * ((x : ℝ) : ℂ) * ∑' k, monicOrthoC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      = -((c : ℂ) * ((x : ℝ) : ℂ)) *
          ((∑' k, monicOrthoC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => monicOrthoC s k 0)
              (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ)) := by
    ring
  rw [hfac, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0]
  calc c * |x| * ‖(∑' k, monicOrthoC s k 0 * secondKindC s k ((x : ℝ) : ℂ) /
              ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
            - bilinearPartialSum s (fun k => monicOrthoC s k 0)
              (fun z k => secondKindC s k z) (n + 1) ((x : ℝ) : ℂ)‖
      < c * r * (ε / (c * r)) := by
        refine mul_lt_mul' ?_ hclose (norm_nonneg _) hcr
        exact mul_le_mul_of_nonneg_left (le_of_lt hx) h0.le
    _ = ε := by field_simp

end HTGeometry
