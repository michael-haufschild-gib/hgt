import GaloisForLFunctions.RHTower.XiHeatStableTestPositivity
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder

/-!
# All-rank positivity of the theta heat Hankel form on the nonnegative orthant

**Theorem** (`exists_xiHeatHankelForm_pos_of_nonneg`).  There is `a₀ > 0` such that for every heat
time `0 < t ≤ a₀`, every rank `N` and every coefficient vector `a` with `a_j ≥ 0` for `j < N`, not
all zero,

`Σ_{j,k<N} a_j a_k Re M_{j+k}(t) > 0`.

The Gaussian heat moments `M_n(t) = Σ_q w_q^n e^{−t w_q}` of the theta lane are the heat moments of
the zero copies (`xiGaussianHeatMomentReal_eq_re_xiHeatMoment`).  At small heat time all of them are
positive (`exists_heatMoment_re_pos_small_time`).  The form is then a sum of nonnegative terms
containing a diagonal term `a_j² M_{2j}(t) > 0`.

This is all-degree positivity at one fixed heat time on the nonnegative orthant, with no hypothesis
on the zeros.  The full statement on all coefficient vectors is RH
(`riemannHypothesis_iff_posRealNodes_heatHankel_nonneg`).  Its content sits on vectors whose
polynomial has nodes inside the spectrum, since stable polynomials are positive at small time
(`exists_heatHankel_re_pos_of_roots_re_nonpos`).
-/

namespace RHTower

noncomputable section

theorem xiGaussianHeatMomentReal_eq_re_xiHeatMoment (n : ℕ) (t : ℝ) :
    xiGaussianHeatMomentReal n t = (xiHeatMoment n t).re := by
  rw [xiGaussianHeatMomentReal, xiGaussianHeatMoment, xiHeatMoment]
  congr 1

/-- **All-rank positivity on the nonnegative orthant at small heat time.** -/
theorem exists_xiHeatHankelForm_pos_of_nonneg :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ t : ℝ, 0 < t → t ≤ a₀ → ∀ (N : ℕ) (a : ℕ → ℝ),
      (∀ j < N, 0 ≤ a j) → (∃ j < N, a j ≠ 0) → 0 < xiHeatHankelForm N a t := by
  obtain ⟨a₀, ha₀, hmom⟩ := exists_heatMoment_re_pos_small_time
  refine ⟨a₀, ha₀, fun t ht hta N a hnn ⟨j, hjN, hj⟩ => ?_⟩
  have hM : ∀ n, 0 < xiGaussianHeatMomentReal n t := fun n => by
    rw [xiGaussianHeatMomentReal_eq_re_xiHeatMoment]
    exact hmom t ht hta n
  have hterm : ∀ i ∈ Finset.range N, ∀ k ∈ Finset.range N,
      0 ≤ a i * a k * xiGaussianHeatMomentReal (i + k) t := fun i hi k hk =>
    mul_nonneg (mul_nonneg (hnn i (Finset.mem_range.1 hi)) (hnn k (Finset.mem_range.1 hk)))
      (hM _).le
  have hjj : 0 < a j * a j * xiGaussianHeatMomentReal (j + j) t :=
    mul_pos (mul_self_pos.2 hj) (hM _)
  have hjN' : j ∈ Finset.range N := Finset.mem_range.2 hjN
  rw [xiHeatHankelForm]
  calc (0 : ℝ) < a j * a j * xiGaussianHeatMomentReal (j + j) t := hjj
    _ ≤ ∑ k ∈ Finset.range N, a j * a k * xiGaussianHeatMomentReal (j + k) t :=
        Finset.single_le_sum (f := fun k => a j * a k * xiGaussianHeatMomentReal (j + k) t)
          (fun k hk => hterm j hjN' k hk) hjN'
    _ ≤ ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * a k * xiGaussianHeatMomentReal (i + k) t :=
        Finset.single_le_sum
          (f := fun i => ∑ k ∈ Finset.range N, a i * a k * xiGaussianHeatMomentReal (i + k) t)
          (fun i hi => Finset.sum_nonneg fun k hk => hterm i hi k hk) hjN'

end

end RHTower
