import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardEnergyLimit
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardMean

/-!
# The residual forward variance exists

The exact source energy and first mean yield an actual nonnegative
variance. Its vanishing is a separate open assertion, not a premise or
a conclusion of this file.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem centered_energy_identity (a : ℕ → ℂ) (B : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖a n - B‖ ^ 2 / n) / Real.log N =
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n) / Real.log N -
        2 * (((∑ n ∈ Finset.Icc 1 N, (a n).re / n) / Real.log N) * B.re +
          ((∑ n ∈ Finset.Icc 1 N, (a n).im / n) / Real.log N) * B.im) +
        ‖B‖ ^ 2 * ((∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) / Real.log N) := by
  have ht (n : ℕ) : ‖a n - B‖ ^ 2 / n = ‖a n‖ ^ 2 / n -
      2 * ((a n).re / n * B.re + (a n).im / n * B.im) + ‖B‖ ^ 2 * (1 / n) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im]
    ring
  simp only [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Every full-positive source has a finite, nonnegative residual variance,
with energy coefficient exactly the residue square plus that variance. -/
theorem exists_forwardCoeff_energy_variance {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K V : ℝ, 0 < K ∧ 0 ≤ V ∧
      K = ‖WeilWorkSettledPhase.sourceCompletion hW 1‖ ^ 2 + V ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n‖ ^ 2 / n) / Real.log N)
          atTop (𝓝 K) ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N,
          ‖forwardCoeff lam n - WeilWorkSettledPhase.sourceCompletion hW 1‖ ^ 2 / n) /
          Real.log N) atTop (𝓝 V) := by
  obtain ⟨K, _, hK⟩ := exists_forwardCoeff_energy_limit hW
  obtain ⟨hr, hi⟩ := forwardCoeff_harmonic_mean hW
  let B : ℂ := WeilWorkSettledPhase.sourceCompletion hW 1
  have hV : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n - B‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 (K - ‖B‖ ^ 2)) := by
    have ht := (hK.sub (((hr.mul_const B.re).add (hi.mul_const B.im)).const_mul 2)).add
      (tendsto_harmonic_weight_div_log.const_mul (‖B‖ ^ 2))
    have he : K - 2 * (B.re * B.re + B.im * B.im) + ‖B‖ ^ 2 * 1 = K - ‖B‖ ^ 2 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
      ring
    change Tendsto _ _ (𝓝 (K - 2 * (B.re * B.re + B.im * B.im) + ‖B‖ ^ 2 * 1)) at ht
    rw [he] at ht
    exact ht.congr fun N => (centered_energy_identity (forwardCoeff lam) B N).symm
  have hV0 : 0 ≤ K - ‖B‖ ^ 2 := by
    apply ge_of_tendsto hV
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    apply div_nonneg
    · exact Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
    · exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hBne : B ≠ 0 := by
    dsimp [B, WeilWorkSettledPhase.sourceCompletion]
    exact mul_ne_zero (IntegerMassRigidity.bigG_ne_zero lam (by norm_num)) (Complex.exp_ne_zero _)
  have hB : 0 < ‖B‖ := norm_pos_iff.mpr hBne
  exact ⟨K, K - ‖B‖ ^ 2, by nlinarith [sq_pos_of_pos hB], hV0, by ring, hK, hV⟩

end RHTower.WeilSingularArithmetic
