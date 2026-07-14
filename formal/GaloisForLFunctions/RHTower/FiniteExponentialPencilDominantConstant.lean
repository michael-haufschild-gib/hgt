import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Eventual survival of a constant dominant mode

If every maximal-radius atom of a norm-summable exponential pencil has the same mode, then
the maximal packet has no phase cancellation.  A nonzero aggregate coefficient consequently
gives an eventual positive lower bound after normalization by the maximal radius.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- If every maximal-radius atom has the same mode and its aggregate coefficient is nonzero,
the normalized infinite pencil is eventually bounded away from zero. -/
theorem eventually_norm_tsum_normalizedExponentialPencil_ge_of_dominant_constant
    {ι : Type*} (c b : ι → ℂ) (hc : Summable c)
    (D : Finset ι) {r : ℝ} (hr : 0 < r) {beta : ℂ}
    (hdom : ∀ i ∈ D, b i = beta)
    (hsub : ∀ i ∉ D, ‖b i‖ < r)
    (hbeta : ‖beta‖ = r)
    (hC : ∑ i ∈ D, c i ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      ‖∑' i : ι, c i * (b i / (r : ℂ)) ^ n‖ ≥
        ‖∑ i ∈ D, c i‖ / 2 := by
  classical
  let z : ι → ℂ := fun i => b i / (r : ℂ)
  let C : ℂ := ∑ i ∈ D, c i
  have hzle (i : ι) : ‖z i‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hble : ‖b i‖ ≤ r := by
      by_cases hi : i ∈ D
      · rw [hdom i hi, hbeta]
      · exact (hsub i hi).le
    exact (div_le_one hr).2 hble
  have hsum (n : ℕ) : Summable (fun i : ι => c i * z i ^ n) := by
    apply hc.norm.of_norm_bounded
    intro i
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg (c i))
      (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
  have htail : Tendsto
      (fun n : ℕ => ∑' i : {i // i ∉ D}, c i * z i ^ n)
      atTop (nhds 0) := by
    have hbound : Summable (fun i : {i // i ∉ D} => ‖c i‖) :=
      hc.norm.subtype _
    have hpoint (i : {i // i ∉ D}) :
        Tendsto (fun n : ℕ => c i * z i ^ n) atTop (nhds 0) := by
      have hzlt : ‖z i‖ < 1 := by
        dsimp only [z]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        exact (div_lt_one hr).2 (hsub i i.2)
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hzlt)
    have hdominated : ∀ᶠ n : ℕ in atTop, ∀ i : {i // i ∉ D},
        ‖c i * z i ^ n‖ ≤ ‖c i‖ := by
      exact Eventually.of_forall fun n i => by
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg (c i))
          (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdominated
  have hsplit (n : ℕ) :
      finiteExponentialPencil D c z n +
          (∑' i : {i // i ∉ D}, c i * z i ^ n) =
        ∑' i : ι, c i * z i ^ n := by
    simpa only [finiteExponentialPencil] using
      (hsum n).sum_add_tsum_subtype_compl D
  let phase : ℂ := beta / (r : ℂ)
  have hphase : ‖phase‖ = 1 := by
    dsimp only [phase]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hbeta]
    exact div_self hr.ne'
  have hlead (n : ℕ) : finiteExponentialPencil D c z n = C * phase ^ n := by
    rw [finiteExponentialPencil]
    have hzphase : ∀ i ∈ D, z i = phase := by
      intro i hi
      simp only [z, phase, hdom i hi]
    apply Eq.trans (Finset.sum_congr rfl (fun i hi => by rw [hzphase i hi]))
    rw [← Finset.sum_mul]
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hevent : ∀ᶠ n : ℕ in atTop,
      ‖∑' i : {i // i ∉ D}, c i * z i ^ n‖ < ‖C‖ / 2 := by
    exact (tendsto_order.1 htail.norm).2 _ (by simpa using half_pos hCpos)
  filter_upwards [hevent] with n hn
  have hleadNorm : ‖finiteExponentialPencil D c z n‖ = ‖C‖ := by
    rw [hlead, norm_mul, norm_pow, hphase, one_pow, mul_one]
  have hreverse := norm_sub_le
    (∑' i : ι, c i * z i ^ n)
    (∑' i : {i // i ∉ D}, c i * z i ^ n)
  have hdiff :
      (∑' i : ι, c i * z i ^ n) -
          (∑' i : {i // i ∉ D}, c i * z i ^ n) =
        finiteExponentialPencil D c z n := by
    rw [← hsplit n]
    ring
  rw [hdiff, hleadNorm] at hreverse
  have hlow : ‖C‖ -
      ‖∑' i : {i // i ∉ D}, c i * z i ^ n‖ ≤
        ‖∑' i : ι, c i * z i ^ n‖ := by
    linarith
  simpa only [z, C] using (show ‖C‖ / 2 ≤
      ‖∑' i : ι, c i * z i ^ n‖ by linarith)

end

end RHTower
