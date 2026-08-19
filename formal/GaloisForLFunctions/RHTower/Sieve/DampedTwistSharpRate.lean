import GaloisForLFunctions.RHTower.Sieve.DampedTwistRate
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The sharp twisted damped sum, with a rate

Comparing the smoothed sum with the sharp one costs `H + 1`, so the rate of `DampedTwistRate`
transfers: the sharp twisted damped sum is at most the Euler correction times `3N` times the
Möbius saving, plus the smoothing cost.  Both main terms are `N` times an explicit saving.
-/

namespace RHTower.Sieve

open Filter Topology Finset GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The sharp twisted damped sum, with an explicit saving.** -/
theorem exists_norm_sum_dampedTwist_rate {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ K₀ : ℕ, ∀ᶠ N : ℝ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ τ : ℝ,
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n‖
        ≤ dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N)))
            * (3 * N
              * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
            / Real.pi
          + (smoothWidth N + 1) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨K₀, hev⟩ := exists_norm_tsum_dampedTwist_smoothWeight_rate hPprime
  refine ⟨K₀, ?_⟩
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hev2 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hev3 : ∀ᶠ N : ℝ in atTop,
      (1 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
    (((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).comp
      tendsto_add_smoothWidth_atTop).eventually_ge_atTop 1
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ), hev2, hev3] with N hN hN1 hlogN ht1'
  intro t ht0 ht1 τ hK hτ
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hH0 : (0 : ℝ) < smoothWidth N := by linarith
  have hHN : smoothWidth N ≤ N := smoothWidth_le hN0 hlog0
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam (N + smoothWidth N)) :=
    le_trans ht1' (le_log_contourParam _)
  have hL9 : (1 : ℝ) ≤ (Real.log (contourParam (N + smoothWidth N))) ^ 9 := one_le_pow₀ hL1
  have hchalf : (1 : ℝ) / 2 ≤ leftAbscissa (contourParam (N + smoothWidth N)) := by
    rw [leftAbscissa]
    have hsmall : zeroFreeConst
        / (16 * (Real.log (contourParam (N + smoothWidth N))) ^ 9) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hL9, hA1, hA0]
    linarith
  set corr : ℝ := dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N)))
    with hcorrdef
  have hcorr0 : 0 ≤ corr := dampedCorrBound_nonneg hP2 hchalf
  set S : ℂ := ∑' n : ℕ, dampedTwist P t τ n
      * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ)
    with hSdef
  have hbase := hN t ht0 ht1 τ hK hτ
  have hsmul : ‖(2 * Real.pi : ℝ) • S‖ = 2 * Real.pi * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hsmul] at hbase
  have hexp0 : (0 : ℝ)
      < Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) :=
    Real.exp_pos _
  have hS : ‖S‖
      ≤ corr * ((N + smoothWidth N + 1)
          * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
        / Real.pi := by
    rw [le_div_iff₀ hpi]
    nlinarith [hbase]
  have hcmp := norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
    (a := dampedTwist P t τ) (norm_dampedTwist_le_one ht0 ht1 τ)
    (N := N) (H := smoothWidth N) hN0 hH0
  have htri : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n‖
      ≤ ‖S‖ + (smoothWidth N + 1) := by
    have h := norm_sub_le S (S - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n)
    have h2 : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n‖
        ≤ ‖S‖ + ‖S - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n‖ := by
      simpa using h
    linarith [hcmp]
  have hsize : N + smoothWidth N + 1 ≤ 3 * N := by linarith
  have hmono : corr * ((N + smoothWidth N + 1)
        * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
        / Real.pi
      ≤ corr * (3 * N
        * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
        / Real.pi := by
    gcongr
  linarith [htri, hS, hmono]

end

end RHTower.Sieve
