import GaloisForLFunctions.RHTower.Sieve.DampedTwistMajorantRatio
import GaloisForLFunctions.RHTower.Sieve.CoeffRatioRate

/-!
# The twisted damped smoothed sum, with a rate

Substituting the quantitative majorant bound for the limit it replaces turns the twisted damped
contour bound into an estimate with an explicit saving, uniform over the admissible twists: the
Möbius saving `exp(-c(log N)^{1/10})` multiplied by the Euler correction, which does not depend on
the damping parameter or on the twist.
-/

namespace RHTower.Sieve

open Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The twisted damped smoothed sum, with an explicit saving.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_rate {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ K₀ : ℕ, ∀ᶠ N : ℝ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ τ : ℝ,
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖
        ≤ dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N)))
          * (2 * (N + smoothWidth N + 1)
            * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2))) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_dampedTwist_smoothWeight_le_majorant_ratio hPprime
  refine ⟨K₀, ?_⟩
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hκ : (0 : ℝ) < zeroFreeConst / 8192 := by positivity
  have ha : (0 : ℝ) ≤ 1024 / zeroFreeConst := by positivity
  have hrate := eventually_coeffMajorant_ratio_rate (C := C) (C' := C') (M₀ := M₀)
    (a := 1024 / zeroFreeConst) hC hC' hM₀ ha hκ
  have hev2 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hev3 : ∀ᶠ N : ℝ in atTop,
      (2 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
    (((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).comp
      tendsto_add_smoothWidth_atTop).eventually_ge_atTop 2
  filter_upwards [hrate, eventually_ge_atTop (1 : ℝ), hev2, hev3] with N hN hN1 hlogN ht
  intro t ht0 ht1 τ hK hτ
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hratio : N / smoothWidth N ≤ smoothRatio N := le_of_eq (div_smoothWidth hN0)
  have hL0 : (0 : ℝ) ≤ smoothRatio N := (smoothRatio_pos N).le
  have hlogNH : (1 : ℝ) ≤ Real.log (N + smoothWidth N) := by
    have := Real.log_le_log hN0 (by linarith : N ≤ N + smoothWidth N)
    linarith
  have hbase := hmain t ht0 ht1 N (smoothWidth N) (smoothRatio N) hN0 hH1 hratio hL0 hlogNH
    ht hK τ hτ
  have ht1' : (1 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) := by linarith
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
  refine norm_tsum_damped_le_of_moebius_shape hP2 hchalf hbase ?_
  have hsize : (0 : ℝ) ≤ N + smoothWidth N + 1 := by linarith
  have key : coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
        (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
        * Real.exp (-(zeroFreeConst
            * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))
      ≤ Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) := by
    have hcongr : (-(zeroFreeConst
        * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))
        = (-(zeroFreeConst / 8192
            * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))) := by ring
    rw [hcongr]
    exact hN
  nlinarith [mul_le_mul_of_nonneg_left key hsize]

end

end RHTower.Sieve
