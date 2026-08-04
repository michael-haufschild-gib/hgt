import GaloisForLFunctions.RHTower.Sieve.CoeffRatioRate
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistMajorantRatio
import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO

/-!
# The twisted smoothed sum, with a rate

Substituting the quantitative majorant bound for the limit it replaces turns the twisted contour
bound into an estimate with an explicit saving:

    ‖∑' μ(n)n^{-iτ}·w(n)‖ ≤ (N + H + 1)·exp(-c(log N)^{1/10}) / π ,

uniformly over the admissible twists.  The `o(1)` of `MoebiusTwistSharpLittleO` becomes
`exp(-c(log N)^{1/10})`, which is what a short-interval application needs.
-/

namespace RHTower.Sieve

open Filter Topology GaloisForLFunctions.HTGeometry

/-- **The twisted smoothed sum, with an explicit saving.** -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_rate :
    ∃ K₀ : ℕ, ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ,
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (N + smoothWidth N + 1)
            * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_majorant_ratio
  refine ⟨K₀, ?_⟩
  have hA0 := zeroFreeConst_pos
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
  intro τ hK hτ
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hratio : N / smoothWidth N ≤ smoothRatio N := le_of_eq (div_smoothWidth hN0)
  have hL0 : (0 : ℝ) ≤ smoothRatio N := (smoothRatio_pos N).le
  have hlogNH : (1 : ℝ) ≤ Real.log (N + smoothWidth N) := by
    have := Real.log_le_log hN0 (by linarith : N ≤ N + smoothWidth N)
    linarith
  have hbase := hmain N (smoothWidth N) (smoothRatio N) hN0 hH1 hratio hL0 hlogNH ht hK τ hτ
  refine le_trans hbase ?_
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

end RHTower.Sieve
