import GaloisForLFunctions.RHTower.Sieve.CoeffRatioLimit
import GaloisForLFunctions.RHTower.Sieve.MoebiusMajorantRatio
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The sharp Möbius sum is `o(N)`

At the smoothing width `H = N/exp((log N)^{1/20})` both requirements hold: the contour bound gives
`‖∑ₙ μ(n)w(n)‖ = o(N)` because the majorant tends to zero, and the comparison with the sharp sum
costs `H + 1 = o(N)`.  Adding them gives

    ‖ ∑_{n ≤ N} μ(n) ‖ / N  →  0.

Everything is unconditional: the zero-free region, the removable-singularity correction of `1/ζ`,
the truncated contour and its four edges, the balanced contour parameter, the choice of smoothing
width, and the elementary comparisons.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- The shifted cutoff tends to infinity. -/
theorem tendsto_add_smoothWidth_atTop :
    Tendsto (fun N : ℝ => N + smoothWidth N) atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have hpos : (0 : ℝ) ≤ smoothWidth N := by
    rw [smoothWidth]
    have := smoothRatio_pos N
    positivity
  simp only [id_eq]
  linarith

/-- **The sharp Möbius sum is `o(N)`.** -/
theorem tendsto_norm_sum_moebius_div :
    Tendsto (fun N : ℝ =>
        ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖ / N)
      atTop (𝓝 0) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_majorant_ratio
  have hA0 := zeroFreeConst_pos
  have hκ : (0 : ℝ) < zeroFreeConst / 8192 := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha : (0 : ℝ) ≤ 1024 / zeroFreeConst := by positivity
  -- the majorant tends to zero
  have hmaj := tendsto_coeffMajorant_ratio (C := C) (C' := C') (M₀ := M₀)
    (a := 1024 / zeroFreeConst) (κ := zeroFreeConst / 8192) hC hC' hM₀ ha hκ
  have hmaj' : Tendsto (fun N : ℝ =>
      3 * (coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
            (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
          * Real.exp (-(zeroFreeConst
              * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) / (2 * Real.pi))
      atTop (𝓝 0) := by
    have hcongr : Tendsto (fun N : ℝ =>
        coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
            (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
          * Real.exp (-(zeroFreeConst
              * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) atTop (𝓝 0) := by
      refine hmaj.congr fun N => ?_
      rw [show zeroFreeConst / 8192 * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10)
          = zeroFreeConst * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192 by ring]
    simpa using ((hcongr.const_mul (3 : ℝ)).div_const (2 * Real.pi))
  have hsum : Tendsto (fun N : ℝ =>
      3 * (coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
            (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
          * Real.exp (-(zeroFreeConst
              * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) / (2 * Real.pi)
        + (smoothWidth N + 1) / N) atTop (𝓝 (0 + 0)) :=
    hmaj'.add tendsto_smoothWidth_div
  rw [add_zero] at hsum
  -- the eventual side conditions
  have hev1 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ N := eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hev3 : ∀ᶠ N : ℝ in atTop,
      (2 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
    (((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop).comp
      tendsto_add_smoothWidth_atTop).eventually_ge_atTop 2
  have hev4 : ∀ᶠ N : ℝ in atTop, K₀ ≤ contourParam (N + smoothWidth N) := by
    have hcp : Tendsto (fun x : ℝ => (contourParam x : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun x => Nat.le_ceil _) ?_
      exact Real.tendsto_exp_atTop.comp
        ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
    have hnat := (tendsto_natCast_atTop_iff (R := ℝ)).1 hcp
    exact (hnat.comp tendsto_add_smoothWidth_atTop).eventually_ge_atTop K₀
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [hev1] with N hN using by positivity
  · filter_upwards [hev1, hev2, hev3, hev4] with N hN hlogN ht hK
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
    have hH1 : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
    have hH0 : (0 : ℝ) < smoothWidth N := by linarith
    have hHN : smoothWidth N ≤ N := smoothWidth_le hN0 hlog0
    have hratio : N / smoothWidth N ≤ smoothRatio N := le_of_eq (div_smoothWidth hN0)
    have hL0 : (0 : ℝ) ≤ smoothRatio N := (smoothRatio_pos N).le
    have hlogNH : (1 : ℝ) ≤ Real.log (N + smoothWidth N) := by
      have := Real.log_le_log hN0 (by linarith : N ≤ N + smoothWidth N)
      linarith
    have hbase := hmain N (smoothWidth N) (smoothRatio N) hN0 hH1 hratio hL0 hlogNH ht hK
    have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ)
          * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖
        = (2 * Real.pi) * ‖(∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpi.le]
    rw [hsmul] at hbase
    have hcmp := norm_tsum_smoothWeight_sub_sum_le (N := N) (H := smoothWidth N) hN0 hH0
    have htri : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
        ≤ ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
              * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖ + (smoothWidth N + 1) := by
      have h := norm_sub_le (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
          * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))
        (∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ))
      have h2 : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
          ≤ ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
                * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖
            + ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
                  * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))
                - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖ := by
        have := norm_sub_le ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
            * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ)))
          ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
              * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))
            - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ))
        simpa using this
      linarith [hcmp]
    have hMpos : (0 : ℝ) ≤ coeffMajorant (C * (smoothRatio N + 2) ^ 2)
        (C' * (smoothRatio N + 2)) M₀ (1024 / zeroFreeConst)
        ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
        * Real.exp (-(zeroFreeConst
            * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192)) := by
      have hĈ : (0 : ℝ) ≤ C * (smoothRatio N + 2) ^ 2 := by
        have := zero_le_smoothRatio_add_two N
        positivity
      have hĈ' : (0 : ℝ) ≤ C' * (smoothRatio N + 2) := by
        have := zero_le_smoothRatio_add_two N
        positivity
      have hNHlog : (0 : ℝ) ≤ Real.log (N + smoothWidth N) := by linarith
      have ht0 : (0 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
        Real.rpow_nonneg hNHlog _
      have := coeffMajorant_nonneg hĈ hĈ' hM₀ ha ht0
      positivity
    have hsize : N + smoothWidth N + 1 ≤ 3 * N := by linarith
    rw [div_le_iff₀ hN0]
    have hstep : ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
          * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ))‖
        ≤ 3 * N * (coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
              (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst
                * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) / (2 * Real.pi) := by
      rw [le_div_iff₀ hpi]
      nlinarith [hbase, hMpos, hsize, hpi]
    have hrhs : (3 * (coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
              (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst
                * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) / (2 * Real.pi)
          + (smoothWidth N + 1) / N) * N
        = 3 * N * (coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀
              (1024 / zeroFreeConst) ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
            * Real.exp (-(zeroFreeConst
                * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) / 8192))) / (2 * Real.pi)
          + (smoothWidth N + 1) := by
      field_simp
    rw [hrhs]
    linarith [htri, hstep]

end RHTower.Sieve
