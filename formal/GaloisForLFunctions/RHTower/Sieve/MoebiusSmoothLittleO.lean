import GaloisForLFunctions.RHTower.Sieve.MoebiusMajorantBound

/-!
# The smoothed Möbius sum is `o(N)`

The end of the contour argument.  The majorant bound is the trivial size `2N+1` times a quantity
that tends to zero, so the smoothed Möbius sum divided by `2N+1` tends to zero.

Everything used here is unconditional: the zero-free region, the removable-singularity correction of
`1/ζ`, the four edges of the truncated contour, the balanced choice of the contour parameter, and
the polynomial-against-exponential comparison.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- Doubling tends to infinity. -/
theorem tendsto_double_atTop : Tendsto (fun N : ℝ => N + N) atTop atTop := by
  have h := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  refine h.congr fun N => ?_
  simp only [id_eq]
  ring

/-- The balanced parameter's variable tends to infinity with the cutoff. -/
theorem tendsto_logRpow_atTop :
    Tendsto (fun N : ℝ => (Real.log (N + N)) ^ ((1 : ℝ) / 10)) atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_log_atTop.comp tendsto_double_atTop)

/-- **The smoothed Möbius sum is `o(N)`.** -/
theorem tendsto_norm_tsum_moebius_smoothWeight_div :
    Tendsto (fun N : ℝ => ‖(∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ))‖
          / (N + N + 1)) atTop (𝓝 0) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_majorant
  have hA0 := zeroFreeConst_pos
  have hκ : (0 : ℝ) < zeroFreeConst / 8192 := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the majorant tends to zero along the balanced parameter
  have hmaj := tendsto_coeffMajorant_mul_exp_neg (C := C) (C' := C') (M₀ := M₀)
    (a := 1024 / zeroFreeConst) hκ
  have hcomp : Tendsto (fun N : ℝ =>
      coeffMajorant C C' M₀ (1024 / zeroFreeConst) ((Real.log (N + N)) ^ ((1 : ℝ) / 10))
        * Real.exp (-(zeroFreeConst * (Real.log (N + N)) ^ ((1 : ℝ) / 10) / 8192)))
      atTop (𝓝 0) := by
    have h := hmaj.comp tendsto_logRpow_atTop
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [show zeroFreeConst / 8192 * (Real.log (N + N)) ^ ((1 : ℝ) / 10)
        = zeroFreeConst * (Real.log (N + N)) ^ ((1 : ℝ) / 10) / 8192 by ring]
  have hlimit : Tendsto (fun N : ℝ =>
      coeffMajorant C C' M₀ (1024 / zeroFreeConst) ((Real.log (N + N)) ^ ((1 : ℝ) / 10))
        * Real.exp (-(zeroFreeConst * (Real.log (N + N)) ^ ((1 : ℝ) / 10) / 8192))
        / (2 * Real.pi)) atTop (𝓝 0) := by
    simpa using hcomp.div_const (2 * Real.pi)
  -- the side conditions hold eventually
  have hev1 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ N := eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log (N + N) :=
    (Real.tendsto_log_atTop.comp tendsto_double_atTop).eventually_ge_atTop 1
  have hev3 : ∀ᶠ N : ℝ in atTop, (2 : ℝ) ≤ (Real.log (N + N)) ^ ((1 : ℝ) / 10) :=
    tendsto_logRpow_atTop.eventually_ge_atTop 2
  have hev4 : ∀ᶠ N : ℝ in atTop, K₀ ≤ contourParam (N + N) := by
    have hcp : Tendsto (fun x : ℝ => (contourParam x : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun x => Nat.le_ceil _) ?_
      exact Real.tendsto_exp_atTop.comp
        ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
    have := (tendsto_natCast_atTop_iff (R := ℝ)).1 hcp
    exact (this.comp tendsto_double_atTop).eventually_ge_atTop K₀
  refine squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [hev1] with N hN using by positivity
  · filter_upwards [hev1, hev2, hev3, hev4] with N hN h1 h2 h3
    have hbase := hmain N hN h1 h2 h3
    have hsmul : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ))‖
        = (2 * Real.pi) * ‖(∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpi.le]
    rw [hsmul] at hbase
    rw [div_le_div_iff₀ (by linarith) hpi]
    nlinarith [hbase, hpi]

end RHTower.Sieve
