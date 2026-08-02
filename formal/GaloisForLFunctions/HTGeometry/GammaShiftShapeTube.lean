import GaloisForLFunctions.HTGeometry.GammaShiftShape
import GaloisForLFunctions.HTGeometry.UniformShapeDominance

/-!
# The shifted boundary shape on a tube

Equation (4) of the shifted law is stated uniformly on a vertical tube, so the ordering `(16)` has
to hold uniformly too: a dominated shape must be negligible against the dominating one *with one
height threshold for every abscissa in `(0, M]`*.

The three decay mechanisms carry over.  The logarithmic one does not see the abscissa at all; the
real-power one is bounded by `t^ω` because `‖σ+it‖ ≥ t`; and the `Γ`-power one uses the uniform
Gamma bound at the shifted abscissa, which stays inside a tube of its own.
-/

open Filter Set Topology Function Real

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- At `Γ`-degree and argument exponent zero the shifted shape is the integer shape. -/
theorem gammaShiftShape_zero_zero (lam σ : ℝ) (b : ℤ) (t : ℝ) :
    gammaShiftShape lam σ 0 0 b t = gammaShapeZ σ 0 0 b t := by
  rw [gammaShiftShape, gammaShapeZ, Complex.ofReal_zero, Complex.cpow_zero]
  simp

/-- **A negative logarithm exponent sends the shifted shape to zero, uniformly on a tube.** -/
theorem tubeLimit_gammaShiftShape_zero_of_log_neg {M lam : ℝ} {b : ℤ} (hb : b < 0) :
    TubeLimit M (fun σ t => gammaShiftShape lam σ 0 0 b t) 0 := by
  refine (tubeLimit_gammaShapeZ_zero_of_log_neg (M := M) hb).congr (T₀ := 0) ?_
  intro σ t _ _ _
  exact (gammaShiftShape_zero_zero lam σ b t).symm

/-- **A negative real argument exponent sends the shifted shape to zero, uniformly on a tube.** -/
theorem tubeLimit_gammaShiftShape_zero_of_arg_neg {M lam : ℝ} {ω : ℝ} (hω : ω < 0) (b : ℤ) :
    TubeLimit M (fun σ t => gammaShiftShape lam σ 0 ω b t) 0 := by
  classical
  refine tubeLimit_of_squeeze (T₀ := 8)
    (g := fun t => (2 * Real.log t) ^ b.toNat * t ^ ω) ?_ ?_
  · intro σ t hσ hσM ht
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htpos : (0 : ℝ) < t := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    have hLnorm : ‖vertLog t ^ b‖ ≤ (2 * Real.log t) ^ b.toNat := by
      refine le_trans (norm_vertLog_zpow_le (by linarith) b) ?_
      refine pow_le_pow_left₀ (add_nonneg (Real.log_nonneg ht1) (by positivity)) ?_ _
      have hpi : Real.pi / 2 ≤ 2 := by
        have := Real.pi_le_four
        linarith
      have hexp2 : Real.exp 2 ≤ t := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        nlinarith [Real.exp_pos 1]
      have hlog2 : (2 : ℝ) ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos 2) hexp2
        rwa [Real.log_exp] at this
      calc Real.log t + Real.pi / 2 ≤ Real.log t + 2 := by linarith
        _ ≤ Real.log t + Real.log t := by linarith
        _ = 2 * Real.log t := by ring
    have harg : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (ω : ℂ)‖ ≤ t ^ ω := by
      rw [norm_cpow_real_vertical]
      exact Real.rpow_le_rpow_of_nonpos htpos (norm_vertical_ge_height σ t) (le_of_lt hω)
    rw [gammaShiftShape, zpow_zero, one_mul, norm_mul]
    calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (ω : ℂ)‖ * ‖vertLog t ^ b‖
        ≤ t ^ ω * (2 * Real.log t) ^ b.toNat := by
          refine mul_le_mul harg hLnorm (norm_nonneg _) (Real.rpow_nonneg (le_of_lt htpos) ω)
      _ = (2 * Real.log t) ^ b.toNat * t ^ ω := by ring
  · -- the logarithm power loses to the negative real power
    have hkey : Tendsto (fun t : ℝ => (2 ^ b.toNat) * ((Real.log t) ^ b.toNat * t ^ ω)) atTop
        (nhds 0) := by
      have h := (isLittleO_log_rpow_rpow_atTop (s := -ω) ((b.toNat : ℕ) : ℝ)
        (by linarith)).tendsto_div_nhds_zero
      have h' : Tendsto (fun t : ℝ => (Real.log t) ^ b.toNat * t ^ ω) atTop (nhds 0) := by
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
        have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
        rw [Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt htpos), neg_neg]
      simpa using h'.const_mul ((2 : ℝ) ^ b.toNat)
    refine hkey.congr fun t => ?_
    rw [mul_pow]
    ring

/-- **A positive `Γ`-degree sends the shifted shape to zero, uniformly on a tube.** -/
theorem tubeLimit_gammaShiftShape_zero_of_gamma_pos {M lam : ℝ} (hM : 0 < M) (hlam : 0 ≤ lam)
    {d : ℤ} (hd : 0 < d) (ω : ℝ) (b : ℤ) :
    TubeLimit M (fun σ t => gammaShiftShape lam σ d ω b t) 0 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d = (m : ℤ) + 1 := ⟨(d - 1).toNat, by omega⟩
  set n : ℕ := ⌈max ω 0⌉₊ with hn
  set B : ℕ := b.toNat with hB
  obtain ⟨C, hC, hΓ⟩ := exists_uniform_bound_norm_Gamma_vertical (M := M + lam)
    (by linarith) (n + 2)
  obtain ⟨D, hD, hΓ0⟩ := exists_uniform_bound_norm_Gamma_vertical (M := M + lam)
    (by linarith) 0
  refine tubeLimit_of_squeeze (T₀ := 8)
    (g := fun t => (C * D ^ m) * ((M + 1) ^ n * 2 ^ B) * ((Real.log t) ^ B / t)) ?_ ?_
  · intro σ t hσ hσM ht
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htpos : (0 : ℝ) < t := by linarith
    have hσlam : 0 < σ + lam := by linarith
    have hσlamM : σ + lam ≤ M + lam := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    -- the Gamma factor
    have hΓval : ‖gammaLine (σ + lam) t‖ ≤ C / t ^ (n + 2) := by
      rw [gammaLine]
      exact hΓ (σ + lam) t hσlam hσlamM ht1
    have hΓval0 : ‖gammaLine (σ + lam) t‖ ≤ D := by
      have := hΓ0 (σ + lam) t hσlam hσlamM ht1
      rw [gammaLine]
      simpa using this
    have hΓpow : ‖gammaLine (σ + lam) t ^ ((m : ℤ) + 1)‖
        ≤ (C / t ^ (n + 2)) * D ^ m := by
      have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, zpow_natCast, norm_pow, pow_succ']
      refine mul_le_mul hΓval ?_ (by positivity) (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) hΓval0 m
    -- the argument factor
    have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      le_trans ht1 (norm_vertical_ge_height σ t)
    have hsle : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (M + 1) * t := by
      have h1 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      have h2 : ‖(σ : ℂ)‖ = |σ| := by simp
      have h3 : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
      rw [h2, h3, abs_of_pos htpos, abs_of_pos hσ] at h1
      calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := h1
        _ ≤ M * t + t := by nlinarith
        _ = (M + 1) * t := by ring
    have harg : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (ω : ℂ)‖ ≤ ((M + 1) * t) ^ n := by
      rw [norm_cpow_real_vertical]
      have hstep : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ ω
          ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ ((n : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hs1 ?_
        exact le_trans (le_max_left ω 0) (Nat.le_ceil _)
      rw [Real.rpow_natCast] at hstep
      exact le_trans hstep (pow_le_pow_left₀ (le_trans zero_le_one hs1) hsle _)
    -- the logarithm factor
    have hLnorm : ‖vertLog t ^ b‖ ≤ (2 * Real.log t) ^ B := by
      refine le_trans (norm_vertLog_zpow_le (by linarith) b) ?_
      refine pow_le_pow_left₀ (add_nonneg (Real.log_nonneg ht1) (by positivity)) ?_ _
      have hpi : Real.pi / 2 ≤ 2 := by
        have := Real.pi_le_four
        linarith
      have hexp2 : Real.exp 2 ≤ t := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        nlinarith [Real.exp_pos 1]
      have hlog2 : (2 : ℝ) ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos 2) hexp2
        rwa [Real.log_exp] at this
      calc Real.log t + Real.pi / 2 ≤ Real.log t + 2 := by linarith
        _ ≤ Real.log t + Real.log t := by linarith
        _ = 2 * Real.log t := by ring
    have htne : t ≠ 0 := ne_of_gt htpos
    have hfinal : (C / t ^ (n + 2) * D ^ m) * (((M + 1) * t) ^ n * (2 * Real.log t) ^ B)
        = (C * D ^ m) * ((M + 1) ^ n * 2 ^ B) * ((Real.log t) ^ B / t ^ 2) := by
      rw [mul_pow, mul_pow, pow_add]
      field_simp
    have htt : t ≤ t ^ 2 := by nlinarith
    rw [gammaShiftShape, hm, norm_mul, norm_mul]
    calc ‖gammaLine (σ + lam) t ^ ((m : ℤ) + 1)‖
          * (‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (ω : ℂ)‖ * ‖vertLog t ^ b‖)
        ≤ ((C / t ^ (n + 2)) * D ^ m) * (((M + 1) * t) ^ n * (2 * Real.log t) ^ B) := by
          refine mul_le_mul hΓpow (mul_le_mul harg hLnorm (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = (C * D ^ m) * ((M + 1) ^ n * 2 ^ B) * ((Real.log t) ^ B / t ^ 2) := hfinal
      _ ≤ (C * D ^ m) * ((M + 1) ^ n * 2 ^ B) * ((Real.log t) ^ B / t) := by
          have hlogpos : (0 : ℝ) ≤ (Real.log t) ^ B := by positivity
          gcongr
  · have hlim : Tendsto (fun t : ℝ => (Real.log t) ^ B / t) atTop (nhds 0) := by
      have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) ((B : ℕ) : ℝ)
        (by norm_num)).tendsto_div_nhds_zero
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [Real.rpow_natCast, Real.rpow_one]
    have := hlim.const_mul ((C * D ^ m) * ((M + 1) ^ n * 2 ^ B))
    simpa using this

/-- **A dominated shifted shape is negligible against the dominating one, uniformly on a tube.** -/
theorem tubeLimit_gammaShiftShape_ratio_zero {M lam : ℝ} (hM : 0 < M) (hlam : 0 ≤ lam)
    {d : ℤ} {ω : ℝ} {b : ℤ} {d' : ℤ} {ω' : ℝ} {b' : ℤ}
    (h : ShiftShapeDominates d ω b d' ω' b') :
    TubeLimit M
      (fun σ t => gammaShiftShape lam σ d' ω' b' t / gammaShiftShape lam σ d ω b t) 0 := by
  have hzero : TubeLimit M (fun σ t => gammaShiftShape lam σ (d' - d) (ω' - ω) (b' - b) t) 0 := by
    rcases h with hd | ⟨hd, hω⟩ | ⟨hd, hω, hb⟩
    · exact tubeLimit_gammaShiftShape_zero_of_gamma_pos hM hlam (by omega) _ _
    · rw [show d' - d = 0 by omega]
      exact tubeLimit_gammaShiftShape_zero_of_arg_neg (by linarith) _
    · rw [show d' - d = 0 by omega, show ω' - ω = 0 by linarith]
      exact tubeLimit_gammaShiftShape_zero_of_log_neg (by omega)
  refine hzero.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hσlam : 0 < σ + lam := by linarith
  exact (gammaShiftShape_div hσlam ht d' ω' b' d ω b).symm

end

end GaloisForLFunctions.HTGeometry
