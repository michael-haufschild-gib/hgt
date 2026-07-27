import GaloisForLFunctions.RHTower.MobiusCausalFlatLimit
import GaloisForLFunctions.RHTower.ZetaShiftedLineBound

/-!
# The far-field bound for the parameter derivative

On the boundary line `z = iτ` with `|τ| ≥ 9` the parameter derivative of the coupled causal
multiplier obeys a log-power bound with an extra `1/|τ|`, uniformly in `0 < ω ≤ ω₁`:

```text
‖∂_ω M_ω(iτ)‖ ≤ C·log²⁶|τ| / |τ| .
```

The `1/|τ|` comes from the linear factor `1+ω+iτ`, the log powers from the shift-uniform bounds on
`1/ζ` and `ζ′/ζ`, and the subtracted pole term is bounded because its coefficient converges.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- The coefficient of the subtracted pole term is bounded near the critical parameter. -/
theorem exists_pole_factor_bound :
    ∃ ω₁ : ℝ, 0 < ω₁ ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₁ →
      ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
          2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
        ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖ ≤ 3 := by
  have h := tendsto_mobiusCausalPoleFactor
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (riemannZeta (1 + 2 * (ω : ℂ)) +
          2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
        ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2 ∈ Metric.ball (-2 : ℂ) 1 :=
    h.eventually (Metric.ball_mem_nhds (-2 : ℂ) (by norm_num : (0 : ℝ) < 1))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  refine ⟨ε / 2, by linarith, fun ω hω hωle => ?_⟩
  have hdist : dist ω (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hω]
    linarith
  have hmem := hε hdist hω
  rw [Metric.mem_ball, dist_eq_norm] at hmem
  have h2 : ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
      2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖
      ≤ ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
          2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
        ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2 - (-2)‖ + ‖(-2 : ℂ)‖ := by
    have := norm_add_le ((riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2 - (-2)) (-2 : ℂ)
    simpa using this
  have hn2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  rw [hn2] at h2
  linarith

/-- The far-field constant. -/
def farFieldConstant : ℝ := 104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2) + 3

theorem farFieldConstant_nonneg : 0 ≤ farFieldConstant := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  rw [farFieldConstant]
  positivity

/-- **The far-field bound.** -/
theorem norm_mobiusCausalMultiplierDeriv_far_le {ω : ℝ} (hω : 0 < ω) (hω1 : 2 * ω ≤ 1)
    (hK : ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
        2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
      ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖ ≤ 3)
    {τ : ℝ} (hτ : 9 ≤ |τ|) :
    ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖
      ≤ farFieldConstant * Real.log |τ| ^ 26 / |τ| := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hL2 : 2 < Real.log |τ| := two_lt_log_abs hτ
  have hL0 : (0 : ℝ) < Real.log |τ| := by linarith
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log |τ| := by linarith
  set z : ℂ := (τ : ℂ) * Complex.I with hzdef
  have hzim : z.im = τ := by
    rw [hzdef]
    simp
  have hznorm : ‖z‖ = |τ| := by
    rw [hzdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  -- the linear factor
  have hlin_lb : |τ| ≤ ‖1 + (ω : ℂ) + z‖ := by
    have h1 : |((1 : ℂ) + (ω : ℂ) + z).im| ≤ ‖1 + (ω : ℂ) + z‖ := Complex.abs_im_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ) + z).im = τ := by
      simp [Complex.add_im, hzim]
    rw [h2] at h1
    exact h1
  have hlin_lb1 : (1 : ℝ) ≤ ‖1 + (ω : ℂ) + z‖ := by
    have h1 : ((1 : ℂ) + (ω : ℂ) + z).re ≤ ‖1 + (ω : ℂ) + z‖ := Complex.re_le_norm _
    have h2 : ((1 : ℂ) + (ω : ℂ) + z).re = 1 + ω := by
      rw [hzdef]
      simp [Complex.add_re]
    rw [h2] at h1
    linarith
  have hlinpos : (0 : ℝ) < ‖1 + (ω : ℂ) + z‖ := by linarith
  -- the three zeta bounds
  have hζ1 : ‖riemannZeta (1 + z)‖ ≤ Real.log |τ| + 5 := by
    have hre : ((1 : ℂ) + z).re = 1 := by
      rw [hzdef]; simp [Complex.add_re]
    have him : ((1 : ℂ) + z).im = τ := by
      simp [Complex.add_im, hzim]
    have h := norm_riemannZeta_le_log_add (s := 1 + z) (by rw [hre]) (by rw [hre]; norm_num)
      (by rw [him]; linarith)
    rwa [him] at h
  have hinv : ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖
      ≤ 26 / zetaLowerA * Real.log |τ| ^ 7 := norm_inv_riemannZeta_shift_le hω hω1 hτ
  have hld : ‖deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)‖
      ≤ 2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18 :=
    norm_logDeriv_riemannZeta_shift_le hω hω1 hτ
  -- the first factor
  have hfac : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
      ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by
    have hsplit : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        = ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹ *
          ‖(riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹‖ := by
      rw [norm_div, norm_mul, norm_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [hsplit]
    have hb1 : ‖1 + (ω : ℂ) + z‖⁻¹ ≤ |τ|⁻¹ := inv_anti₀ hτ0 hlin_lb
    have hstep1 : ‖riemannZeta (1 + z)‖ * ‖1 + (ω : ℂ) + z‖⁻¹
        ≤ (Real.log |τ| + 5) * |τ|⁻¹ :=
      mul_le_mul hζ1 hb1 (by positivity) (by linarith)
    exact mul_le_mul hstep1 hinv (norm_nonneg _) (by positivity)
  -- the bracket
  have hbr : ‖-(1 / (1 + (ω : ℂ) + z)) -
      2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)‖
      ≤ 1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18) := by
    have hrw : 2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)
        = 2 * (deriv riemannZeta (1 + 2 * (ω : ℂ) + z) /
          riemannZeta (1 + 2 * (ω : ℂ) + z)) := by
      ring
    rw [hrw]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖-(1 / (1 + (ω : ℂ) + z))‖ ≤ 1 := by
      rw [norm_neg, norm_div, norm_one]
      rw [div_le_one hlinpos]
      exact hlin_lb1
    have h2 : ‖2 * (deriv riemannZeta (1 + 2 * (ω : ℂ) + z) /
        riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        ≤ 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18) := by
      rw [norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      linarith
    linarith
  -- the subtracted pole term
  have hpole : ‖1 / z * ((riemannZeta (1 + 2 * (ω : ℂ)) +
      2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
        ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2)‖ ≤ 3 * |τ|⁻¹ := by
    rw [norm_mul, norm_div, norm_one, hznorm]
    have h1 : |τ|⁻¹ * 3 = 3 * |τ|⁻¹ := by ring
    rw [one_div]
    calc |τ|⁻¹ * ‖(riemannZeta (1 + 2 * (ω : ℂ)) +
            2 * (1 + (ω : ℂ)) * deriv riemannZeta (1 + 2 * (ω : ℂ))) /
          ((1 + (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2‖
        ≤ |τ|⁻¹ * 3 := by
          have : (0 : ℝ) ≤ |τ|⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left hK this
      _ = 3 * |τ|⁻¹ := by ring
  -- assemble
  have hmain : ‖mobiusCausalMultiplierDeriv ω z‖
      ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
        (1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18)) + 3 * |τ|⁻¹ := by
    rw [mobiusCausalMultiplierDeriv]
    refine le_trans (norm_add_le _ _) ?_
    have hprod : ‖riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) *
        (-(1 / (1 + (ω : ℂ) + z)) -
          2 * deriv riemannZeta (1 + 2 * (ω : ℂ) + z) / riemannZeta (1 + 2 * (ω : ℂ) + z))‖
        ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
          (1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18)) := by
      rw [norm_mul]
      refine mul_le_mul hfac hbr (norm_nonneg _) ?_
      have hA7 : (0 : ℝ) ≤ 26 / zetaLowerA * Real.log |τ| ^ 7 := by positivity
      have : (0 : ℝ) ≤ (Real.log |τ| + 5) * |τ|⁻¹ := by positivity
      positivity
    linarith
  -- the closing arithmetic
  have hL7 : (0 : ℝ) < Real.log |τ| ^ 7 := by positivity
  have hL18 : (1 : ℝ) ≤ Real.log |τ| ^ 18 := one_le_pow₀ hL1
  have hstep1 : Real.log |τ| + 5 ≤ 4 * Real.log |τ| := by linarith
  have hstep2 : 1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18)
      ≤ (1 + 4496 / zetaLowerA ^ 2) * Real.log |τ| ^ 18 := by
    have hexp : (1 + 4496 / zetaLowerA ^ 2) * Real.log |τ| ^ 18
        = Real.log |τ| ^ 18 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18) := by ring
    rw [hexp]
    linarith [hL18]
  have hbound : (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
      (1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18)) + 3 * |τ|⁻¹
      ≤ farFieldConstant * Real.log |τ| ^ 26 / |τ| := by
    have hτinv : (0 : ℝ) < |τ|⁻¹ := by positivity
    have hfac1 : (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7)
        ≤ 4 * Real.log |τ| * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by
      have hnn : (0 : ℝ) ≤ |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by positivity
      nlinarith
    have hfac1nn : (0 : ℝ) ≤ (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) := by
      positivity
    have hbr_nn : (0 : ℝ) ≤ 1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18) := by positivity
    have hmul : (Real.log |τ| + 5) * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
        (1 + 2 * (2248 / zetaLowerA ^ 2 * Real.log |τ| ^ 18))
        ≤ 4 * Real.log |τ| * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
          ((1 + 4496 / zetaLowerA ^ 2) * Real.log |τ| ^ 18) :=
      mul_le_mul hfac1 hstep2 hbr_nn (by positivity)
    have hid : 4 * Real.log |τ| * |τ|⁻¹ * (26 / zetaLowerA * Real.log |τ| ^ 7) *
        ((1 + 4496 / zetaLowerA ^ 2) * Real.log |τ| ^ 18)
        = (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      ring
    have h3 : 3 * |τ|⁻¹ ≤ 3 * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      have h26 : (1 : ℝ) ≤ Real.log |τ| ^ 26 := one_le_pow₀ hL1
      nlinarith
    have hsum : farFieldConstant * Real.log |τ| ^ 26 / |τ|
        = (104 / zetaLowerA * (1 + 4496 / zetaLowerA ^ 2)) * Real.log |τ| ^ 26 * |τ|⁻¹ +
          3 * Real.log |τ| ^ 26 * |τ|⁻¹ := by
      rw [farFieldConstant, div_eq_mul_inv]
      ring
    rw [hsum]
    linarith [hid ▸ hmul]
  linarith

end

end RHTower
