import GaloisForLFunctions.RHTower.Heat.TheHeatDetectionRateIsQuadraticInTheDepth
import GaloisForLFunctions.RHTower.XiSliceMixedClassDetection
import GaloisForLFunctions.RHTower.XiSliceHeatEffectiveKKL

/-!
# Heat detection from the local zero configuration

Let `f_t(y) = |ξ(½+y+it)|²`, let `T_n(λ, 0, t)` be the heated slice coefficients, and for a zero copy
`q` write `u_q = z_q − t` (`z_q = xiSpectralPoint q`).  For `r > 0` the **zero-growth functional**

  `Ψ_{t,r}(ρ) = Σ_q log⁺((|u_q|² + ρ²)/|u_q² + r²|)`        (`zeroGrowthSum`)

is a sum over all zeros; a zero contributes `≈ ρ²/|u_q|²` when `|u_q| ≫ ρ` and a logarithm when it is
within `O(ρ)` of the slice.

* **Growth law** (`xiSliceReal_le_mul_exp_zeroGrowthSum`).  If `Ξ(t) ≠ 0` and `f_t(r) ≠ 0`, then
  `f_t(y) ≤ f_t(r) e^{Ψ_{t,r}(y)}` for every real `y`: the Hadamard product
  `f_t(y)/f_t(0) = Π_q (1 + y²/u_q²)` (`tendsto_prod_one_add_sq_div_xiSliceProduct`), factor by factor.

* **Detection law** (`re_xiSliceHeatTransfer_neg_of_zeroGrowth`).  Let `½ + δ + it` be a zero
  (`f_t(δ) = 0`), `0 < 4r ≤ δ`, `f_t(r) ≠ 0`, and let `Ψ_{t,r}(ρ) ≤ αρ + B` on `[0, 3/2]` with
  `α ≥ log t + K₀`.  If, with `n₁ = ⌊r²/(4λ)⌋`,
  `log(6√2) + B + 2α²λ + 2αr + 16r² + 32α²λ < (n₁ + 1) log(3/2)` and
  `log(12√2) + B + 2α²λ + 2αδ + 16δ² + 32α²λ < (δ²/(4λ)) log(3/2)`,
  some `T_n(λ, 0, t)` has negative real part.

* **Linear rate** (`re_xiSliceHeatTransfer_neg_of_zeroGrowth_linear`).  For `t ≥ e^{16}`, `L = log t`,
  `δL ≥ 1`, `δ/8 ≤ r ≤ δ/4` with `f_t(r) ≠ 0`: if `Ψ_{t,r}(ρ) ≤ cLρ + bδL` on `[0, 3/2]` (`c ≥ 2`,
  `b ≥ 0`), some `T_n(κ/L, 0, t)` is negative for every `κ ≤ δ/(3000(b + c + 1))`.

The hypothesis on `Ψ` always holds with `B = Ψ_{t,r}(3/2)`; the content of the linear rate is a slope
`O(log t)` with offset `O(δ log t)`.  The offset collects the zeros within `O(δ)` of `½ + it`.  The
unit-window count allows `≍ log t` of them, and then only the quadratic rate
`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic` holds; it is sharp for such clusters
(`DeBruijn.hasSum_clusterModelHeat`).

Proof of the detection law.  The growth law, the Stirling growth beyond `3/2` and `α ≥ log t + K₀`
give `f_t(y) ≤ f_t(r) e^{B + α|y| + y²}` for all `y`; a Gaussian average gives
`H(R) ≤ √2 f_t(r) e^{B + 2α²λ} e^{αR + 2R²}`.  The Hermite expansion at `r`,
`f_t(r) = Σ p_n(r) a_n` with `|p_n(r)| ≤ (r + 2√(λn))ⁿ`, splits at `n₁` into `≤ H(2r)` and a tail that
the first condition makes `≤ f_t(r)/2`; so `f_t(r) ≤ 2H(2r) ≤ 2H(δ/2)`, and
`H(R) ≤ 2√2 e^{B + 2α²λ} H(δ/2) e^{αR + 2R²}`.  The second condition is then the hypothesis of
`re_xiSliceHeatTransfer_neg_of_relative_growth`.
-/

open Complex MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-! ## The zero-growth functional -/

/-- The contribution `log⁺((|u|² + ρ²)/|u² + r²|)` of the zero copy `q`, `u = z_q − t`. -/
def zeroGrowthTerm (t r ρ : ℝ) (q : XiZeroCopy) : ℝ :=
  max 0 (Real.log ((‖xiSpectralPoint q - t‖ ^ 2 + ρ ^ 2) / ‖(xiSpectralPoint q - t) ^ 2 + (r : ℂ) ^ 2‖))

/-- The zero-growth functional `Ψ_{t,r}(ρ) = Σ_q log⁺((|u_q|² + ρ²)/|u_q² + r²|)`. -/
def zeroGrowthSum (t r ρ : ℝ) : ℝ := ∑' q, zeroGrowthTerm t r ρ q

theorem zeroGrowthTerm_nonneg (t r ρ : ℝ) (q : XiZeroCopy) : 0 ≤ zeroGrowthTerm t r ρ q :=
  le_max_left _ _

/-- `|u² + r²| ≥ |u|² − r²`. -/
theorem sub_le_norm_sq_add_sq (u : ℂ) (r : ℝ) : ‖u‖ ^ 2 - r ^ 2 ≤ ‖u ^ 2 + (r : ℂ) ^ 2‖ := by
  have h := norm_sub_norm_le (u ^ 2) (-(r : ℂ) ^ 2)
  rw [sub_neg_eq_add, norm_neg, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at h
  exact h

/-- **Far zeros.**  If `|u|² ≥ 2r²` then the term is at most `2(ρ² + r²)/|u|²`. -/
theorem zeroGrowthTerm_le_of_far {t r ρ : ℝ} {q : XiZeroCopy}
    (hfar : 2 * r ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2) (hu : xiSpectralPoint q ≠ t) :
    zeroGrowthTerm t r ρ q ≤ 2 * (ρ ^ 2 + r ^ 2) * (1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
  set u := xiSpectralPoint q - t with hu_def
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu)
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  have hden := sub_le_norm_sq_add_sq u r
  have hb : ‖u‖ ^ 2 / 2 ≤ ‖u ^ 2 + (r : ℂ) ^ 2‖ := by linarith
  have hb0 : 0 < ‖u ^ 2 + (r : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hb
  have hrhs : 0 ≤ 2 * (ρ ^ 2 + r ^ 2) * (1 / ‖u‖ ^ 2) := by positivity
  refine max_le hrhs ?_
  have hx : 0 < (‖u‖ ^ 2 + ρ ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖ := by positivity
  refine (Real.log_le_sub_one_of_pos hx).trans ?_
  rw [div_sub_one hb0.ne', div_le_iff₀ hb0]
  have h1 : ‖u‖ ^ 2 + ρ ^ 2 - ‖u ^ 2 + (r : ℂ) ^ 2‖ ≤ ρ ^ 2 + r ^ 2 := by linarith
  have h2 : 2 * (ρ ^ 2 + r ^ 2) * (1 / ‖u‖ ^ 2) * ‖u ^ 2 + (r : ℂ) ^ 2‖
      ≥ 2 * (ρ ^ 2 + r ^ 2) * (1 / ‖u‖ ^ 2) * (‖u‖ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : 2 * (ρ ^ 2 + r ^ 2) * (1 / ‖u‖ ^ 2) * (‖u‖ ^ 2 / 2) = ρ ^ 2 + r ^ 2 := by
    field_simp
  linarith

theorem summable_zeroGrowthTerm {t : ℝ} (ht : XiC t ≠ 0) (r ρ : ℝ) :
    Summable (zeroGrowthTerm t r ρ) := by
  refine Summable.of_norm_bounded_eventually
    ((summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).mul_left (2 * (ρ ^ 2 + r ^ 2))) ?_
  have hfin := finite_xiZeroCopy_norm_le (|t| + 2 * |r|)
  refine hfin.eventually_cofinite_notMem.mono fun q hq => ?_
  simp only [Set.mem_setOf_eq, not_le] at hq
  rw [Real.norm_eq_abs, abs_of_nonneg (zeroGrowthTerm_nonneg t r ρ q)]
  refine zeroGrowthTerm_le_of_far ?_ (xiSpectralPoint_ne_ofReal ht q)
  have hd : 2 * |r| ≤ ‖xiSpectralPoint q - t‖ := by
    have h := norm_sub_norm_le (xiSpectralPoint q) (t : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hsq : (2 * |r|) ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
  nlinarith [sq_abs r, sq_nonneg r]

theorem zeroGrowthSum_nonneg (t r ρ : ℝ) : 0 ≤ zeroGrowthSum t r ρ :=
  tsum_nonneg (zeroGrowthTerm_nonneg t r ρ)

/-- `Ψ_{t,r}` depends on `ρ` through `ρ²` and is nondecreasing in `|ρ|`. -/
theorem zeroGrowthSum_mono {t : ℝ} (ht : XiC t ≠ 0) (r : ℝ) {ρ ρ' : ℝ} (h : ρ ^ 2 ≤ ρ' ^ 2) :
    zeroGrowthSum t r ρ ≤ zeroGrowthSum t r ρ' := by
  refine Summable.tsum_le_tsum (fun q => ?_) (summable_zeroGrowthTerm ht r ρ)
    (summable_zeroGrowthTerm ht r ρ')
  unfold zeroGrowthTerm
  refine max_le_max le_rfl ?_
  have hu0 : 0 < ‖xiSpectralPoint q - t‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
  rcases eq_or_lt_of_le (norm_nonneg ((xiSpectralPoint q - t) ^ 2 + (r : ℂ) ^ 2)) with h0 | h0
  · rw [← h0, div_zero, div_zero]
  · exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) h0.le)

/-! ## The growth law -/

/-- One Hadamard factor: `|1 + y²/u²|/|1 + r²/u²| ≤ e^{log⁺((|u|² + y²)/|u² + r²|)}`. -/
theorem norm_factor_div_le_exp {u : ℂ} (hu : u ≠ 0) (y r : ℝ) :
    ‖1 + (y : ℂ) ^ 2 / u ^ 2‖ / ‖1 + (r : ℂ) ^ 2 / u ^ 2‖
      ≤ Real.exp (max 0 (Real.log ((‖u‖ ^ 2 + y ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖))) := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hnu : 0 < ‖u ^ 2‖ := norm_pos_iff.mpr hu2
  have ea : 1 + (y : ℂ) ^ 2 / u ^ 2 = (u ^ 2 + (y : ℂ) ^ 2) / u ^ 2 := by field_simp
  have eb : 1 + (r : ℂ) ^ 2 / u ^ 2 = (u ^ 2 + (r : ℂ) ^ 2) / u ^ 2 := by field_simp
  rw [ea, eb, norm_div, norm_div]
  rcases eq_or_lt_of_le (norm_nonneg (u ^ 2 + (r : ℂ) ^ 2)) with h0 | h0
  · rw [← h0, zero_div, div_zero]; exact (Real.exp_pos _).le
  have hnum : ‖u ^ 2 + (y : ℂ) ^ 2‖ ≤ ‖u‖ ^ 2 + y ^ 2 := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e : ‖u ^ 2 + (y : ℂ) ^ 2‖ / ‖u ^ 2‖ / (‖u ^ 2 + (r : ℂ) ^ 2‖ / ‖u ^ 2‖)
      = ‖u ^ 2 + (y : ℂ) ^ 2‖ / ‖u ^ 2 + (r : ℂ) ^ 2‖ := by
    field_simp
  rw [e]
  have hX : ‖u ^ 2 + (y : ℂ) ^ 2‖ / ‖u ^ 2 + (r : ℂ) ^ 2‖
      ≤ (‖u‖ ^ 2 + y ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖ := div_le_div_of_nonneg_right hnum h0.le
  refine hX.trans ?_
  have hpos : 0 < (‖u‖ ^ 2 + y ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖ := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  calc (‖u‖ ^ 2 + y ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖
      = Real.exp (Real.log ((‖u‖ ^ 2 + y ^ 2) / ‖u ^ 2 + (r : ℂ) ^ 2‖)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (le_max_right _ _)

/-- **Growth law.**  If `Ξ(t) ≠ 0` and `f_t(r) ≠ 0`, then `f_t(y) ≤ f_t(r) e^{Ψ_{t,r}(y)}` for every
real `y`. -/
theorem xiSliceReal_le_mul_exp_zeroGrowthSum {t r : ℝ} (ht : XiC t ≠ 0) (hr : xiSliceReal t r ≠ 0)
    (y : ℝ) : xiSliceReal t y ≤ xiSliceReal t r * Real.exp (zeroGrowthSum t r y) := by
  have hu0 : ∀ q : XiZeroCopy, xiSpectralPoint q - t ≠ 0 := fun q =>
    sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q)
  have h0 : xiSliceProduct t 0 ≠ 0 := by
    rw [xiSliceProduct_eq_XiC_mul, mul_zero, sub_zero, add_zero]
    exact mul_ne_zero ht ht
  have hP0 : 0 < ‖xiSliceProduct t 0‖ := norm_pos_iff.mpr h0
  have hfr : 0 < xiSliceReal t r := lt_of_le_of_ne (xiSliceReal_nonneg t r) (Ne.symm hr)
  have hny := (continuous_norm.tendsto _).comp (tendsto_prod_one_add_sq_div_xiSliceProduct ht (y : ℂ))
  have hnr := (continuous_norm.tendsto _).comp (tendsto_prod_one_add_sq_div_xiSliceProduct ht (r : ℂ))
  have hnormy : ‖xiSliceProduct t (y : ℂ) / xiSliceProduct t 0‖ = xiSliceReal t y / ‖xiSliceProduct t 0‖ := by
    rw [norm_div, xiSliceProduct_ofReal_eq_xiSliceReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (xiSliceReal_nonneg t y)]
  have hnormr : ‖xiSliceProduct t (r : ℂ) / xiSliceProduct t 0‖ = xiSliceReal t r / ‖xiSliceProduct t 0‖ := by
    rw [norm_div, xiSliceProduct_ofReal_eq_xiSliceReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (xiSliceReal_nonneg t r)]
  have hne : ‖xiSliceProduct t (r : ℂ) / xiSliceProduct t 0‖ ≠ 0 := by
    rw [hnormr]; positivity
  have hratio := hny.div hnr hne
  have hbound : ∀ S : Finset XiZeroCopy,
      ((fun S : Finset XiZeroCopy => ‖∏ q ∈ S, (1 + (y : ℂ) ^ 2 / (xiSpectralPoint q - t) ^ 2)‖) /
        (fun S : Finset XiZeroCopy => ‖∏ q ∈ S, (1 + (r : ℂ) ^ 2 / (xiSpectralPoint q - t) ^ 2)‖)) S
        ≤ Real.exp (zeroGrowthSum t r y) := by
    intro S
    simp only [Pi.div_apply, norm_prod]
    rw [← Finset.prod_div_distrib]
    calc ∏ q ∈ S, ‖1 + (y : ℂ) ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          / ‖1 + (r : ℂ) ^ 2 / (xiSpectralPoint q - t) ^ 2‖
        ≤ ∏ q ∈ S, Real.exp (zeroGrowthTerm t r y q) :=
          Finset.prod_le_prod (fun q _ => by positivity) fun q _ => norm_factor_div_le_exp (hu0 q) y r
      _ = Real.exp (∑ q ∈ S, zeroGrowthTerm t r y q) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (zeroGrowthSum t r y) :=
          Real.exp_le_exp.mpr ((summable_zeroGrowthTerm ht r y).sum_le_tsum S
            fun q _ => zeroGrowthTerm_nonneg t r y q)
  have hle := le_of_tendsto' hratio hbound
  rw [hnormy, hnormr, div_div_div_cancel_right₀ hP0.ne'] at hle
  rw [div_le_iff₀ hfr] at hle
  linarith

theorem zeroGrowthSum_abs (t r y : ℝ) : zeroGrowthSum t r |y| = zeroGrowthSum t r y := by
  unfold zeroGrowthSum zeroGrowthTerm
  simp only [sq_abs]

/-! ## The envelope of the slice relative to `f_t(r)` -/

/-- **Stirling growth beyond `3/2`.**  For `t ≥ 16` and `y ≥ 3/2`,
`f_t(y) ≤ f_t(3/2) e^{A(y − 3/2) + (y − 3/2)²}`, `A = log t + K₀`. -/
theorem xiSliceReal_le_shifted {t : ℝ} (ht : 16 ≤ t) {y : ℝ} (hy : 3 / 2 ≤ y) :
    xiSliceReal t y ≤ xiSliceReal t (3 / 2) *
      Real.exp ((Real.log t + xiSliceGlobalConstant) * (y - 3 / 2) + (y - 3 / 2) ^ 2) := by
  set C := xiLogDerivStirlingConstant with hC
  have hC0 : 0 < C := xiLogDerivStirlingConstant_pos
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hF := xiSliceReal_nonneg t (3 / 2)
  have hK : xiSliceGlobalConstant = 2 * C + Real.log 6 := rfl
  set d := y - 3 / 2 with hd
  have hd0 : 0 ≤ d := by linarith
  rcases le_or_gt y (t / 2) with hz | hz
  · have h := xiSliceReal_le_of_stirling (t := t) (by linarith) (y₁ := 3 / 2) (y₂ := y)
      le_rfl hy hz
    rw [← hC] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF)
    rw [hK]
    nlinarith
  · have h1 := xiSliceReal_le_of_stirling (t := t) (by linarith) (y₁ := 3 / 2) (y₂ := t / 2)
      le_rfl (by linarith) le_rfl
    have h2 := xiSliceReal_le_of_large ht (y₁ := t / 2) (y₂ := y) le_rfl hz.le
    rw [← hC] at h1 h2
    have hlogz : Real.log (4 * y) ≤ Real.log 6 + d := by
      rw [show 4 * y = 6 * (1 + 2 / 3 * d) by rw [hd]; ring,
        Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / 3 * d by positivity)
      linarith
    have hA : 0 ≤ t / 2 - 3 / 2 := by linarith
    have hB : 0 ≤ y - t / 2 := by linarith
    have hBy : y - t / 2 ≤ d := by rw [hd]; linarith
    calc xiSliceReal t y
        ≤ xiSliceReal t (t / 2) * Real.exp ((Real.log (4 * y) + 2 * C) * (y - t / 2)) := h2
      _ ≤ xiSliceReal t (3 / 2) * Real.exp ((Real.log t + 2 * C) * (t / 2 - 3 / 2))
            * Real.exp ((Real.log (4 * y) + 2 * C) * (y - t / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = xiSliceReal t (3 / 2) * Real.exp ((Real.log t + 2 * C) * (t / 2 - 3 / 2)
            + (Real.log (4 * y) + 2 * C) * (y - t / 2)) := by
          rw [Real.exp_add]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF
          rw [hK]
          have e1 : (Real.log t + 2 * C) * (t / 2 - 3 / 2)
              ≤ (Real.log t + 2 * C + Real.log 6) * (t / 2 - 3 / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hA
          have e2 : (Real.log (4 * y) + 2 * C) * (y - t / 2)
              ≤ (Real.log t + 2 * C + Real.log 6 + d) * (y - t / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hB
          have e3 : d * (y - t / 2) ≤ d * d := mul_le_mul_of_nonneg_left hBy hd0
          have e4 : (t / 2 - 3 / 2) + (y - t / 2) = d := by rw [hd]; ring
          nlinarith

/-- **The envelope relative to `f_t(r)`.**  Let `t ≥ 16`, `Ξ(t) ≠ 0`, `f_t(r) ≠ 0`, `α ≥ log t + K₀`,
and `Ψ_{t,r}(ρ) ≤ αρ + B` for `0 ≤ ρ ≤ 3/2`.  Then `f_t(y) ≤ f_t(r) e^{B + α|y| + y²}` for
every real `y`. -/
theorem xiSliceReal_le_envelope_of_zeroGrowth {t r α B : ℝ} (ht : 16 ≤ t) (hΞ : XiC t ≠ 0)
    (hr : xiSliceReal t r ≠ 0) (hα : Real.log t + xiSliceGlobalConstant ≤ α)
    (hΨ : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 3 / 2 → zeroGrowthSum t r ρ ≤ α * ρ + B) (y : ℝ) :
    xiSliceReal t y ≤ xiSliceReal t r * Real.exp (B + α * |y| + y ^ 2) := by
  have hfr := xiSliceReal_nonneg t r
  have hA0 : 0 ≤ Real.log t + xiSliceGlobalConstant :=
    add_nonneg (Real.log_nonneg (by linarith)) xiSliceGlobalConstant_pos.le
  rcases le_or_gt |y| (3 / 2) with hy | hy
  · have h := xiSliceReal_le_mul_exp_zeroGrowthSum hΞ hr y
    rw [← zeroGrowthSum_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hfr)
    have := hΨ |y| (abs_nonneg y) hy
    nlinarith [sq_nonneg y]
  · have hy' : xiSliceReal t y = xiSliceReal t |y| := by
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0, DeBruijn.xiSliceReal_neg]
    rw [hy']
    have h1 := xiSliceReal_le_shifted ht hy.le
    have h2 := xiSliceReal_le_mul_exp_zeroGrowthSum hΞ hr (3 / 2)
    have h3 := hΨ (3 / 2) (by norm_num) le_rfl
    calc xiSliceReal t |y|
        ≤ xiSliceReal t (3 / 2) * Real.exp ((Real.log t + xiSliceGlobalConstant) * (|y| - 3 / 2)
            + (|y| - 3 / 2) ^ 2) := h1
      _ ≤ xiSliceReal t r * Real.exp (zeroGrowthSum t r (3 / 2))
            * Real.exp ((Real.log t + xiSliceGlobalConstant) * (|y| - 3 / 2) + (|y| - 3 / 2) ^ 2) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ xiSliceReal t r * Real.exp (α * (3 / 2) + B)
            * Real.exp ((Real.log t + xiSliceGlobalConstant) * (|y| - 3 / 2) + (|y| - 3 / 2) ^ 2) := by
          gcongr
      _ = xiSliceReal t r * Real.exp (α * (3 / 2) + B
            + ((Real.log t + xiSliceGlobalConstant) * (|y| - 3 / 2) + (|y| - 3 / 2) ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hfr
          have e1 : (Real.log t + xiSliceGlobalConstant) * (|y| - 3 / 2) ≤ α * (|y| - 3 / 2) :=
            mul_le_mul_of_nonneg_right hα (by linarith)
          have e2 : (|y| - 3 / 2) ^ 2 ≤ y ^ 2 := by
            rw [← sq_abs y]; nlinarith
          linarith

/-! ## Gaussian averages -/

/-- **The heated slice relative to `f_t(r)`.**  Under the hypotheses of
`xiSliceReal_le_envelope_of_zeroGrowth`, with `16λ ≤ 1` and `R ≥ 0`,
`H(R) ≤ √2 f_t(r) e^{B + 2α²λ} e^{αR + 2R²}`. -/
theorem heatedSliceReal_le_of_zeroGrowth {t r α B lam R : ℝ} (ht : 16 ≤ t) (hΞ : XiC t ≠ 0)
    (hr : xiSliceReal t r ≠ 0) (hα : Real.log t + xiSliceGlobalConstant ≤ α)
    (hΨ : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 3 / 2 → zeroGrowthSum t r ρ ≤ α * ρ + B)
    (hlam : 0 < lam) (hlam16 : 16 * lam ≤ 1) (hR : 0 ≤ R) :
    heatedSliceReal t lam R
      ≤ Real.sqrt 2 * xiSliceReal t r * Real.exp (B + 2 * α ^ 2 * lam) * Real.exp (α * R + 2 * R ^ 2) := by
  have hA0 : 0 ≤ Real.log t + xiSliceGlobalConstant :=
    add_nonneg (Real.log_nonneg (by linarith)) xiSliceGlobalConstant_pos.le
  have hα0 : 0 ≤ α := hA0.trans hα
  have hfr := xiSliceReal_nonneg t r
  obtain ⟨hint, hle⟩ := DeBruijn.integral_gauss_mul_expEnvelope_le (c₀ := xiSliceReal t r)
    (K := B) (A := α) (B := 1) (r := R) hfr zero_le_one hlam (by linarith)
  have hpt : ∀ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R)
      ≤ Real.exp (-(w ^ 2 / 2)) * DeBruijn.sliceExpEnvelope (xiSliceReal t r) B α 1
          (Real.sqrt lam * |w| + R) := by
    intro w
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (xiSliceReal_le_envelope_of_zeroGrowth ht hΞ hr hα hΨ _).trans ?_
    unfold DeBruijn.sliceExpEnvelope
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hfr
    have h1 : |Real.sqrt lam * w + R| ≤ Real.sqrt lam * |w| + R := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hR]
    have h2 : (Real.sqrt lam * w + R) ^ 2 ≤ (Real.sqrt lam * |w| + R) ^ 2 := by
      rw [← sq_abs (Real.sqrt lam * w + R)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : α * |Real.sqrt lam * w + R| ≤ α * (Real.sqrt lam * |w| + R) :=
      mul_le_mul_of_nonneg_left h1 hα0
    linarith
  have hnn : ∀ w : ℝ, 0 ≤ Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R) :=
    fun w => mul_nonneg (Real.exp_pos _).le (xiSliceReal_nonneg _ _)
  have hint' : Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R)) :=
    (integral_gauss_mul_xiSliceReal_le ht hlam hlam16 hR).1
  have hI := (integral_mono_of_nonneg (Eventually.of_forall hnn) hint
    (Eventually.of_forall hpt)).trans hle
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have e : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  unfold heatedSliceReal
  rw [div_le_iff₀ hs2π]
  refine hI.trans (le_of_eq ?_)
  rw [e, show B + α * R + 2 * 1 * R ^ 2 + 2 * α ^ 2 * lam = (B + 2 * α ^ 2 * lam) + (α * R + 2 * R ^ 2)
    by ring, Real.exp_add]
  ring

/-! ## The Hermite expansion at the base point -/

/-- **Coefficients against a growth majorant.**  If every `a_n = Re T_n(λ, 0, t) ≥ 0` and
`H(R) ≤ G₀ e^{αR + βR²}` for `R > 0`, with `β ≥ 0`, `256βλ ≤ 1`, then for `r > 0`,
`a_n (r + 2√(λn))ⁿ ≤ G₀ e^{2αr + 8βr² + 32α²λ} (2/3)ⁿ`. -/
theorem coeff_mul_pow_le_of_growth {t lam r G₀ α β : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hG₀ : 0 ≤ G₀) (hβ : 0 ≤ β) (hβlam : 256 * β * lam ≤ 1)
    (hgr : ∀ R : ℝ, 0 < R → heatedSliceReal t lam R ≤ G₀ * Real.exp (α * R + β * R ^ 2))
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) (n : ℕ) :
    (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * (r + 2 * Real.sqrt (lam * n)) ^ n
      ≤ G₀ * Real.exp (2 * α * r + 8 * β * r ^ 2 + 32 * α ^ 2 * lam) * (2 / 3) ^ n := by
  set c₁ := 2 * α * r + 8 * β * r ^ 2 + 32 * α ^ 2 * lam with hc₁
  set ρ := Real.sqrt (lam * n) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set R := 2 * (r + 2 * ρ) with hR
  have hR0 : 0 < R := by positivity
  have hr2 : ρ ^ 2 = lam * n := Real.sq_sqrt (by positivity)
  have hle := le_hasSum (hasSum_heatedSliceReal (t := t) hlam hR0) n
    fun j _ => mul_nonneg (hAM j) (pow_nonneg hR0.le j)
  have hHR := hgr R hR0
  have hexp : α * R + β * R ^ 2 ≤ c₁ + n / 4 := by
    have h1 : 4 * α * ρ ≤ n / 8 + 32 * α ^ 2 * lam := by
      nlinarith [sq_nonneg (ρ - 16 * α * lam), sq_nonneg (4 * α * ρ - n / 8 - 32 * α ^ 2 * lam)]
    have h2 : R ^ 2 ≤ 8 * r ^ 2 + 32 * (lam * n) := by
      rw [hR, ← hr2]; nlinarith [sq_nonneg (r - 2 * ρ)]
    have h3 : β * (32 * (lam * n)) ≤ n / 8 := by
      have := mul_le_mul_of_nonneg_right hβlam (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith
    have h4 : β * R ^ 2 ≤ β * (8 * r ^ 2 + 32 * (lam * n)) := mul_le_mul_of_nonneg_left h2 hβ
    have h5 : α * R = 2 * α * r + 4 * α * ρ := by rw [hR]; ring
    rw [hc₁]
    nlinarith
  have hqR : (r + 2 * ρ) ^ n = R ^ n / 2 ^ n := by rw [hR, mul_pow]; field_simp
  have he14 : Real.exp (1 / 4) ≤ 4 / 3 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [← Real.exp_le_exp, Real.exp_log (by norm_num)] at h
    refine le_trans (Real.exp_le_exp.mpr (le_of_eq (by norm_num))) h
  have h2n : Real.exp (n / 4) / 2 ^ n ≤ (2 / 3) ^ n := by
    rw [show Real.exp (n / 4) = Real.exp (1 / 4) ^ n by
      rw [← Real.exp_nat_mul]; congr 1; ring, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  calc (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * (r + 2 * ρ) ^ n
      = (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * R ^ n / 2 ^ n := by rw [hqR]; ring
    _ ≤ heatedSliceReal t lam R / 2 ^ n := div_le_div_of_nonneg_right hle (by positivity)
    _ ≤ G₀ * Real.exp (c₁ + n / 4) / 2 ^ n := by
        refine div_le_div_of_nonneg_right (hHR.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hG₀
    _ = G₀ * Real.exp c₁ * (Real.exp (n / 4) / 2 ^ n) := by rw [Real.exp_add]; ring
    _ ≤ G₀ * Real.exp c₁ * (2 / 3) ^ n := mul_le_mul_of_nonneg_left h2n (by positivity)

/-- **Reverse Hermite bound at the base point.**  Under the hypotheses of
`coeff_mul_pow_le_of_growth`, with `c₁ = 2αr + 8βr² + 32α²λ` and `n₁ = ⌊r²/(4λ)⌋`,
`f_t(r) ≤ H(2r) + 3 G₀ e^{c₁} (2/3)^{n₁+1}`.  The Hermite expansion `f_t(r) = Σ p_n(r) a_n` has
`|p_n(r)| ≤ (r + 2√(λn))ⁿ ≤ (2r)ⁿ` for `n ≤ n₁`. -/
theorem xiSliceReal_le_heatedSliceReal_add {t lam r G₀ α β : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hG₀ : 0 ≤ G₀) (hβ : 0 ≤ β) (hβlam : 256 * β * lam ≤ 1)
    (hgr : ∀ R : ℝ, 0 < R → heatedSliceReal t lam R ≤ G₀ * Real.exp (α * R + β * R ^ 2))
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    xiSliceReal t r ≤ heatedSliceReal t lam (2 * r)
      + 3 * (G₀ * Real.exp (2 * α * r + 8 * β * r ^ 2 + 32 * α ^ 2 * lam))
        * (2 / 3) ^ (⌊r ^ 2 / (4 * lam)⌋₊ + 1) := by
  set a : ℕ → ℝ := fun n => (DeBruijn.xiSliceHeatTransfer lam 0 t n).re with ha
  set p : ℕ → ℝ := fun n => DeBruijn.sliceHermiteWeight lam r n with hp
  set q : ℕ → ℝ := fun n => (r + 2 * Real.sqrt (lam * n)) ^ n with hq
  set c := G₀ * Real.exp (2 * α * r + 8 * β * r ^ 2 + 32 * α ^ 2 * lam) with hc
  set n₁ := ⌊r ^ 2 / (4 * lam)⌋₊ with hn₁
  have hherm : HasSum (fun n => p n * a n) (xiSliceReal t r) := by
    have h := Complex.hasSum_re (DeBruijn.hasSum_hermiteWeight_mul_xiSliceHeatTransfer hlam t r)
    rw [xiSliceProduct_ofReal_eq_xiSliceReal, Complex.ofReal_re] at h
    refine h.congr_fun fun n => ?_
    simp only [hp, ha]
    rw [Complex.re_ofReal_mul]
  have hterm : ∀ n, a n * q n ≤ c * (2 / 3) ^ n :=
    coeff_mul_pow_le_of_growth hlam hr hG₀ hβ hβlam hgr hAM
  have hq0 : ∀ n, 0 ≤ q n := fun n => pow_nonneg (by positivity) n
  have haq0 : ∀ n, 0 ≤ a n * q n := fun n => mul_nonneg (hAM n) (hq0 n)
  have hgeo : Summable (fun n : ℕ => c * (2 / 3 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsq : Summable (fun n => a n * q n) := Summable.of_nonneg_of_le haq0 hterm hgeo
  have hpq : ∀ n, p n * a n ≤ a n * q n := by
    intro n
    have h := DeBruijn.abs_hermiteWeight_le hlam r n
    rw [abs_of_pos hr] at h
    have h1 := le_abs_self (p n)
    have h2 : p n ≤ q n := h1.trans h
    calc p n * a n ≤ q n * a n := mul_le_mul_of_nonneg_right h2 (hAM n)
      _ = a n * q n := mul_comm _ _
  have h1 : xiSliceReal t r ≤ ∑' n, a n * q n := hasSum_le hpq hherm hsq.hasSum
  have hsplit := hsq.sum_add_tsum_nat_add (n₁ + 1)
  have hH := hasSum_heatedSliceReal (t := t) hlam (show 0 < 2 * r by positivity)
  have hhead : ∑ i ∈ Finset.range (n₁ + 1), a i * q i ≤ heatedSliceReal t lam (2 * r) := by
    refine le_trans (Finset.sum_le_sum fun i hi => ?_)
      (sum_le_hasSum _ (fun j _ => mul_nonneg (hAM j) (by positivity)) hH)
    have hi' : i ≤ n₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h4 : 4 * lam * i ≤ r ^ 2 := by
      have h' : (i : ℝ) ≤ r ^ 2 / (4 * lam) :=
        le_trans (by exact_mod_cast hi') (Nat.floor_le (by positivity))
      rw [le_div_iff₀ (by positivity)] at h'
      linarith
    have h5 : 2 * Real.sqrt (lam * i) ≤ r := by
      have h6 : (2 * Real.sqrt (lam * i)) ^ 2 ≤ r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; linarith
      exact (pow_le_pow_iff_left₀ (by positivity) hr.le (by norm_num)).mp h6
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) i) (hAM i)
  have hsq' : Summable fun k => a (k + (n₁ + 1)) * q (k + (n₁ + 1)) :=
    (summable_nat_add_iff (f := fun n => a n * q n) (n₁ + 1)).mpr hsq
  have hgeo' : Summable fun k : ℕ => c * (2 / 3 : ℝ) ^ (n₁ + 1) * (2 / 3 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail : ∑' k, a (k + (n₁ + 1)) * q (k + (n₁ + 1)) ≤ 3 * c * (2 / 3 : ℝ) ^ (n₁ + 1) := by
    refine (hsq'.tsum_le_tsum (fun k => (hterm _).trans (le_of_eq ?_)) hgeo').trans (le_of_eq ?_)
    · rw [pow_add]; ring
    · rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num; ring
  linarith

/-! ## The detection law -/

/-- **Heat detection from the local zero configuration.**  Let `t ≥ 16`, `Ξ(t) ≠ 0`, `f_t(δ) = 0`
with `δ > 0`, `0 < 4r ≤ δ`, `f_t(r) ≠ 0`, `0 < λ`, `512λ ≤ 1`, `α ≥ log t + K₀`, and
`Ψ_{t,r}(ρ) ≤ αρ + B` for `0 ≤ ρ ≤ 3/2`.  With `n₁ = ⌊r²/(4λ)⌋`, if
`log(6√2) + B + 2α²λ + 2αr + 16r² + 32α²λ < (n₁ + 1) log(3/2)` and
`log(12√2) + B + 2α²λ + 2αδ + 16δ² + 32α²λ < (δ²/(4λ)) log(3/2)`, then some `T_n(λ, 0, t)` has
negative real part. -/
theorem re_xiSliceHeatTransfer_neg_of_zeroGrowth {t δ r lam α B : ℝ} (ht : 16 ≤ t)
    (hΞ : XiC t ≠ 0) (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0) (hr : 0 < r) (hrδ : 4 * r ≤ δ)
    (hfr : xiSliceReal t r ≠ 0) (hlam : 0 < lam) (hlam512 : 512 * lam ≤ 1)
    (hα : Real.log t + xiSliceGlobalConstant ≤ α)
    (hΨ : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 3 / 2 → zeroGrowthSum t r ρ ≤ α * ρ + B)
    (htail : Real.log (6 * Real.sqrt 2) + B + 2 * α ^ 2 * lam
        + (2 * α * r + 16 * r ^ 2 + 32 * α ^ 2 * lam)
      < ((⌊r ^ 2 / (4 * lam)⌋₊ + 1 : ℕ) : ℝ) * Real.log (3 / 2))
    (hbig : Real.log (12 * Real.sqrt 2) + B + 2 * α ^ 2 * lam + 2 * α * δ + 16 * δ ^ 2
        + 32 * α ^ 2 * lam < δ ^ 2 / (4 * lam) * Real.log (3 / 2)) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer lam 0 t n).re < 0 := by
  by_contra hcon
  push Not at hcon
  set X := B + 2 * α ^ 2 * lam with hX
  set f := xiSliceReal t r with hf
  have hf0 : 0 < f := lt_of_le_of_ne (xiSliceReal_nonneg t r) (Ne.symm hfr)
  set G₀ := Real.sqrt 2 * f * Real.exp X with hG₀
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hgr0 : ∀ R : ℝ, 0 < R → heatedSliceReal t lam R ≤ G₀ * Real.exp (α * R + 2 * R ^ 2) :=
    fun R hR => heatedSliceReal_le_of_zeroGrowth ht hΞ hfr hα hΨ hlam (by linarith) hR.le
  have hrev := xiSliceReal_le_heatedSliceReal_add hlam hr (by positivity) zero_le_two (by linarith)
    hgr0 hcon
  -- the tail is at most `f/2`
  set n₁ := ⌊r ^ 2 / (4 * lam)⌋₊ with hn₁
  set c₁ := 2 * α * r + 8 * 2 * r ^ 2 + 32 * α ^ 2 * lam with hc₁
  have hsmall : 3 * (G₀ * Real.exp c₁) * (2 / 3 : ℝ) ^ (n₁ + 1) ≤ f / 2 := by
    have h23 : (2 / 3 : ℝ) ^ (n₁ + 1) = Real.exp (-(((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2))) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), ← inv_pow]; norm_num
    have hlog : Real.log (6 * Real.sqrt 2) + X + c₁ - ((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2) ≤ 0 := by
      rw [hX, hc₁]; push_cast at htail ⊢; linarith
    have hexp : Real.exp (Real.log (6 * Real.sqrt 2) + X + c₁
        - ((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr hlog
    have e : 3 * (G₀ * Real.exp c₁) * (2 / 3 : ℝ) ^ (n₁ + 1)
        = f / 2 * Real.exp (Real.log (6 * Real.sqrt 2) + X + c₁
          - ((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2)) := by
      clear_value c₁ X
      have h6 : Real.exp (Real.log (6 * Real.sqrt 2) + X + c₁
          - ((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2))
          = 6 * Real.sqrt 2 * Real.exp X * Real.exp c₁
            * Real.exp (-(((n₁ + 1 : ℕ) : ℝ) * Real.log (3 / 2))) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
      rw [h23, h6, hG₀]
      ring
    rw [e]
    calc f / 2 * Real.exp _ ≤ f / 2 * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = f / 2 := mul_one _
  have hf2 : f ≤ 2 * heatedSliceReal t lam (2 * r) := by linarith
  have hmono := heatedSliceReal_mono hlam (by positivity) (show 2 * r ≤ δ / 2 by linarith) hcon
  -- the relative growth bound
  set C := 2 * Real.sqrt 2 * Real.exp X with hC
  have hC0 : 0 < C := by positivity
  have hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R))
          / Real.sqrt (2 * Real.pi)
        ≤ C * ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi)) * Real.exp (α * R + 2 * R ^ 2) := by
    intro R hR
    change heatedSliceReal t lam R ≤ C * heatedSliceReal t lam (δ / 2) * Real.exp (α * R + 2 * R ^ 2)
    calc heatedSliceReal t lam R ≤ G₀ * Real.exp (α * R + 2 * R ^ 2) := hgr0 R hR
      _ = Real.sqrt 2 * Real.exp X * f * Real.exp (α * R + 2 * R ^ 2) := by rw [hG₀]; ring
      _ ≤ Real.sqrt 2 * Real.exp X * (2 * heatedSliceReal t lam (δ / 2))
            * Real.exp (α * R + 2 * R ^ 2) := by
          gcongr
          linarith
      _ = C * heatedSliceReal t lam (δ / 2) * Real.exp (α * R + 2 * R ^ 2) := by rw [hC]; ring
  have hbig' : Real.log (6 * C) + 2 * α * δ + 8 * 2 * δ ^ 2 + 32 * α ^ 2 * lam
      < δ ^ 2 / (4 * lam) * Real.log (3 / 2) := by
    have e : Real.log (6 * C) = Real.log (12 * Real.sqrt 2) + X := by
      rw [hC, show 6 * (2 * Real.sqrt 2 * Real.exp X) = 12 * Real.sqrt 2 * Real.exp X by ring,
        Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    rw [e, hX]; linarith
  obtain ⟨n, hn⟩ := re_xiSliceHeatTransfer_neg_of_relative_growth ht hlam (by linarith) hδ hzero
    hC0 zero_le_two (by linarith) hgr hbig'
  exact absurd (hcon n) (not_le.mpr hn)

/-- The numerical conditions of `re_xiSliceHeatTransfer_neg_of_zeroGrowth` at `α = cL`, `B = bδL`,
`λL = κ ≤ δL/(3000(b + c + 1))`. -/
theorem zeroGrowthLinear_numerics {L δ r κ b c lam N : ℝ} (hL : 16 ≤ L) (hδL : 1 ≤ δ * L)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hr8 : δ / 8 ≤ r) (hr4 : 4 * r ≤ δ) (hc : 2 ≤ c) (hb : 0 ≤ b)
    (hκK : κ * (3000 * (b + c + 1)) ≤ δ) (hlamL : lam * L = κ) (hlam : 0 < lam)
    (hlog6 : Real.log (6 * Real.sqrt 2) ≤ 3) (hlog12 : Real.log (12 * Real.sqrt 2) ≤ 3)
    (hl32 : 1 / 3 ≤ Real.log (3 / 2)) (hα2 : (c * L) ^ 2 * lam ≤ c * δ * L / 2000)
    (hn : r ^ 2 / (4 * lam) < N) :
    (Real.log (6 * Real.sqrt 2) + b * δ * L + 2 * (c * L) ^ 2 * lam
        + (2 * (c * L) * r + 16 * r ^ 2 + 32 * (c * L) ^ 2 * lam) < N * Real.log (3 / 2)) ∧
      (Real.log (12 * Real.sqrt 2) + b * δ * L + 2 * (c * L) ^ 2 * lam + 2 * (c * L) * δ
        + 16 * δ ^ 2 + 32 * (c * L) ^ 2 * lam < δ ^ 2 / (4 * lam) * Real.log (3 / 2)) := by
  obtain ⟨P, hP⟩ : ∃ P, P = δ * L := ⟨_, rfl⟩
  rw [← hP] at hδL
  have hL0 : 0 < L := by linarith
  have hr : 0 < r := by linarith
  have hδ2' : δ ^ 2 ≤ δ / 2 := by
    have := mul_le_mul_of_nonneg_left hδ2 hδ.le
    rw [sq]; linarith
  have hδP : δ / 2 ≤ P / 32 := by
    have := mul_le_mul_of_nonneg_left hL hδ.le
    rw [hP]; linarith
  have hcL : 0 ≤ c * L := by positivity
  have hcr : 2 * (c * L) * r ≤ c * P / 2 := by
    have := mul_le_mul_of_nonneg_left (show r ≤ δ / 4 by linarith) hcL
    have e : c * P / 2 = 2 * (c * L * (δ / 4)) := by rw [hP]; ring
    rw [e]; linarith
  have hcδ : 2 * (c * L) * δ = 2 * (c * P) := by rw [hP]; ring
  have hbP : b * δ * L = b * P := by rw [hP]; ring
  have hcα : c * δ * L / 2000 = c * P / 2000 := by rw [hP]; ring
  have hK0 : 0 < 3000 * (b + c + 1) := by positivity
  -- `r²/(4λ) ≥ 3000(b + c + 1) P/256`
  have hN : 3000 * (b + c + 1) * P / 256 ≤ r ^ 2 / (4 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have e : 3000 * (b + c + 1) * P / 256 * (4 * lam) = κ * (3000 * (b + c + 1)) * δ / 64 := by
      rw [← hlamL, hP]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hκK (show 0 ≤ δ / 64 by positivity)
    have h2 : (δ / 8) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hr8 2
    have e2 : κ * (3000 * (b + c + 1)) * δ / 64 = κ * (3000 * (b + c + 1)) * (δ / 64) := by ring
    have e3 : δ * (δ / 64) = (δ / 8) ^ 2 := by ring
    rw [e2]; linarith
  -- `δ²/(4λ) ≥ 3000(b + c + 1) P/4`
  have hM : 3000 * (b + c + 1) * P / 4 ≤ δ ^ 2 / (4 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have e : 3000 * (b + c + 1) * P / 4 * (4 * lam) = κ * (3000 * (b + c + 1)) * δ := by
      rw [← hlamL, hP]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hκK hδ.le
    rw [sq]; linarith
  have hT1 : 3000 * (b + c + 1) * P / 768 < N * Real.log (3 / 2) := by
    have h1 : 3000 * (b + c + 1) * P / 256 < N := lt_of_le_of_lt hN hn
    have hN0 : 0 ≤ N := le_trans (by positivity) h1.le
    have h3 : N * (1 / 3) ≤ N * Real.log (3 / 2) := mul_le_mul_of_nonneg_left hl32 hN0
    linarith
  have hT2 : 3000 * (b + c + 1) * P / 12 ≤ δ ^ 2 / (4 * lam) * Real.log (3 / 2) := by
    have := mul_le_mul hM hl32 (by norm_num) (by positivity)
    linarith
  have hcP : 0 ≤ c * P := by positivity
  have hbP0 : 0 ≤ b * P := by positivity
  have hexp1 : 3000 * (b + c + 1) * P / 768 = 3000 / 768 * (b * P) + 3000 / 768 * (c * P)
      + 3000 / 768 * P := by ring
  have hexp2 : 3000 * (b + c + 1) * P / 12 = 250 * (b * P) + 250 * (c * P) + 250 * P := by ring
  have h16r : 16 * r ^ 2 ≤ P / 32 := by
    have h1 : r ^ 2 ≤ (δ / 4) ^ 2 := pow_le_pow_left₀ hr.le (by linarith) 2
    have e : (δ / 4) ^ 2 = δ ^ 2 / 16 := by ring
    linarith
  have h16δ : 16 * δ ^ 2 ≤ P / 2 := by linarith
  have hα2' : (c * L) ^ 2 * lam ≤ c * P / 2000 := hcα ▸ hα2
  refine ⟨?_, ?_⟩
  · rw [hbP]; linarith
  · rw [hbP, hcδ]; linarith

/-- **The linear detection rate.**  Let `t ≥ e^{16}`, `L = log t`, `Ξ(t) ≠ 0`, `f_t(δ) = 0` with `δ > 0` and
`δL ≥ 1`, and let `δ/8 ≤ r ≤ δ/4` with `f_t(r) ≠ 0`.  If `Ψ_{t,r}(ρ) ≤ cLρ + bδL` for `0 ≤ ρ ≤ 3/2`,
with `c ≥ 2` and `b ≥ 0`, then some `T_n(κ/L, 0, t)` has negative real part for every
`0 < κ ≤ δ/(3000(b + c + 1))`. -/
theorem re_xiSliceHeatTransfer_neg_of_zeroGrowth_linear {t δ r κ b c : ℝ}
    (ht16 : Real.exp 16 ≤ t) (hΞ : XiC t ≠ 0) (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0)
    (hδL : 1 ≤ δ * Real.log t) (hr8 : δ / 8 ≤ r) (hr4 : 4 * r ≤ δ) (hfr : xiSliceReal t r ≠ 0)
    (hc : 2 ≤ c) (hb : 0 ≤ b)
    (hΨ : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 3 / 2 →
      zeroGrowthSum t r ρ ≤ c * Real.log t * ρ + b * δ * Real.log t)
    (hκ : 0 < κ) (hκδ : κ ≤ δ / (3000 * (b + c + 1))) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t n).re < 0 := by
  have ht : 16 ≤ t := by
    have h2 : (16 : ℝ) ≤ Real.exp 16 := by have := Real.add_one_le_exp (16 : ℝ); linarith
    linarith
  set L := Real.log t with hLdef
  have hL : 16 ≤ L := by
    rw [hLdef, ← Real.log_exp 16]; exact Real.log_le_log (Real.exp_pos _) ht16
  have hL0 : 0 < L := by linarith
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h
    push Not at h
    exact (xiSliceReal_pos t h).ne' hzero
  have hr : 0 < r := by linarith
  have hK16 := xiSliceGlobalConstant_le_sixteen
  set K := 3000 * (b + c + 1) with hK
  have hK0 : 0 < K := by positivity
  have hκK : κ * K ≤ δ := by rwa [le_div_iff₀ hK0] at hκδ
  set lam := κ / L with hlamdef
  have hlam : 0 < lam := div_pos hκ hL0
  have hlamL : lam * L = κ := by rw [hlamdef]; field_simp
  have hκ1 : κ ≤ 1 / 6000 := by
    have : 3000 ≤ K := by rw [hK]; linarith
    nlinarith
  have hlam512 : 512 * lam ≤ 1 := by
    rw [hlamdef, mul_div_assoc', div_le_one hL0]; linarith
  -- `α²λ = c²Lκ ≤ cδL/2000`
  have hα2 : (c * L) ^ 2 * lam ≤ c * δ * L / 2000 := by
    have e : (c * L) ^ 2 * lam = c ^ 2 * L * κ := by rw [← hlamL]; ring
    rw [e]
    have h1 : c * κ * 2000 ≤ δ := by
      have : c * 2000 ≤ K := by rw [hK]; nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c * L by positivity)
    nlinarith
  have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at this ⊢; linarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hlog12 : Real.log (12 * Real.sqrt 2) ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h3 : Real.exp 3 ≥ 18 := by
      have h1 := Real.exp_one_gt_d9
      have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
      rw [e]; norm_num at h2 ⊢; linarith
    nlinarith
  have hlog6 : Real.log (6 * Real.sqrt 2) ≤ 3 :=
    (Real.log_le_log (by positivity) (by have := Real.sqrt_nonneg 2; linarith)).trans hlog12
  have hαA : Real.log t + xiSliceGlobalConstant ≤ c * L := by
    have : 2 * L ≤ c * L := mul_le_mul_of_nonneg_right hc hL0.le
    rw [← hLdef]; linarith
  have hn : r ^ 2 / (4 * lam) < ((⌊r ^ 2 / (4 * lam)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  clear_value L lam K
  rw [hK] at hκK
  obtain ⟨htail, hbig⟩ := zeroGrowthLinear_numerics hL hδL hδ hδ2 hr8 hr4 hc hb hκK hlamL
    hlam hlog6 hlog12 hl32 hα2 hn
  exact re_xiSliceHeatTransfer_neg_of_zeroGrowth ht hΞ hδ hzero hr hr4 hfr hlam hlam512
    (α := c * L) (B := b * δ * L) hαA (fun ρ h0 h1 => by have := hΨ ρ h0 h1; linarith) htail hbig

end

end RHTower

