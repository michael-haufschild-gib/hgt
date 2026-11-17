import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSideIsNormalisedAtTheLeftEnd
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroPairingOfTheStateConvergesAbsolutely

/-!
# The state is the Cauchy transform of its zero values

For a profile `G` of the energy domain with square-summable zero values, the pairing with a probe
is the Cauchy transform of the zero values, absolutely convergent and without base point:

  `B G(p) = Σ_z L G(z) / (p - z)`   off the zeros.

For the critical state `F` the zero values are square-summable, so on `Re w > -4`

  `a L F(w) = -Σ_z L F(z) / (w + 8 - z)`,

the continuation of `L F` to the plane is its Mittag-Leffler expansion
`-(1/a) Σ_z L F(z) / (w + 8 - z)` off the transported zeros, and `c = (L F(z))_z` is a nonzero
square-summable solution of the Cauchy system of the zeros

  `a c_{z'} = -Σ_z c_z / (z' + 8 - z)`.

Mechanism. `Σ_z |p - z|⁻² < ∞`, so square-summable values are absolutely summable against the
Cauchy kernel (Cauchy–Schwarz). The regularising term `Σ_z c_z / (b - z)` of the explicit formula
is dominated by `2 |c_z| / |z|` on the negative real axis and tends to zero there.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Square-summable values against the Cauchy kernel -/

/-- Square-summable values are absolutely summable against the Cauchy kernel of a point off the
zeros. -/
theorem summable_norm_mul_inv_sub_centredZero {c : XiZeroCopy → ℂ}
    (hc : Summable fun q => ‖c q‖ ^ 2) {p : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ q : XiZeroCopy, δ ≤ ‖p - centredZero q‖) :
    Summable fun q : XiZeroCopy => ‖c q * (p - centredZero q)⁻¹‖ := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((hc.add (summable_inv_sq_centredZero.mul_left ((1 + ‖p‖ / δ) ^ 2))).div_const 2)
  have h := norm_inv_sub_le hδ (centredZero_ne_zero q) (hp q) (le_refl ‖p‖)
  have hB : ‖(p - centredZero q)⁻¹‖ ^ 2 ≤ (1 + ‖p‖ / δ) ^ 2 * ‖centredZero q‖⁻¹ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖c q‖ - ‖(p - centredZero q)⁻¹‖), hB]

theorem norm_inv_ofReal_sub_centredZero_le {x : ℝ} (hx : x ≤ -1) (q : XiZeroCopy) :
    ‖((x : ℂ) - centredZero q)⁻¹‖ ≤ 2 * ‖centredZero q‖⁻¹ := by
  have hz := abs_re_centredZero_lt q
  have h1 : 1 / 2 ≤ ‖(x : ℂ) - centredZero q‖ :=
    half_le_norm_sub_centredZero (p := (x : ℂ))
      (by rw [Complex.ofReal_re, abs_of_nonpos (by linarith)]; linarith) q
  have h2 : |(centredZero q).im| ≤ ‖(x : ℂ) - centredZero q‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - centredZero q)
    rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  have h3 : ‖centredZero q‖ ≤ 2 * ‖(x : ℂ) - centredZero q‖ := by
    have h := Complex.norm_le_abs_re_add_abs_im (centredZero q)
    linarith
  have hzpos : 0 < ‖centredZero q‖ := norm_pos_iff.mpr (centredZero_ne_zero q)
  have hpos : 0 < ‖(x : ℂ) - centredZero q‖ := by linarith
  rw [norm_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hpos hzpos]
  linarith

theorem tendsto_inv_ofReal_sub_atBot (z : ℂ) :
    Tendsto (fun x : ℝ => ((x : ℂ) - z)⁻¹) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun x : ℝ => (-x + -|z.re|)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atBot _ tendsto_neg_atBot_atTop)
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_lt_atBot (-|z.re| - 1)] with x hx
  have hpos : 0 < -x + -|z.re| := by linarith
  have hle : -x + -|z.re| ≤ ‖(x : ℂ) - z‖ := by
    have h1 := Complex.abs_re_le_norm ((x : ℂ) - z)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 := neg_le_abs (x - z.re)
    have h3 := neg_abs_le z.re
    linarith
  rw [norm_inv]
  exact inv_anti₀ hpos hle

/-- The Cauchy transform of square-summable values vanishes at the left end of the real axis. -/
theorem tendsto_tsum_mul_inv_ofReal_sub_centredZero {c : XiZeroCopy → ℂ}
    (hc : Summable fun q => ‖c q‖ ^ 2) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, c q * ((x : ℂ) - centredZero q)⁻¹) atBot (𝓝 0) := by
  have hbound : Summable fun q : XiZeroCopy => ‖c q‖ * (2 * ‖centredZero q‖⁻¹) := by
    refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
      (hc.add summable_inv_sq_centredZero)
    nlinarith [sq_nonneg (‖c q‖ - ‖centredZero q‖⁻¹)]
  have hpt : ∀ q : XiZeroCopy,
      Tendsto (fun x : ℝ => c q * ((x : ℂ) - centredZero q)⁻¹) atBot (𝓝 0) := by
    intro q
    have h := (tendsto_inv_ofReal_sub_atBot (centredZero q)).const_mul (c q)
    rwa [mul_zero] at h
  have hev : ∀ᶠ x : ℝ in atBot, ∀ q : XiZeroCopy,
      ‖c q * ((x : ℂ) - centredZero q)⁻¹‖ ≤ ‖c q‖ * (2 * ‖centredZero q‖⁻¹) := by
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx q
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_inv_ofReal_sub_centredZero_le hx q) (norm_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence hbound hpt hev
  rwa [tsum_zero] at h

/-! ### The explicit formula against probes without base point -/

/-- **The pairing with a probe is the Cauchy transform of the zero values.** For a profile of the
domain with square-summable zero values, `B G(p) = Σ_z L G(z) / (p - z)` off the zeros, absolutely
convergent. -/
theorem hasSum_zeroValues_cauchy {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hc : Summable fun q : XiZeroCopy => ‖negativeHalfLineLaplace (cx G) (centredZero q)‖ ^ 2)
    {p : ℂ} (hp : xi (1 / 2 + p) ≠ 0) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹)
      (globalRemainder G p) := by
  obtain ⟨δ, hδ, hball⟩ := exists_zeroFree_ball hp
  have hs1 : Summable fun q : XiZeroCopy =>
      negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹ :=
    (summable_norm_mul_inv_sub_centredZero hc hδ fun q => hball p (mem_ball_self hδ) q).of_norm
  have hre : Tendsto (fun x : ℝ => (x : ℂ)) atBot (comap Complex.re atBot) := by
    rw [tendsto_comap_iff]
    exact tendsto_id.congr fun x => (Complex.ofReal_re x).symm
  have h3 : Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) *
      ((p - centredZero q)⁻¹ - ((x : ℂ) - centredZero q)⁻¹)) atBot (𝓝 (globalRemainder G p)) :=
    (tendsto_tsum_sub_left hG hp).comp hre
  have hsplit : ∀ᶠ x : ℝ in atBot,
      (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) *
        ((p - centredZero q)⁻¹ - ((x : ℂ) - centredZero q)⁻¹)) =
      (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹) -
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * ((x : ℂ) - centredZero q)⁻¹ := by
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
    have hs2 : Summable fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx G) (centredZero q) * ((x : ℂ) - centredZero q)⁻¹ :=
      (summable_norm_mul_inv_sub_centredZero hc (by norm_num : (0 : ℝ) < 1 / 2) fun q =>
        half_le_norm_sub_centredZero (p := (x : ℂ))
          (by rw [Complex.ofReal_re, abs_of_nonpos (by linarith)]; linarith) q).of_norm
    calc (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) *
          ((p - centredZero q)⁻¹ - ((x : ℂ) - centredZero q)⁻¹))
        = ∑' q : XiZeroCopy, (negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹ -
            negativeHalfLineLaplace (cx G) (centredZero q) * ((x : ℂ) - centredZero q)⁻¹) :=
          tsum_congr fun q => by ring
      _ = (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹) -
            ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * ((x : ℂ) - centredZero q)⁻¹ :=
          (hs1.hasSum.sub hs2.hasSum).tsum_eq
  have h2 : Tendsto (fun x : ℝ =>
      (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹) -
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * ((x : ℂ) - centredZero q)⁻¹) atBot
      (𝓝 ((∑' q : XiZeroCopy, negativeHalfLineLaplace (cx G) (centredZero q) * (p - centredZero q)⁻¹) - 0)) :=
    tendsto_const_nhds.sub (tendsto_tsum_mul_inv_ofReal_sub_centredZero hc)
  have heq := tendsto_nhds_unique (h3.congr' hsplit) h2
  rw [sub_zero] at heq
  rw [heq]
  exact hs1.hasSum

/-! ### The critical state -/

/-- **(★) at one point.** For `Re w > -4`, `a L F(w) = -Σ_z L F(z) / (w + 8 - z)`, absolutely
convergent: the transform of the state is the Cauchy transform of its square-summable zero
values. -/
theorem criticalState_hasSum_starEquation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -4 < w.re) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) * (w + 8 - centredZero q)⁻¹)
      (-((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) w)) := by
  have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have h8 : (w + 8).re = w.re + 8 := by simp
    rw [h8]
    have := le_abs_self (w.re + 8)
    linarith)
  have h := hasSum_zeroValues_cauchy (criticalHalfLineEnergyDomain_of_groundState hF)
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) hxi
  rwa [← neg_eq_iff_eq_neg.mpr (criticalState_alias_mul_laplace hW hthreshold hF hw)] at h

/-- **The Mittag-Leffler expansion of the continuation.** Off the transported zeros the
continuation of `L F` is `-(1/a) Σ_z L F(z) / (w + 8 - z)`, absolutely convergent without
subtraction. -/
theorem criticalState_hasSum_stateMeromorphic {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ}
    (hw : xi (1 / 2 + (w + 8)) ≠ 0) :
    HasSum (fun q : XiZeroCopy => -(criticalAliasCoefficient W₀ : ℂ)⁻¹ *
        (negativeHalfLineLaplace (cx F) (centredZero q) * (w + 8 - centredZero q)⁻¹))
      (stateMeromorphic W₀ F w) := by
  have h := (hasSum_zeroValues_cauchy (criticalHalfLineEnergyDomain_of_groundState hF)
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) hw).mul_left
      (-(criticalAliasCoefficient W₀ : ℂ)⁻¹)
  have e : stateMeromorphic W₀ F w =
      -(criticalAliasCoefficient W₀ : ℂ)⁻¹ * globalRemainder F (w + 8) := by
    unfold stateMeromorphic
    ring
  rwa [← e] at h

/-- **The Cauchy system of the zeros.** The zero values `c_z = L F(z)` of the state are a
square-summable solution of `a c_{z'} = -Σ_z c_z / (z' + 8 - z)`. -/
theorem criticalState_hasSum_zeroValues_cauchy {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (q' : XiZeroCopy) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) * (centredZero q' + 8 - centredZero q)⁻¹)
      (-((criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (centredZero q'))) :=
  criticalState_hasSum_starEquation hW hthreshold hF
    (by have := (abs_lt.mp (abs_re_centredZero_lt q')).1; linarith)

/-- The solution is not zero: some zero value of the state does not vanish. -/
theorem criticalState_exists_zeroValue_ne_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) ≠ 0 := by
  by_contra hne
  have hall : ∀ q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) = 0 :=
    fun q => by_contra fun h => hne ⟨q, h⟩
  have hs := criticalState_hasSum_zeroNorm hW hthreshold hF
  have h0 : HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx F) (-centredZero q)) 0 := by
    have hz : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)) = fun _ => 0 :=
      funext fun q => by rw [hall q, zero_mul]
    rw [hz]
    exact hasSum_zero
  have heq := hs.unique h0
  have hneg := criticalState_zeroNorm_limit_neg hW hF
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re, Complex.zero_re] at hre
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
