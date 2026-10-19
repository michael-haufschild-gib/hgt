import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity

/-!
# Single-height positivity of `ζ` above the archimedean horizon

Let `f` be a `C²` profile supported in `[-a, a]`, and put `X = e^{2a}`. The localized Weil form of
`ζ` at height `2πξ` is `W_ζ(S_ξ f, S_ξ f)`, where `S_ξ f = e^{2πiξ·} f`.

**Lower bound** (`zetaZeroConfig_re_W_heightShift_ge`).
`Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − E(X) − 2S(a)) ‖f‖² − B_f²/(8(1 + π|ξ|))`. Here:
* `E(X) = 10 + 68√X` is the archimedean horizon exponent of `RHTower.ZetaSymbolArchimedeanHorizon`;
* `S(a) = sinh a − a` is the cost of the pole terms, which form a pair at depth `½`;
* `B_f = 4(‖f‖₁ + ‖f''‖₁)` controls the spectral tail of `f`.

The proof uses the localized explicit formula
`W_ζ(g, g) = h_k(i/2) + h_k(−i/2) + ∫ |h_g|²(μ + P_X)` (`zetaZeroConfig_W_eq_pole_add_integral`).
It splits the height axis at half the shift: near the shifted centre the symbol is at least
`(log(1 + π|ξ|/4) − E)/2π`, and the remaining mass is the spectral tail of `f`.

**Positivity at large heights** (`exists_zetaZeroConfig_re_W_heightShift_nonneg`). Every fixed
profile has nonnegative localized Weil forms at all sufficiently large heights.

**Calibration.** At height `T`, positivity holds once `log T ≳ 68√X`, that is, for prime lengths
`X ≲ (log T/68)²`. Consider an isolated pair of depth `½` in a background of local density `L`. By
`isolatedPairConfig_weil_nonneg_iff`, it becomes visible at `2 sinh a = 2L + 2a`, that is, at
`X ≈ 4L²`; for `ζ`, `L ≍ log T`. So the unconditional single-height range is the visibility range
of depth-`½` zeros, up to constants. A depth-`δ` pair becomes visible at `X ≈ (4δL)^{1/δ}`.
Single-height positivity for `X ≤ (log T)^{1/δ}` is therefore the localized form of a zero-free
region of depth `δ`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **The localized explicit formula of `ζ`.** For a `C²` test supported in `[-a, a]`,
`W_ζ(g, g) = h_k(i/2) + h_k(−i/2) + ∫ h_k(τ)(μ(τ) + P_X(τ)) dτ` with `k = g ⋆ g̃` and
`X = e^{2a}`. -/
theorem zetaZeroConfig_W_eq_pole_add_integral {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-a) a) :
    zetaZeroConfig.W g g = paperFT (EF.weilTest g g) (I / 2) + paperFT (EF.weilTest g g) (-I / 2) +
      ∫ τ : ℝ, paperFT (EF.weilTest g g) τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ) := by
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hkd : ContDiff ℝ 2 (EF.weilTest g g) := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc : HasCompactSupport (EF.weilTest g g) := EF.weilTest_hasCompactSupport hgc hgc
  have hgs' : tsupport g ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hks : tsupport (EF.weilTest g g) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset hgs' hgs'
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * a) hFk
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig (EF.weilTest g g) hkd hkc
  have hfac := EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (EF.weilTest g g) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand g g ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS, sub_eq_add_neg,
    EF.prime_term hkd.continuous hks hFk, EF.gamma_term,
    add_assoc (paperFT (EF.weilTest g g) (I / 2) + paperFT (EF.weilTest g g) (-I / 2)),
    ← integral_add hPX hμ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  push_cast
  ring

/-- The weight bound behind the tail estimate: beyond `|y|/2`, `(1 + |σ|)^{-4}` is at most
`(1 + |y|/2)^{-2} (1 + σ²)^{-1}`. -/
theorem inv_one_add_abs_pow_four_le {y σ : ℝ} (hσ : |y| / 2 < |σ|) :
    1 / ((1 + |σ|) ^ 2) ^ 2 ≤ 1 / (1 + |y| / 2) ^ 2 * (1 + σ ^ 2)⁻¹ := by
  have h1 : (1 + |y| / 2) ^ 2 ≤ (1 + |σ|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : 1 + σ ^ 2 ≤ (1 + |σ|) ^ 2 := by nlinarith [sq_abs σ, abs_nonneg σ]
  rw [← one_div (1 + σ ^ 2), div_mul_div_comm, one_mul]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [sq ((1 + |σ|) ^ 2)]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The transform of the Weil kernel of a height-shifted profile is the shifted spectral
density: `h_k(τ) = |h_f(τ + 2πξ)|²` for `k = S_ξ f ⋆ (S_ξ f)~`. -/
theorem paperFT_weilTest_heightShift_ofReal {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ξ τ : ℝ) :
    paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ =
      ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hgc : HasCompactSupport (heightShift ξ f) := hfc.mul_left
  have hg : Continuous (heightShift ξ f) := (by fun_prop : Continuous fun u : ℝ =>
    cexp (2 * π * I * ξ * u)).mul hf
  rw [paperFT_weilTest_self_ofReal hg hgc τ, paperFT_heightShift]
  push_cast
  rfl

/-- **The symbol estimate at height `2πξ`.** Let `w` be a symbol with
`w(τ) ≥ (log(1 + |τ|/4) − E)/2π`, and let `|h_f(· + 2πξ)|² w` be integrable. Then the pole terms of
`S_ξ f` plus `∫ |h_f(τ + 2πξ)|² w(τ) dτ` are at least
`(log(1 + π|ξ|/4) − E − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem re_pole_add_integral_symbol_heightShift_ge {a E : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) {w : ℝ → ℝ}
    (hw : ∀ τ, (Real.log (1 + |τ| / 4) - E) / (2 * π) ≤ w τ)
    (hwi : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * w τ) :
    (Real.log (1 + π * |ξ| / 4) - E - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      (paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (I / 2) +
        paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (-I / 2)).re +
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * w τ := by
  set g := heightShift ξ f with hgdef
  have hg : ContDiff ℝ 2 g := heightShift_contDiff hf ξ
  have hgs : tsupport g ⊆ Icc (-a) a := (tsupport_heightShift_subset ξ f).trans hfs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkdf : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkcf : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  set y : ℝ := 2 * π * ξ with hy
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hB
  set F : ℝ → ℝ := fun σ => ‖paperFT f σ‖ ^ 2 with hFdef
  set ℓ := Real.log (1 + |y| / 8) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith [abs_nonneg y])
  have hπ : 0 < 2 * π := by positivity
  have hnorm_g : ∀ u, ‖g u‖ = ‖f u‖ := fun u => by
    simp only [hgdef, heightShift, norm_mul]
    rw [show (2 * π * I * ξ * u : ℂ) = ((2 * π * ξ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hNg : ∫ t, ‖g t‖ ^ 2 = N := by
    rw [hN]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only [hnorm_g])
  have hFi : Integrable F := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkdf hkcf)).re.congr (Eventually.of_forall fun σ => ?_)
    simp only [paperFT_weilTest_self_ofReal hf.continuous hfc σ, RCLike.re_to_complex,
      Complex.ofReal_re, hFdef]
  have hFyi : Integrable fun τ : ℝ => F (τ + y) := hFi.comp_add_right y
  set Cu : ℝ := B ^ 2 / (1 + |y| / 2) ^ 2 with hCu
  have hui : Integrable fun τ : ℝ => Cu * (1 + (τ + y) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.const_mul Cu).comp_add_right y
  set c₁ := (ℓ - E) / (2 * π) with hc₁
  set c₂ := ℓ / (2 * π) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hsf : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (eq_zero_of_not_mem_Icc hfs fun hm => h (abs_le.mpr ⟨hm.1, hm.2⟩))
  have hptw : ∀ τ : ℝ, c₁ * F (τ + y) - c₂ * (Cu * (1 + (τ + y) ^ 2)⁻¹) ≤ F (τ + y) * w τ := by
    intro τ
    have hmu := hw τ
    have hF0 : 0 ≤ F (τ + y) := sq_nonneg _
    have hu0 : 0 ≤ Cu * (1 + (τ + y) ^ 2)⁻¹ := by positivity
    by_cases hσ : |τ + y| ≤ |y| / 2
    · have hτ : |y| / 2 ≤ |τ| := by
        have := abs_sub_abs_le_abs_sub y (τ + y)
        rw [show y - (τ + y) = -τ by ring, abs_neg] at this
        linarith
      have hlog : ℓ ≤ Real.log (1 + |τ| / 4) :=
        Real.log_le_log (by linarith [abs_nonneg y]) (by linarith)
      have hμ : c₁ ≤ w τ := by
        refine le_trans ?_ hmu
        rw [hc₁]
        exact div_le_div_of_nonneg_right (by linarith) hπ.le
      have e1 : F (τ + y) * c₁ ≤ F (τ + y) * w τ := mul_le_mul_of_nonneg_left hμ hF0
      nlinarith
    · rw [not_le] at hσ
      have hlog0 : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith [abs_nonneg τ])
      have hμ : c₁ - c₂ ≤ w τ := by
        refine le_trans ?_ hmu
        rw [hc₁, hc₂, ← sub_div]
        exact div_le_div_of_nonneg_right (by linarith) hπ.le
      have hdec : F (τ + y) ≤ Cu * (1 + (τ + y) ^ 2)⁻¹ := by
        have h := norm_paperFT_le_decay hf hsf (((τ + y : ℝ)) : ℂ)
        simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
          Complex.ofReal_re] at h
        have hsq : F (τ + y) ≤ (B / (1 + |τ + y|) ^ 2) ^ 2 := by
          rw [hFdef]
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
        refine hsq.trans ?_
        rw [div_pow, hCu]
        calc B ^ 2 / ((1 + |τ + y|) ^ 2) ^ 2 = B ^ 2 * (1 / ((1 + |τ + y|) ^ 2) ^ 2) := by ring
          _ ≤ B ^ 2 * (1 / (1 + |y| / 2) ^ 2 * (1 + (τ + y) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_four_le hσ) (sq_nonneg B)
          _ = B ^ 2 / (1 + |y| / 2) ^ 2 * (1 + (τ + y) ^ 2)⁻¹ := by ring
      have e1 : F (τ + y) * (c₁ - c₂) ≤ F (τ + y) * w τ := mul_le_mul_of_nonneg_left hμ hF0
      have e2 : c₂ * F (τ + y) ≤ c₂ * (Cu * (1 + (τ + y) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hdec hc₂0
      nlinarith
  have hlow : Integrable fun τ : ℝ => c₁ * F (τ + y) - c₂ * (Cu * (1 + (τ + y) ^ 2)⁻¹) :=
    (hFyi.const_mul c₁).sub (hui.const_mul c₂)
  have hmono := integral_mono hlow hwi hptw
  have hFint : ∫ τ : ℝ, F (τ + y) = 2 * π * N := by
    rw [integral_add_right_eq_self (fun σ => F σ) y, hFdef]
    exact integral_norm_sq_paperFT_eq hf hfs
  have huint : ∫ τ : ℝ, Cu * (1 + (τ + y) ^ 2)⁻¹ = Cu * π := by
    rw [integral_add_right_eq_self (fun σ => Cu * (1 + σ ^ 2)⁻¹) y, integral_const_mul,
      integral_univ_inv_one_add_sq]
  rw [integral_sub (hFyi.const_mul c₁) (hui.const_mul c₂), integral_const_mul,
    integral_const_mul, hFint, huint] at hmono
  have hpole := neg_le_re_pole_terms ha hg.continuous hgs
  rw [hNg] at hpole
  have hyabs : |y| = 2 * π * |ξ| := by
    rw [hy, abs_mul, abs_of_pos hπ]
  have hℓy : ℓ ≤ |y| / 8 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |y| / 8)
    linarith
  have htail : c₂ * (Cu * π) ≤ B ^ 2 / (8 * (1 + π * |ξ|)) := by
    have hy2 : 1 + |y| / 2 = 1 + π * |ξ| := by rw [hyabs]; ring
    have hpos : 0 < 1 + π * |ξ| := by positivity
    rw [hc₂, hCu, hy2]
    have hℓ' : ℓ ≤ π * |ξ| / 4 := by rw [hyabs] at hℓy; linarith
    set p := 1 + π * |ξ| with hp
    have hrw : ℓ / (2 * π) * (B ^ 2 / p ^ 2 * π) = ℓ * B ^ 2 / (2 * p ^ 2) := by
      field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : 8 * ℓ ≤ 2 * p := by
      have : 0 ≤ π * |ξ| := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ B ^ 2 * p)
    nlinarith [this]
  have hlogeq : Real.log (1 + π * |ξ| / 4) = ℓ := by
    rw [hℓ, hyabs]
    ring_nf
  rw [hlogeq]
  have hc₁N : c₁ * (2 * π * N) = (ℓ - E) * N := by
    rw [hc₁]
    field_simp
  linarith

/-- **Lower bound at height `2πξ`.** For a `C²` profile supported in `[-a, a]`,
`Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − E(e^{2a}) − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem zetaZeroConfig_re_W_heightShift_ge {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
        2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hsym : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 *
      (mu τ + PX (Real.exp (2 * a)) τ) := by
    refine (integrable_paperFT_mul_mu_add_PX hkd hkc (2 * a)).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have h := re_pole_add_integral_symbol_heightShift_ge ha hf hfs ξ
    (fun τ => mu_add_PX_ge (Real.exp_pos (2 * a)).le τ) hsym
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [zetaZeroConfig_W_eq_pole_add_integral hg hgs, Complex.add_re, hμre]
  exact h

/-- **Positivity at large heights.** Every `C²` profile of compact support has nonnegative
localized Weil forms `W_ζ(S_ξ f, S_ξ f)` at all sufficiently large heights. -/
theorem exists_zetaZeroConfig_re_W_heightShift_nonneg {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ Ξ : ℝ, ∀ ξ : ℝ, Ξ ≤ |ξ| →
      0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨a, ha, hfa⟩ := exists_radius_of_hasCompactSupport hfc
  have hfs : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra h
    exact hu (hfa u (lt_of_not_ge fun h' => h (abs_le.mp h')))
  have hfsq : Integrable fun t => ‖f t‖ ^ 2 :=
    (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := -a) (b := a))
      fun u (hu : u ∉ Icc (-a) a) => by simp [eq_zero_of_not_mem_Icc hfs hu])
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  rcases hN0.lt_or_eq with hNpos | hNzero
  · set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hB
    set E' := horizonExponent (Real.exp (2 * a)) + 2 * pairEnergy (1 / 2) a + 1 with hE'
    refine ⟨max (4 / π * Real.exp E') (B ^ 2 / (8 * π * N)), fun ξ hξ => ?_⟩
    have h1 : 4 / π * Real.exp E' ≤ |ξ| := le_trans (le_max_left _ _) hξ
    have h2 : B ^ 2 / (8 * π * N) ≤ |ξ| := le_trans (le_max_right _ _) hξ
    have hlog : E' ≤ Real.log (1 + π * |ξ| / 4) := by
      have hexp : Real.exp E' ≤ 1 + π * |ξ| / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at h1
        linarith
      calc E' = Real.log (Real.exp E') := (Real.log_exp E').symm
        _ ≤ Real.log (1 + π * |ξ| / 4) := Real.log_le_log (Real.exp_pos _) hexp
    have htail : B ^ 2 / (8 * (1 + π * |ξ|)) ≤ N := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h2
      nlinarith [abs_nonneg ξ, Real.pi_pos]
    have hbound := zetaZeroConfig_re_W_heightShift_ge ha hf hfs ξ
    have hcoef : N ≤ (Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
        2 * pairEnergy (1 / 2) a) * N := by
      have : 1 ≤ Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
          2 * pairEnergy (1 / 2) a := by rw [hE'] at hlog; linarith
      nlinarith
    linarith
  · refine ⟨0, fun ξ _ => ?_⟩
    have hae : (fun t => ‖f t‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hfsq).mp hNzero.symm
    have heq : (fun t => ‖f t‖ ^ 2) = fun _ => (0 : ℝ) :=
      (Continuous.ae_eq_iff_eq volume (hf.continuous.norm.pow 2) continuous_const).mp hae
    have hf0 : ∀ t, f t = 0 := fun t => by
      have := congrFun heq t
      simpa using this
    have hg0 : heightShift ξ f = 0 := by
      funext u
      simp [heightShift, hf0 u]
    rw [hg0]
    simp [ZeroConfig.W, ZeroConfig.Wsummand, paperFT]

end GaloisForLFunctions.SquareRootThreshold
