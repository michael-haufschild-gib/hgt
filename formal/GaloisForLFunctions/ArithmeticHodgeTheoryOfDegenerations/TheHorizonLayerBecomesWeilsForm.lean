import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockOnTheArithmeticSide
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy

/-!
# The horizon layer becomes Weil's form

The exact horizon formula compares the normalized complete form of a horizon block, divided by the
overlap, with Weil's form of the synthesized test `H(y) = e^{y/2} h(y)`, frequency by frequency.

* **Below the grid** (`tendsto_lowFrequency`): on `|τ| ≤ N e^{−A}` the integrand
  `‖φ̂(wτ)‖² |D_x(τ)|²/N ν(τ)` converges to `(∫φ)² |ĥ(½ + iτ)|² ν(τ)` and is dominated by
  `C (1 + τ²)⁻¹ (A_ν + log(2 + |τ|))` (Kuzmin–Landau), so its integral converges.
* **Above the grid** (`abs_highFrequency_le`): the aliasing tails are at most
  `2 K_al (A_ν + 2 + log N)/c^p` (mean values of the block's Dirichlet polynomial).
* **The pole terms** (`tendsto_alphaPlus`, `tendsto_alphaMinus`) converge to `(∫φ) ĥ(0)` and
  `(∫φ) ĥ(1)`.

Hence, for a profile with `‖φ̂(u)‖² ≤ C_φ (1 + |u|)^{−p}`, `p > 1`:

* **Two-sided horizon theorem** (`horizon_layer_two_sided`): eventually
  `|c_N⁻¹ ⟨W x, x⟩ − κ_φ Q(H)| ≤ ε + K (1 + log N)/c_N^p`, `κ_φ = (∫φ)²/∫φ²`;
* **Past the critical curve** (`tendsto_horizon_layer_supercritical`): if `log N/c_N^p → 0` the
  horizon layer, divided by the overlap, converges to `κ_φ Q(H)`;
* **At the critical curve** (`horizon_layer_criticalCurve`): if `c_N^p/log N → K_c` it is
  `κ_φ Q(H)` up to `K/K_c`.

The second-order term of the degeneration on the horizon layer is Weil's form of the synthesized
test, with a coercive aliasing part inversely proportional to the multiple of the critical curve.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

variable {h : ℝ → ℝ} {A : ℝ}

/-! ### Regularity of the window profile -/

theorem hasCompactSupport_of_window (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    HasCompactSupport h :=
  HasCompactSupport.intro isCompact_Icc fun y hy => hsupp y hy

/-- A `C²` window profile is bounded and Lipschitz. -/
theorem exists_bound_lipschitz (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ Bh L : ℝ, (∀ y, |h y| ≤ Bh) ∧ ∀ u v, |h u - h v| ≤ L * |u - v| := by
  have hc := hasCompactSupport_of_window hsupp
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hh.continuous
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hh (by norm_num)
  refine ⟨B, K, fun y => by simpa [Real.norm_eq_abs] using hB y, fun u v => ?_⟩
  have := hK.dist_le_mul u v
  simpa [Real.dist_eq] using this

/-! ### The synthesized test on the arithmetic side -/

theorem paperFT_halfWeight_gammaOf (h : ℝ → ℝ) (s : ℂ) :
    paperFT (cx (halfWeight h)) (gammaOf s) = horizonTransform h s := by
  unfold paperFT horizonTransform
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [cx, halfWeight, gammaOf]
  push_cast
  rw [mul_comm (Complex.exp _) (h y : ℂ), mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem gammaOf_zero : gammaOf 0 = Complex.I / 2 := by
  rw [gammaOf, div_eq_iff Complex.I_ne_zero]
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

theorem gammaOf_one : gammaOf 1 = -Complex.I / 2 := by
  rw [gammaOf, div_eq_iff Complex.I_ne_zero]
  linear_combination (1 / 2 : ℂ) * Complex.I_sq

theorem gammaOf_half_add (τ : ℝ) : gammaOf (1 / 2 + Complex.I * τ) = τ := by
  rw [gammaOf, div_eq_iff Complex.I_ne_zero]
  ring

theorem tsupport_halfWeight_subset (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    tsupport (halfWeight h) ⊆ Set.Icc (-A) 0 := by
  refine closure_minimal (fun y hy => ?_) isClosed_Icc
  by_contra hout
  exact hy (by simp only [halfWeight, hsupp y hout, mul_zero])

/-- **Weil's form of the synthesized test** on the arithmetic side. -/
theorem weilQuad_halfWeight_eq (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) :
    weilQuad (halfWeight h) =
      (horizonTransform h 0 * conj (horizonTransform h 1) +
        horizonTransform h 1 * conj (horizonTransform h 0)).re +
      ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
        nuSymbol (Real.exp (2 * (A + 1))) τ := by
  have hH := contDiff_halfWeight hh
  have hHs : tsupport (halfWeight h) ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    (tsupport_halfWeight_subset hsupp).trans (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hHc := hasCompactSupport_halfWeight (hasCompactSupport_of_window hsupp)
  have hcx : Continuous (cx (halfWeight h)) := Complex.continuous_ofReal.comp hH.continuous
  have hcxc : HasCompactSupport (cx (halfWeight h)) := hHc.comp_left Complex.ofReal_zero
  rw [weilQuad_eq_pole_add_symbol hH hHs, EF.paperFT_weilTest hcx hcx hcxc hcxc,
    EF.paperFT_weilTest hcx hcx hcxc hcxc]
  have hc1 : conj (Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc1, hc2, ← gammaOf_zero, ← gammaOf_one, paperFT_halfWeight_gammaOf,
    paperFT_halfWeight_gammaOf]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  conv_lhs => rw [← gammaOf_half_add τ, paperFT_halfWeight_gammaOf]

/-! ### The pole amplitudes -/

theorem paperFT_cx_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (paperFT (cx φ)) :=
  (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
    (hφc.comp_left Complex.ofReal_zero)).continuous

theorem tendsto_atom_factor {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {c : ℕ → ℝ} (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) (z : ℂ) :
    Tendsto (fun N : ℕ => paperFT (cx φ) (((c N / N : ℝ) : ℂ) * z)) atTop
      (𝓝 (((∫ u, φ u : ℝ) : ℂ))) := by
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ) * z) atTop (𝓝 0) := by
    have := (hcN.ofReal).mul_const z
    simpa using this
  rw [← paperFT_cx_zero]
  exact ((paperFT_cx_continuous hφ hφc).tendsto 0).comp hw

theorem tendsto_alphaPlus {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {c : ℕ → ℝ}
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => alphaPlus φ h (c N) N) atTop
      (𝓝 (((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0)) := by
  have hD := tendsto_horizonDirichlet hh hsupp hA 0
  simp only [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at hD
  exact (tendsto_atom_factor hφ hφc hcN _).mul hD

theorem tendsto_alphaMinus {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {c : ℕ → ℝ}
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => alphaMinus φ h (c N) N) atTop
      (𝓝 (((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1)) := by
  have hD := tendsto_horizonDirichlet hh hsupp hA 1
  simp only [gammaOf_one] at hD
  refine ((tendsto_atom_factor hφ hφc hcN (-Complex.I / 2)).mul hD).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [alphaMinus, Complex.cpow_neg_one]
  push_cast
  field_simp

/-- The pole part converges to `(∫φ)²` times the pole part of the synthesized test. -/
theorem tendsto_polePart {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {c : ℕ → ℝ}
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
        alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re) atTop
      (𝓝 ((∫ u, φ u) ^ 2 * (horizonTransform h 0 * conj (horizonTransform h 1) +
        horizonTransform h 1 * conj (horizonTransform h 0)).re)) := by
  have hp := tendsto_alphaPlus hφ hφc hh hsupp hA hcN
  have hm := tendsto_alphaMinus hφ hφc hh hsupp hA hcN
  have hlim := ((hp.mul (Complex.continuous_conj.tendsto _ |>.comp hm)).add
    (hm.mul (Complex.continuous_conj.tendsto _ |>.comp hp)))
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hval : (((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0 *
      conj (((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1) +
      ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1 *
      conj (((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0)).re =
      (∫ u, φ u) ^ 2 * (horizonTransform h 0 * conj (horizonTransform h 1) +
        horizonTransform h 1 * conj (horizonTransform h 0)).re := by
    rw [map_mul, map_mul, Complex.conj_ofReal,
      show ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0 *
        (((∫ u, φ u : ℝ) : ℂ) * conj (horizonTransform h 1)) +
        ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1 *
        (((∫ u, φ u : ℝ) : ℂ) * conj (horizonTransform h 0)) =
        (((∫ u, φ u) ^ 2 : ℝ) : ℂ) * (horizonTransform h 0 * conj (horizonTransform h 1) +
          horizonTransform h 1 * conj (horizonTransform h 0)) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [← hval]
  exact hre

/-! ### Below the grid -/

theorem norm_sq_div_eq {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) (τ : ℝ) :
    ‖dirichletPoly N x τ‖ ^ 2 / N =
      ‖((N : ℝ) : ℂ) ^ (-(1 / 2 + Complex.I * τ)) *
        dirichletPoly N x (gammaOf (1 / 2 + Complex.I * τ))‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hre : (-(1 / 2 + Complex.I * (τ : ℂ))).re = -(1 / 2) := by simp
  have hpow : ((N : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [gammaOf_half_add, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre, hpow,
    div_eq_mul_inv, mul_comm]

/-- Pointwise convergence of the symbol integrand. -/
theorem tendsto_horizonSymbolIntegrand {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) {c : ℕ → ℝ}
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) (X τ : ℝ) :
    Tendsto (fun N : ℕ => horizonSymbolIntegrand φ h (c N) N X τ) atTop
      (𝓝 ((∫ u, φ u) ^ 2 * ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
        nuSymbol X τ)) := by
  have h1 := ((continuous_norm.tendsto _).comp (tendsto_atom_factor hφ hφc hcN (τ : ℂ))).pow 2
  have h2 := ((continuous_norm.tendsto _).comp
    (tendsto_horizonDirichlet hh hsupp hA (1 / 2 + Complex.I * τ))).pow 2
  have h3 := (h1.mul h2).mul_const (nuSymbol X τ)
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp_apply, horizonSymbolIntegrand]
  rw [norm_sq_div_eq hN]

/-- `log(2 + t) ≤ 2√2 (1 + t)^{1/2}`. -/
theorem log_two_add_le_rpow {t : ℝ} (ht : 0 ≤ t) :
    Real.log (2 + t) ≤ 2 * Real.sqrt 2 * (1 + t) ^ (1 / 2 : ℝ) := by
  have h1 : Real.log (2 + t) = 2 * Real.log (Real.sqrt (2 + t)) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 + t by linarith))
  have h3 : Real.sqrt (2 + t) ≤ Real.sqrt 2 * (1 + t) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith [Real.sqrt_nonneg (2 + t)]

/-- The dominating function `(1 + τ²)⁻¹ (A_ν + log(2 + |τ|))` is integrable. -/
theorem integrable_dominator {Aν : ℝ} (hAν : 0 ≤ Aν) :
    Integrable (fun τ : ℝ => (1 + τ ^ 2)⁻¹ * (Aν + Real.log (2 + |τ|))) := by
  have hint : Integrable (fun τ : ℝ => (2 * (Aν + 2 * Real.sqrt 2)) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine hint.mono' (by fun_prop) (Eventually.of_forall fun τ => ?_)
  have ht : 0 ≤ |τ| := abs_nonneg τ
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  have hp : 0 < 1 + |τ| := by linarith
  have hsq : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]
  have hlog := log_two_add_le_rpow ht
  have hhalf : (1 : ℝ) ≤ (1 + |τ|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hsplit : (1 + |τ|) ^ (-(3 / 2 : ℝ)) = (1 + |τ|) ^ (1 / 2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
    rw [show -(3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hp, Real.rpow_two, div_eq_mul_inv]
  rw [hsplit]
  have hinv : (1 + τ ^ 2)⁻¹ ≤ 2 * ((1 + |τ|) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    calc (1 + |τ|) ^ 2 * (1 + τ ^ 2)⁻¹ ≤ (2 * (1 + τ ^ 2)) * (1 + τ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 2 := by field_simp
  have hnum : Aν + Real.log (2 + |τ|) ≤ (Aν + 2 * Real.sqrt 2) * (1 + |τ|) ^ (1 / 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  calc (1 + τ ^ 2)⁻¹ * (Aν + Real.log (2 + |τ|))
      ≤ (2 * ((1 + |τ|) ^ 2)⁻¹) * ((Aν + 2 * Real.sqrt 2) * (1 + |τ|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hinv hnum (by positivity) (by positivity)
    _ = _ := by ring

/-! ### Integrability of the symbol integrand -/

theorem hasCompactSupport_centredHorizonTest {φ : ℝ → ℝ}
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) : HasCompactSupport (centredHorizonTest φ h c N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := fun u hu => by
    unfold atomDilate
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  exact (hasCompactSupport_atomicTest hg N _).comp_homeomorph (Homeomorph.addRight _)

theorem integrable_horizonSymbolIntegrand {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) (L : ℝ) :
    Integrable (horizonSymbolIntegrand φ h c N (Real.exp L)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hTd : ContDiff ℝ 2 (cx (centredHorizonTest φ h c N)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_centredHorizonTest hφ h c N)
  have hTc : HasCompactSupport (cx (centredHorizonTest φ h c N)) :=
    (hasCompactSupport_centredHorizonTest hφsupp h hc hN).comp_left Complex.ofReal_zero
  have hk := RHTower.integrable_paperFT_mul_mu_add_PX
    (EF.weilTest_contDiff hTd hTd.continuous hTc) (EF.weilTest_hasCompactSupport hTc hTc) L
  have hre : Integrable (fun τ : ℝ => (paperFT (EF.weilTest (cx (centredHorizonTest φ h c N))
      (cx (centredHorizonTest φ h c N))) τ * ((mu τ + PX (Real.exp L) τ : ℝ) : ℂ)).re) := hk.re
  have hfun : (fun τ : ℝ => (paperFT (EF.weilTest (cx (centredHorizonTest φ h c N))
      (cx (centredHorizonTest φ h c N))) τ * ((mu τ + PX (Real.exp L) τ : ℝ) : ℂ)).re) =
      fun τ => ((c / N) ^ 2 * N) * horizonSymbolIntegrand φ h c N (Real.exp L) τ := by
    funext τ
    rw [RHTower.paperFT_weilTest_self_ofReal hTd.continuous hTc τ, ← Complex.ofReal_mul,
      Complex.ofReal_re, norm_sq_paperFT_centredHorizonTest hφ.continuous hφc h hc hN,
      horizonSymbolIntegrand, nuSymbol]
    field_simp
  rw [hfun] at hre
  have hconst : ((c / N) ^ 2 * N : ℝ) ≠ 0 := by positivity
  refine (hre.const_mul ((c / N) ^ 2 * N)⁻¹).congr (Eventually.of_forall fun τ => ?_)
  simp only
  field_simp

/-! ### Above the grid -/

/-- The two aliasing tails bound the part of the symbol integral above the grid. -/
theorem abs_highFrequency_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {X Aν Bh : ℝ} (hAν : 0 ≤ Aν) (hν : ∀ τ, |nuSymbol X τ| ≤ Aν + Real.log (2 + |τ|))
    (hX : ∃ L, X = Real.exp L)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh)
    {N : ℕ} (hNA : Real.exp A ≤ N) {c : ℝ} (hc : 0 < c) :
    |(∫ τ, horizonSymbolIntegrand φ h c N X τ) -
        ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
          horizonSymbolIntegrand φ h c N X τ| ≤
      2 * (aliasConst Cφ p A Bh * (Aν + 2 + Real.log N) / c ^ p) := by
  obtain ⟨L, rfl⟩ := hX
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  set T₀ : ℝ := (N : ℝ) * Real.exp (-A) with hT₀
  set S := horizonSymbolIntegrand φ h c N (Real.exp L) with hS
  have hSi : Integrable S := integrable_horizonSymbolIntegrand hφ hφsupp h hc hN L
  -- the integral off the window
  have hcompl : (∫ τ, S τ) - ∫ τ in Set.Icc (-T₀) T₀, S τ = ∫ τ in (Set.Icc (-T₀) T₀)ᶜ, S τ := by
    rw [← integral_add_compl measurableSet_Icc hSi]; ring
  rw [hcompl]
  refine (abs_integral_le_integral_abs).trans ?_
  have hunion : (Set.Icc (-T₀) T₀)ᶜ = Set.Iio (-T₀) ∪ Set.Ioi T₀ := by
    ext τ; simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hτ; by_contra hc'; push Not at hc'; exact hτ ⟨hc'.1, hc'.2⟩
    · rintro (hτ | hτ) ⟨h1, h2⟩ <;> linarith
  have habsi : Integrable fun τ => |S τ| := hSi.abs
  rw [hunion, setIntegral_union (Set.disjoint_left.mpr fun τ h1 h2 => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at h1 h2
      have : 0 ≤ T₀ := by positivity
      linarith) measurableSet_Ioi habsi.integrableOn habsi.integrableOn]
  -- each tail is an aliasing integral
  have hpos : ∀ τ, |S τ| = aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) 1 τ := by
    intro τ
    simp only [hS, horizonSymbolIntegrand, aliasIntegrand, one_mul]
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hneg : ∀ τ, |S (-τ)| = aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) (-1) τ := by
    intro τ
    simp only [hS, horizonSymbolIntegrand, aliasIntegrand, neg_one_mul]
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hI1 : ∫ τ in Set.Ioi T₀, |S τ| ≤ aliasConst Cφ p A Bh * (Aν + 2 + Real.log N) / c ^ p := by
    have := integral_aliasing_le hp hCφ hdecay hAν hν hsupp hA hB hNA hc (Or.inl rfl)
      (by rw [show aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) 1 = fun τ => |S τ| from
        funext fun τ => (hpos τ).symm]; exact habsi.integrableOn)
    rwa [show aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) 1 = fun τ => |S τ| from
      funext fun τ => (hpos τ).symm] at this
  have hI2 : ∫ τ in Set.Iio (-T₀), |S τ| ≤
      aliasConst Cφ p A Bh * (Aν + 2 + Real.log N) / c ^ p := by
    have hcomp : Integrable fun τ => |S (-τ)| := habsi.comp_neg
    have := integral_aliasing_le hp hCφ hdecay hAν hν hsupp hA hB hNA hc (Or.inr rfl)
      (by rw [show aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) (-1) =
          fun τ => |S (-τ)| from funext fun τ => (hneg τ).symm]; exact hcomp.integrableOn)
    rw [show aliasIntegrand φ (nuSymbol (Real.exp L)) h N (c / N) (-1) = fun τ => |S (-τ)| from
      funext fun τ => (hneg τ).symm] at this
    simp only [integral_comp_neg_Ioi (f := fun τ => |S τ|)] at this
    rw [← integral_Iic_eq_integral_Iio]
    exact this
  linarith

/-! ### The two-sided horizon theorem -/

/-- **Below the grid**: the symbol integral over `|τ| ≤ N e^{−A}` converges to `(∫φ)²` times the
symbol integral of the synthesized test (dominated convergence; Kuzmin–Landau domination). -/
theorem tendsto_lowFrequency {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A)), horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ)
      atTop (𝓝 ((∫ u, φ u) ^ 2 * ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
        nuSymbol (Real.exp (2 * (A + 1))) τ)) := by
  set I₁ := ∫ u, φ u with hI₁
  set X := Real.exp (2 * (A + 1)) with hX
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (X := X) (Real.exp_pos _).le
  obtain ⟨Bh, Lh, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  set G : ℝ → ℝ := fun τ => ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 * nuSymbol X τ
    with hG
  show Tendsto _ atTop (𝓝 (I₁ ^ 2 * ∫ τ, G τ))
  set Cd := 2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 * windowConst A Bh Lh ^ 2) with hCd
  set I₀ := ∫ u, |φ u| with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun u => abs_nonneg _
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  set bound : ℝ → ℝ := fun τ => I₀ ^ 2 * Cd * ((1 + τ ^ 2)⁻¹ * (Aν + Real.log (2 + |τ|)))
    with hbound
  have hbi : Integrable bound := (integrable_dominator hAν).const_mul _
  have hrw : ∀ N : ℕ, ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
      horizonSymbolIntegrand φ h (c N) N X τ = ∫ τ, Set.indicator (Set.Icc
        (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
        (horizonSymbolIntegrand φ h (c N) N X) τ := fun N =>
    (integral_indicator measurableSet_Icc).symm
  simp_rw [hrw]
  rw [← integral_const_mul]
  refine tendsto_integral_of_dominated_convergence (F := fun (N : ℕ) (τ : ℝ) => Set.indicator
    (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
    (horizonSymbolIntegrand φ h (c N) N X) τ) (f := fun τ => I₁ ^ 2 * G τ) bound
    (fun N => ?_) hbi ?_ ?_
  · rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have h00 : horizonSymbolIntegrand φ h (c 0) 0 X = 0 := by
        funext τ; simp [horizonSymbolIntegrand]
      rw [h00]
      simp only [Set.indicator_zero', Pi.zero_apply]
      exact aestronglyMeasurable_const
    · exact ((integrable_horizonSymbolIntegrand hφ hφsupp h (hc N) h0 (2 * (A + 1))).indicator
        measurableSet_Icc).aestronglyMeasurable
  · refine fun N => Eventually.of_forall fun τ => ?_
    have hb0 : 0 ≤ bound τ := by
      simp only [hbound]
      have : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
      positivity
    by_cases hτ : τ ∈ Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A))
    · rw [Set.indicator_of_mem hτ, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simpa [horizonSymbolIntegrand] using hb0
      have hτN : |τ| ≤ (N : ℝ) * Real.exp (-A) := abs_le.mpr ⟨hτ.1, hτ.2⟩
      have hD := horizonDirichlet_sq_div_le hsupp hA hB hL h0 hτN
      rw [← hCd] at hD
      have hΦ : ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ≤ I₀ := by
        have := RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) (c N / N * τ)
        push_cast at this
        simpa [cx, Complex.norm_real, Real.norm_eq_abs] using this
      have hΦ2 : ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ I₀ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hΦ 2
      have hν' := hν τ
      have hDn : 0 ≤ ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N := by positivity
      simp only [horizonSymbolIntegrand, hbound]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hDn]
      calc ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) * |nuSymbol X τ|
          ≤ I₀ ^ 2 * (Cd / (1 + τ ^ 2)) * (Aν + Real.log (2 + |τ|)) :=
            mul_le_mul (mul_le_mul hΦ2 hD hDn (by positivity)) hν' (abs_nonneg _)
              (by positivity)
        _ = I₀ ^ 2 * Cd * ((1 + τ ^ 2)⁻¹ * (Aν + Real.log (2 + |τ|))) := by ring
    · rw [Set.indicator_of_notMem hτ, norm_zero]; exact hb0
  · refine Eventually.of_forall fun τ => ?_
    have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
    have hin : ∀ᶠ N : ℕ in atTop, τ ∈ Set.Icc (-((N : ℝ) * Real.exp (-A)))
        ((N : ℝ) * Real.exp (-A)) := by
      filter_upwards [hT.eventually (eventually_ge_atTop |τ|)] with N hN
      exact ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have hl := tendsto_horizonSymbolIntegrand hφ.continuous hφc hh.continuous hsupp hA hcN X τ
    refine (hl.congr' ?_).trans (by simp only [hG]; rw [mul_assoc])
    filter_upwards [hin] with N hN
    rw [Set.indicator_of_mem hN]


/-- **Two-sided horizon theorem.** For a `C²` profile on `[0, 1]` with `‖φ̂(u)‖² ≤ C_φ(1 + |u|)^{−p}`,
`p > 1`, and a `C²` window profile `h` on `[−A, 0]`, there is a constant `K` such that for every
overlap schedule with `c_N/N → 0` and every `ε > 0`, eventually
`|c_N⁻¹ ⟨W_{c_N,N} x_N, x_N⟩ − κ_φ Q(H)| ≤ ε + K (1 + log N)/c_N^p`, where
`⟨W x, x⟩ = Q(atomic test)/∫g²`, `κ_φ = (∫φ)²/∫φ²` and `H = e^{y/2} h`. -/
theorem horizon_layer_two_sided {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℕ → ℝ, (∀ N, 0 < c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |(c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2) -
        (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h)| ≤
        ε + K * (1 + Real.log N) / c N ^ p := by
  set M := ∫ u, φ u ^ 2 with hM
  set I₁ := ∫ u, φ u with hI₁
  set X := Real.exp (2 * (A + 1)) with hX
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (X := X) (Real.exp_pos _).le
  obtain ⟨Bh, Lh, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  set Kal := aliasConst Cφ p A Bh with hKal
  have hKal0 : 0 ≤ Kal := by
    have hr1 : (2 : ℝ) ^ (1 - p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : 0 < 1 - (2 : ℝ) ^ (1 - p) := by linarith
    rw [hKal, aliasConst]; positivity
  refine ⟨2 * Kal * (Aν + 2) / M, by positivity, fun c hc hcN ε hε => ?_⟩
  -- the limit pieces
  have hpole := tendsto_polePart hφ.continuous hφc hh.continuous hsupp hA hcN
  set P := (horizonTransform h 0 * conj (horizonTransform h 1) +
    horizonTransform h 1 * conj (horizonTransform h 0)).re with hP
  set G : ℝ → ℝ := fun τ => ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 * nuSymbol X τ
    with hG
  have hlow : Tendsto (fun N : ℕ => ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A)), horizonSymbolIntegrand φ h (c N) N X τ) atTop
      (𝓝 (I₁ ^ 2 * ∫ τ, G τ)) := tendsto_lowFrequency hφ hφsupp hh hA hsupp hc hcN
  have hWH := weilQuad_halfWeight_eq hh hsupp hA
  -- eventually all estimates hold
  have hevpole := (hpole.const_mul M⁻¹).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hevlow := (hlow.const_mul M⁻¹).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hNA : ∀ᶠ N : ℕ in atTop, Real.exp A ≤ N := by
    obtain ⟨n, hn⟩ := exists_nat_ge (Real.exp A)
    exact eventually_ge_atTop n |>.mono fun N hN => hn.trans (by exact_mod_cast hN)
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_one hN0] at h1
    exact h1.le
  filter_upwards [hevpole, hevlow, hNA, hcle, eventually_ge_atTop 1] with N h1 h2 hNA' hcle' hN
  rw [Real.dist_eq] at h1 h2
  have hform := horizonForm_eq hφ hφsupp hφ2 hsupp hA (hc N) hN hcle'
  rw [hform, hWH]
  have hhigh := abs_highFrequency_le hφ hφsupp hp hCφ hdecay hAν hν ⟨_, rfl⟩ hsupp hA hB hNA'
    (hc N) (N := N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hM0 : 0 < M := hφ2
  have hcp : 0 < c N ^ p := Real.rpow_pos_of_pos (hc N) p
  set Sint := ∫ τ, horizonSymbolIntegrand φ h (c N) N X τ
  set Sicc := ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
    horizonSymbolIntegrand φ h (c N) N X τ
  set poleN := (alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
    alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re
  have hsplit : poleN / M + M⁻¹ * Sint - I₁ ^ 2 / M * (P + ∫ τ, G τ) =
      (M⁻¹ * poleN - M⁻¹ * (I₁ ^ 2 * P)) + M⁻¹ * (Sint - Sicc) +
        (M⁻¹ * Sicc - M⁻¹ * (I₁ ^ 2 * ∫ τ, G τ)) := by ring
  have hhigh' : |M⁻¹ * (Sint - Sicc)| ≤ 2 * Kal * (Aν + 2) / M * (1 + Real.log N) / c N ^ p := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hM0)]
    have hle : Aν + 2 + Real.log N ≤ (Aν + 2) * (1 + Real.log N) := by nlinarith
    calc M⁻¹ * |Sint - Sicc| ≤ M⁻¹ * (2 * (Kal * (Aν + 2 + Real.log N) / c N ^ p)) :=
          mul_le_mul_of_nonneg_left hhigh (inv_pos.mpr hM0).le
      _ = (2 * Kal / (M * c N ^ p)) * (Aν + 2 + Real.log N) := by field_simp
      _ ≤ (2 * Kal / (M * c N ^ p)) * ((Aν + 2) * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 * Kal * (Aν + 2) / M * (1 + Real.log N) / c N ^ p := by field_simp
  rw [show (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) = I₁ ^ 2 / M from rfl, hsplit]
  refine (abs_add_three _ _ _).trans ?_
  have h1' : |M⁻¹ * poleN - M⁻¹ * (I₁ ^ 2 * P)| ≤ ε / 2 := h1.le
  have h2' : |M⁻¹ * Sicc - M⁻¹ * (I₁ ^ 2 * ∫ τ, G τ)| ≤ ε / 2 := h2.le
  linarith

/-! ### Past the critical curve and at it -/

/-- **Past the critical curve the horizon layer is Weil's form.** If `(1 + log N)/c_N^p → 0`, the
normalized complete form of the horizon block of `h`, divided by the overlap, converges to
`κ_φ Q(H)`. -/
theorem tendsto_horizon_layer_supercritical {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))
    (hsuper : Tendsto (fun N : ℕ => (1 + Real.log N) / c N ^ p) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h))) := by
  obtain ⟨K, hK0, hK⟩ := horizon_layer_two_sided hφ hφsupp hφ2 hp hCφ hdecay hh hA hsupp
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := (hsuper.const_mul K).eventually (gt_mem_nhds (show K * 0 < ε / 2 by
    rw [mul_zero]; linarith))
  filter_upwards [hK c hc hcN (ε / 3) (by linarith), hsmall] with N h1 h2
  rw [Real.dist_eq]
  have : K * (1 + Real.log N) / c N ^ p = K * ((1 + Real.log N) / c N ^ p) := by ring
  linarith

/-- **At the critical curve.** If `c_N^p/log N → K_c > 0`, the horizon layer is `κ_φ Q(H)` up to
`K/K_c`: eventually `|c_N⁻¹ ⟨W x, x⟩ − κ_φ Q(H)| ≤ ε + K/K_c`. -/
theorem horizon_layer_criticalCurve {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℕ → ℝ, (∀ N, 0 < c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ Kc : ℝ, 0 < Kc → Tendsto (fun N : ℕ => c N ^ p / Real.log N) atTop (𝓝 Kc) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |(c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2) -
        (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h)| ≤ ε + K / Kc := by
  obtain ⟨K, hK0, hK⟩ := horizon_layer_two_sided hφ hφsupp hφ2 hp hCφ hdecay hh hA hsupp
  refine ⟨K, hK0, fun c hc hcN Kc hKc hcrit ε hε => ?_⟩
  -- `(1 + log N)/c^p = (1/log N + 1) · (log N/c^p) → 1/K_c`
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) := hlog.inv_tendsto_atTop
  have hratio : Tendsto (fun N : ℕ => Real.log N / c N ^ p) atTop (𝓝 Kc⁻¹) := by
    have := hcrit.inv₀ hKc.ne'
    refine this.congr fun N => ?_
    simp only [inv_div]
  have hlim : Tendsto (fun N : ℕ => (1 + Real.log N) / c N ^ p) atTop (𝓝 ((0 + 1) * Kc⁻¹)) := by
    refine ((hinv.add_const 1).mul hratio).congr' ?_
    filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with N hN
    field_simp
  rw [zero_add, one_mul] at hlim
  have hev := (hlim.const_mul K).eventually (gt_mem_nhds (show K * Kc⁻¹ < K / Kc + ε / 2 by
    rw [div_eq_mul_inv]; linarith))
  filter_upwards [hK c hc hcN (ε / 2) (by linarith), hev] with N h1 h2
  have : K * (1 + Real.log N) / c N ^ p = K * ((1 + Real.log N) / c N ^ p) := by ring
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
