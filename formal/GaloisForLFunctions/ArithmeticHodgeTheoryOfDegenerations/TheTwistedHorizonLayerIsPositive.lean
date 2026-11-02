import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsZeroBlind

/-!
# The twisted horizon layer is positive

A horizon window twisted by an `m`-periodic weight `χ` of mean zero has the weights
`x_n = χ(n) h(log(n/N))/√n`. Its Dirichlet polynomial is a twisted Riemann sum, `O(1/N)` on
every compact set of the critical strip (`norm_twistedRiemannSum_le`). The transform of the
recentred block is `e^{−iz log N} w φ̂(wz) D_x(z)`, so the twist removes the block from the low
frequencies and from the two pole values, which are exactly the places where Weil's form can be
negative:

* **Weil's form above the archimedean horizon** (`exists_weilQuad_ge_of_lowFrequency`): for a real
  test supported in `[−a, a]`, the symbol `ν` of the localized explicit formula is nonnegative
  beyond `τ₀(a)` (`nuSymbol_nonneg_of_archHorizon_le`), hence
  `Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a sup_{|τ| ≤ τ₀(a)} |f̂(τ)|²`.
* **Positivity of twisted windows** (`twisted_horizon_form_ge`): at every resolution `0 < c ≤ N`,
  `c⁻¹⟨Wx, x⟩/∫g² ≥ −C₀ (L_h + B_h)²/N²`, with `C₀` depending only on `φ`, the window length and
  the twist.
* Along every schedule the normalized form of a twisted window has nonnegative lower limit
  (`eventually_twisted_horizon_form_ge`).
* **Coercivity** (`twisted_horizon_layer_coercive`, `twisted_horizon_layer_criticalCurve_ge`): for
  the tilted spline, a nonzero window profile and a nonzero twist, one dyadic window above the grid
  carries `a log N/c⁸` (the mean-value theorem from below, with `Σ x_n² → μ_χ ∫ h²`), so at the
  multiple `K` of the critical curve the twisted window is eventually `≥ a/K − ε`.

Twisted windows see no zero (`tendsto_twistedLedger`), carry no negative direction, and have a
strictly positive second-order term of order `1/K`: every negative direction of the horizon layer
lives on untwisted windows, where it is Weil's form of the synthesized test.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-! ### Weil's form above the archimedean horizon -/

/-- The archimedean horizon of tests supported in `[−a, a]`: beyond it the symbol
`ν = μ + P_{e^{2a}}` is nonnegative. -/
def archHorizon (a : ℝ) : ℝ := 4 * Real.exp (10 + 2 * Real.exp (2 * a) ^ 2)

theorem archHorizon_nonneg (a : ℝ) : 0 ≤ archHorizon a := by unfold archHorizon; positivity

theorem nuSymbol_nonneg_of_archHorizon_le {a τ : ℝ} (hτ : archHorizon a ≤ |τ|) :
    0 ≤ nuSymbol (Real.exp (2 * a)) τ := by
  have h := nuSymbol_ge (Real.exp_pos (2 * a)).le τ
  have hlog : 10 + 2 * Real.exp (2 * a) ^ 2 ≤ Real.log (1 + |τ| / 4) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    unfold archHorizon at hτ
    linarith
  have e : (Real.log (1 + |τ| / 4) - 10) / (2 * Real.pi) - Real.exp (2 * a) ^ 2 / Real.pi =
      (Real.log (1 + |τ| / 4) - 10 - 2 * Real.exp (2 * a) ^ 2) / (2 * Real.pi) := by
    field_simp
  rw [e] at h
  exact (div_nonneg (by linarith) (by positivity)).trans h

theorem integrable_normSq_paperFT_mul_nuSymbol {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (L : ℝ) :
    Integrable (fun τ : ℝ => ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp L) τ) := by
  have hcx : ContDiff ℝ 2 (cx f) := Complex.ofRealCLM.contDiff.comp hf
  have hcxc : HasCompactSupport (cx f) := hfc.comp_left Complex.ofReal_zero
  have hk := RHTower.integrable_paperFT_mul_mu_add_PX
    (EF.weilTest_contDiff hcx hcx.continuous hcxc) (EF.weilTest_hasCompactSupport hcxc hcxc) L
  refine hk.re.congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [RHTower.paperFT_weilTest_self_ofReal hcx.continuous hcxc τ, ← Complex.ofReal_mul]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, nuSymbol]

/-- **Weil's form above the archimedean horizon.** For a real test supported in `[−a, a]`,
`Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a B + ∫_U^{2U} |f̂|² ν` whenever `|f̂|² ≤ B` on
`[−τ₀(a), τ₀(a)]` and `U ≥ τ₀(a)`. -/
theorem exists_weilQuad_ge_of_lowFrequency (a : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport f ⊆ Set.Icc (-a) a →
      ∀ B : ℝ, 0 ≤ B → (∀ τ : ℝ, |τ| ≤ archHorizon a → ‖paperFT (cx f) τ‖ ^ 2 ≤ B) →
        ∀ U : ℝ, archHorizon a ≤ U →
          -(2 * (‖paperFT (cx f) (Complex.I / 2)‖ * ‖paperFT (cx f) (-Complex.I / 2)‖)) - M * B +
              ∫ τ in U..(2 * U), ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ ≤
            weilQuad f := by
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * a)).le
  have hτ₀ := archHorizon_nonneg a
  have hL0 : 0 ≤ Real.log (2 + archHorizon a) := Real.log_nonneg (by linarith)
  refine ⟨2 * archHorizon a * (Aν + Real.log (2 + archHorizon a)),
    mul_nonneg (by positivity) (by linarith), fun f hf hfs B hB hlow U hU => ?_⟩
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc fun u hu => by
    by_contra hne
    exact hu (hfs (subset_tsupport f hne))
  have hcx : ContDiff ℝ 2 (cx f) := Complex.ofRealCLM.contDiff.comp hf
  have hcxc : HasCompactSupport (cx f) := hfc.comp_left Complex.ofReal_zero
  rw [weilQuad_eq_pole_add_symbol hf hfs]
  -- the pole terms
  have hpole : -(2 * (‖paperFT (cx f) (Complex.I / 2)‖ * ‖paperFT (cx f) (-Complex.I / 2)‖)) ≤
      (paperFT (EF.weilTest (cx f) (cx f)) (Complex.I / 2) +
        paperFT (EF.weilTest (cx f) (cx f)) (-Complex.I / 2)).re := by
    rw [EF.paperFT_weilTest hcx.continuous hcx.continuous hcxc hcxc,
      EF.paperFT_weilTest hcx.continuous hcx.continuous hcxc hcxc]
    have hc1 : conj (Complex.I / 2) = -Complex.I / 2 := by
      rw [map_div₀, Complex.conj_I, map_ofNat]
    have hc2 : conj (-Complex.I / 2) = Complex.I / 2 := by
      rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
    rw [hc1, hc2]
    have hn : ‖paperFT (cx f) (Complex.I / 2) * conj (paperFT (cx f) (-Complex.I / 2)) +
        paperFT (cx f) (-Complex.I / 2) * conj (paperFT (cx f) (Complex.I / 2))‖ ≤
        2 * (‖paperFT (cx f) (Complex.I / 2)‖ * ‖paperFT (cx f) (-Complex.I / 2)‖) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      ring
    have := (Complex.abs_re_le_norm _).trans hn
    linarith [(abs_le.mp this).1]
  -- the symbol integral
  have hint := integrable_normSq_paperFT_mul_nuSymbol hf hfc (2 * a)
  set τ₀ := archHorizon a with hτ₀def
  set s := Set.Icc (-τ₀) τ₀ with hs
  have hin : -(B * (Aν + Real.log (2 + τ₀))) * (2 * τ₀) ≤
      ∫ τ in s, ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ := by
    have hconst : ∫ τ in s, -(B * (Aν + Real.log (2 + τ₀))) =
        -(B * (Aν + Real.log (2 + τ₀))) * (2 * τ₀) := by
      rw [setIntegral_const, hs, Real.volume_real_Icc, smul_eq_mul,
        max_eq_left (by linarith)]
      ring
    rw [← hconst]
    refine setIntegral_mono_on continuous_const.integrableOn_Icc hint.integrableOn
      measurableSet_Icc fun τ hτ => ?_
    have hτ' : |τ| ≤ τ₀ := abs_le.mpr hτ
    have h1 := hlow τ hτ'
    have h2 := hν τ
    have hlog : Real.log (2 + |τ|) ≤ Real.log (2 + τ₀) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : |nuSymbol (Real.exp (2 * a)) τ| ≤ Aν + Real.log (2 + τ₀) := by linarith
    have h4 : |‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ| ≤
        B * (Aν + Real.log (2 + τ₀)) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul h1 h3 (abs_nonneg _) hB
    linarith [(abs_le.mp h4).1]
  have hτ₀pos : 0 < τ₀ := by rw [hτ₀def]; unfold archHorizon; positivity
  have hout : ∫ τ in U..(2 * U), ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ ≤
      ∫ τ in sᶜ, ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ := by
    refine window_le_off_window hint hU (by linarith) fun τ hτ => ?_
    have hτ' : τ₀ ≤ |τ| := by
      by_contra hlt
      exact hτ (abs_le.mp (not_le.mp hlt).le)
    exact mul_nonneg (by positivity) (nuSymbol_nonneg_of_archHorizon_le hτ')
  have hsplit := integral_add_compl (s := s) measurableSet_Icc hint
  linarith

/-! ### Recentred atomic tests -/

/-- An atomic test recentred at the horizon `log N`. -/
def centredAtomicTest (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  atomicTest N x (atomDilate φ (c / N)) (u + Real.log N)

theorem weilQuad_centredAtomicTest (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    weilQuad (centredAtomicTest φ x c N) = weilQuad (atomicTest N x (atomDilate φ (c / N))) := by
  have h1 := weilQuad_comp_sub (atomicTest N x (atomDilate φ (c / N))) (-Real.log N)
  simp only [sub_neg_eq_add] at h1
  exact h1

theorem paperFT_centredAtomicTest {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (z : ℂ) :
    paperFT (cx (centredAtomicTest φ x c N)) z =
      Complex.exp (-(Complex.I * z * Real.log N)) *
        (((c / N : ℝ) : ℂ) * paperFT (cx φ) (((c / N : ℝ) : ℂ) * z) * dirichletPoly N x z) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have := paperFT_comp_add (cx (atomicTest N x (atomDilate φ (c / N)))) (Real.log N) z
  rw [show (fun u => cx (atomicTest N x (atomDilate φ (c / N))) (u + Real.log N)) =
      cx (centredAtomicTest φ x c N) from rfl] at this
  rw [this, paperFT_atomicTest_atomDilate hφ hφc hw]

theorem contDiff_centredAtomicTest {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (x : ℕ → ℝ) (c : ℝ)
    (N : ℕ) : ContDiff ℝ 2 (centredAtomicTest φ x c N) := by
  unfold centredAtomicTest
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := by
    unfold atomDilate; exact hφ.comp (contDiff_id.div_const _)
  exact (contDiff_atomicTest hg N _).comp (contDiff_id.add contDiff_const)

/-- A recentred block with window-supported weights lives in `[−A, w]`. -/
theorem tsupport_centredAtomicTest_subset {φ : ℝ → ℝ} (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {x : ℕ → ℝ} {A : ℝ} {N : ℕ}
    (hx : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0) {c : ℝ} (hc : 0 < c)
    (hN : 1 ≤ N) : tsupport (centredAtomicTest φ x c N) ⊆ Set.Icc (-A) (c / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  unfold centredAtomicTest atomicTest
  refine sum_eq_zero fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  by_cases hy : Real.log n - Real.log N ∈ Set.Icc (-A) 0
  · rw [atomDilate, hφsupp _ (fun hm => hout ?_), mul_zero]
    obtain ⟨hm0, hm1⟩ := hm
    rw [le_div_iff₀ hw, zero_mul] at hm0
    rw [div_le_one hw] at hm1
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · rw [hx n hn1 hy, zero_mul]

theorem twistedWeights_eq_zero {h : ℝ → ℝ} {A : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (χ : ℕ → ℝ) (N : ℕ) :
    ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → twistedWeights h χ N n = 0 :=
  fun n _ hy => by rw [twistedWeights, horizonWeights, hsupp _ hy, zero_div, zero_mul]

/-! ### Positivity of twisted windows -/

/-- A uniform bound for the transform of the profile on a ball. -/
theorem exists_norm_paperFT_le {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (R : ℝ) : ∃ Φ : ℝ, 0 ≤ Φ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖paperFT (cx φ) z‖ ≤ Φ := by
  have hF : Continuous (paperFT (cx φ)) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)).continuous
  obtain ⟨Φ, hΦ⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max Φ 0, le_max_right _ _, fun z hz => (hΦ z ?_).trans (le_max_left _ _)⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hz

/-- The twisted Dirichlet polynomial on the critical line: `|D_x(τ)|² ≤ N (2 S K/N)²`. -/
theorem norm_sq_dirichletPoly_twisted_le {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    {Lh : NNReal} (hLh : LipschitzWith Lh h) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m)
    {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 ≤
      N * (2 * (∑ j ∈ range m, |χ j|) *
        (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A)) / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set s : ℂ := 1 / 2 + Complex.I * τ with hsdef
  have hs0 : 0 ≤ s.re := by simp [hsdef]
  have hs2 : s.re ≤ 2 := by simp [hsdef]; norm_num
  have hb := norm_twistedRiemannSum_le hh hA hsupp hB hLh hχ hs0 hs2 hN
  rw [hsdef, gammaOf_half_add] at hb
  have hs1 : ‖s - 1‖ ≤ 1 / 2 + |τ| := by
    rw [hsdef, show (1 / 2 + Complex.I * τ - 1 : ℂ) = -(1 / 2) + Complex.I * τ by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hnorm : ‖((N : ℝ) : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    congr 1
    simp [hsdef]
  rw [norm_mul, hnorm, ← hsdef] at hb
  set S := ∑ j ∈ range m, |χ j|
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : 2 * S * (((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A)) / N ≤
      2 * S * (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A)) / N := by
    gcongr
  have hb' := hb.trans hK
  have hpos : 0 < (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hsq : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  have h2 := pow_le_pow_left₀ (by positivity) hb' 2
  rw [mul_pow, hsq] at h2
  rw [← le_div_iff₀' (inv_pos.mpr hN0), div_inv_eq_mul, mul_comm] at h2
  · exact h2

/-- **Positivity of twisted windows, with a window above the archimedean horizon.** At every
resolution `0 < c ≤ N` and for every `U ≥ τ₀(A + 1)`, the normalized form of a twisted window is at
least `−C₀ (L_h + B_h)²/N² + (c w ∫φ²)⁻¹ ∫_U^{2U} |T̂|² ν`, `T` the recentred block. -/
theorem twisted_horizon_form_ge_window {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {A : ℝ} (hA : 0 ≤ A)
    {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ h : ℝ → ℝ, ContDiff ℝ 2 h → (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
      ∀ (Bh : ℝ) (Lh : NNReal), (∀ y, |h y| ≤ Bh) → LipschitzWith Lh h →
        ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N → ∀ U : ℝ, archHorizon (A + 1) ≤ U →
          -(C₀ * ((Lh : ℝ) + Bh) ^ 2) / (N : ℝ) ^ 2 + (c * (c / N * ∫ u, φ u ^ 2))⁻¹ *
              ∫ τ in U..(2 * U), ‖paperFT (cx (centredAtomicTest φ (twistedWeights h χ N) c N)) τ‖ ^ 2 *
                nuSymbol (Real.exp (2 * (A + 1))) τ ≤
            c⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N) (atomDilate φ (c / N))) /
              ∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨M, hM0, hM⟩ := exists_weilQuad_ge_of_lowFrequency (A + 1)
  have hτ₀ := archHorizon_nonneg (A + 1)
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_norm_paperFT_le hφ.continuous hφc (archHorizon (A + 1) + 1)
  have hS0 : 0 ≤ ∑ j ∈ range m, |χ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE0 := Real.exp_pos (2 * A)
  refine ⟨(2 + M) * Φ ^ 2 * (2 * (∑ j ∈ range m, |χ j|) *
      ((1 + archHorizon (A + 1)) * Real.exp (2 * A))) ^ 2 / ∫ u, φ u ^ 2, by positivity, ?_⟩
  intro h hh hsupp Bh Lh hB hLh N hN c hc hcN U hU
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  set τ₀ := archHorizon (A + 1) with hτ₀def
  set S := ∑ j ∈ range m, |χ j| with hSdef
  set E := Real.exp (2 * A) with hEdef
  set x := twistedWeights h χ N with hxdef
  set Kb := ((Lh : ℝ) + (1 + τ₀) * Bh) * E with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  -- the twisted Riemann sums at the points we need
  have hD : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 + τ₀ →
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)‖ ≤ 2 * S * Kb / N := by
    intro s h0 h2 h1
    refine (norm_twistedRiemannSum_le hh hA hsupp hB hLh hχ h0 h2 hN).trans ?_
    rw [hKb]
    gcongr
  set B := (c / N) ^ 2 * Φ ^ 2 * (N * (2 * S * Kb / N) ^ 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  -- low frequencies
  have hlow : ∀ τ : ℝ, |τ| ≤ τ₀ →
      ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 ≤ B := by
    intro τ hτ
    rw [paperFT_centredAtomicTest hφ.continuous hφc x hc hN, norm_mul, norm_mul, norm_mul]
    have he : ‖Complex.exp (-(Complex.I * (τ : ℂ) * (Real.log N : ℂ)))‖ = 1 := by
      rw [show -(Complex.I * (τ : ℂ) * (Real.log N : ℂ)) = ((-(τ * Real.log N) : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hφτ : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ≤ Φ := by
      refine hΦ _ ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hw]
      nlinarith [abs_nonneg τ]
    have hDτ := norm_sq_dirichletPoly_twisted_le hh hA hsupp hB hLh hχ hN τ
    have hKτ : 2 * S * (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * E) / N ≤ 2 * S * Kb / N := by
      rw [hKb]; gcongr; linarith
    have hDτ' : ‖dirichletPoly N x τ‖ ^ 2 ≤ N * (2 * S * Kb / N) ^ 2 :=
      hDτ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hKτ 2) hN0.le)
    rw [he, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, mul_pow, mul_pow, hBdef]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hφτ 2)
      (by positivity)) hDτ' (by positivity) (by positivity)
  -- the pole values
  have hpole : ‖paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2)‖ *
      ‖paperFT (cx (centredAtomicTest φ x c N)) (-Complex.I / 2)‖ ≤ B := by
    rw [paperFT_centredAtomicTest hφ.continuous hφc x hc hN,
      paperFT_centredAtomicTest hφ.continuous hφc x hc hN]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    have he : ‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
        ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖ = 1 := by
      have e1 : -(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)) = ((Real.log N / 2 : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      have e2 : -(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)) =
          ((-(Real.log N / 2) : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [e1, e2, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero]
    have hφ1 : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ ≤ Φ := by
      refine hΦ _ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, Complex.norm_I]
      norm_num
      nlinarith
    have hφ2' : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖ ≤ Φ := by
      refine hΦ _ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, norm_neg,
        Complex.norm_I]
      norm_num
      nlinarith
    have hD0 : ‖dirichletPoly N x (Complex.I / 2)‖ ≤ 2 * S * Kb / N := by
      have := hD 0 (by simp) (by simp) (by simp; linarith)
      rwa [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at this
    have hD1 : ‖dirichletPoly N x (-Complex.I / 2)‖ ≤ N * (2 * S * Kb / N) := by
      have := hD 1 (by simp) (by simp) (by simp; linarith)
      rw [Complex.cpow_neg_one, gammaOf_one, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hN0, inv_mul_le_iff₀ hN0] at this
      exact this
    calc ‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
          (c / N * ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
            ‖dirichletPoly N x (Complex.I / 2)‖) *
        (‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖ *
          (c / N * ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖ *
            ‖dirichletPoly N x (-Complex.I / 2)‖))
        = (‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
            ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖) *
          ((c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
            ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
          (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖)) := by ring
      _ ≤ 1 * ((c / N) ^ 2 * (Φ * Φ) * ((2 * S * Kb / N) * (N * (2 * S * Kb / N)))) := by
          rw [he]
          gcongr
      _ = B := by rw [hBdef]; ring
  -- Weil's form of the recentred block
  have hts : tsupport (centredAtomicTest φ x c N) ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    (tsupport_centredAtomicTest_subset hφsupp (twistedWeights_eq_zero hsupp χ N) hc hN).trans
      (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hQ := hM _ (contDiff_centredAtomicTest hφ x c N) hts B hB0 hlow U hU
  rw [weilQuad_centredAtomicTest] at hQ
  set I := ∫ τ in U..(2 * U), ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 *
    nuSymbol (Real.exp (2 * (A + 1))) τ with hIdef
  have hQ' : -((2 + M) * B) + I ≤ weilQuad (atomicTest N x (atomDilate φ (c / N))) := by
    nlinarith
  -- normalization
  rw [integral_atomDilate_sq φ hw]
  have hKbl : Kb ≤ (1 + τ₀) * E * ((Lh : ℝ) + Bh) := by
    rw [hKb]
    have hL0 : (0 : ℝ) ≤ Lh := Lh.2
    nlinarith [mul_nonneg (mul_nonneg hτ₀ hE0.le) hL0]
  have hI := hφ2
  have key : (2 + M) * B / (c * (c / N * ∫ u, φ u ^ 2)) =
      (2 + M) * Φ ^ 2 * (2 * S * Kb) ^ 2 / (∫ u, φ u ^ 2) / (N : ℝ) ^ 2 := by
    rw [hBdef]; field_simp
  have hfin : (2 + M) * Φ ^ 2 * (2 * S * Kb) ^ 2 / (∫ u, φ u ^ 2) / (N : ℝ) ^ 2 ≤
      (2 + M) * Φ ^ 2 * (2 * S * ((1 + τ₀) * E)) ^ 2 / (∫ u, φ u ^ 2) *
        ((Lh : ℝ) + Bh) ^ 2 / (N : ℝ) ^ 2 := by
    have h1 : 2 * S * Kb ≤ 2 * S * ((1 + τ₀) * E * ((Lh : ℝ) + Bh)) :=
      mul_le_mul_of_nonneg_left hKbl (by positivity)
    have hnum : (2 + M) * Φ ^ 2 * (2 * S * Kb) ^ 2 ≤
        (2 + M) * Φ ^ 2 * (2 * S * ((1 + τ₀) * E)) ^ 2 * ((Lh : ℝ) + Bh) ^ 2 := by
      calc (2 + M) * Φ ^ 2 * (2 * S * Kb) ^ 2
          ≤ (2 + M) * Φ ^ 2 * (2 * S * ((1 + τ₀) * E * ((Lh : ℝ) + Bh))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 2) (by positivity)
        _ = _ := by ring
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hnum hI.le
  have hpos : 0 < c * (c / N * ∫ u, φ u ^ 2) := by positivity
  have hlow' : -((2 + M) * B / (c * (c / N * ∫ u, φ u ^ 2))) +
      (c * (c / N * ∫ u, φ u ^ 2))⁻¹ * I ≤
      c⁻¹ * (weilQuad (atomicTest N x (atomDilate φ (c / N))) / (c / N * ∫ u, φ u ^ 2)) := by
    have hR : c⁻¹ * (weilQuad (atomicTest N x (atomDilate φ (c / N))) / (c / N * ∫ u, φ u ^ 2)) =
        weilQuad (atomicTest N x (atomDilate φ (c / N))) / (c * (c / N * ∫ u, φ u ^ 2)) := by
      rw [inv_mul_eq_div, div_div, mul_comm (c / N * ∫ u, φ u ^ 2) c]
    rw [hR]
    have := div_le_div_of_nonneg_right hQ' hpos.le
    calc -((2 + M) * B / (c * (c / N * ∫ u, φ u ^ 2))) + (c * (c / N * ∫ u, φ u ^ 2))⁻¹ * I
        = (-((2 + M) * B) + I) / (c * (c / N * ∫ u, φ u ^ 2)) := by ring
      _ ≤ _ := this
  rw [neg_div]
  linarith

/-- **Positivity of twisted windows.** At every resolution `0 < c ≤ N` the normalized form of a
twisted window is at least `−C₀ (L_h + B_h)²/N²`; `C₀` depends only on `φ`, `A` and `χ`. -/
theorem twisted_horizon_form_ge {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {A : ℝ} (hA : 0 ≤ A)
    {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ h : ℝ → ℝ, ContDiff ℝ 2 h → (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
      ∀ (Bh : ℝ) (Lh : NNReal), (∀ y, |h y| ≤ Bh) → LipschitzWith Lh h →
        ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
          -(C₀ * ((Lh : ℝ) + Bh) ^ 2) / (N : ℝ) ^ 2 ≤
            c⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N) (atomDilate φ (c / N))) /
              ∫ u, atomDilate φ (c / N) u ^ 2) := by
  obtain ⟨C₀, hC₀, hb⟩ := twisted_horizon_form_ge_window hφ hφsupp hφ2 hA hχ
  refine ⟨C₀, hC₀, fun h hh hsupp Bh Lh hB hLh N hN c hc hcN => ?_⟩
  have h1 := hb h hh hsupp Bh Lh hB hLh N hN c hc hcN _ le_rfl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ₀ := archHorizon_nonneg (A + 1)
  have hwin : 0 ≤ ∫ τ in archHorizon (A + 1)..(2 * archHorizon (A + 1)),
      ‖paperFT (cx (centredAtomicTest φ (twistedWeights h χ N) c N)) τ‖ ^ 2 *
        nuSymbol (Real.exp (2 * (A + 1))) τ :=
    intervalIntegral.integral_nonneg (by linarith) fun τ hτ => mul_nonneg (by positivity)
      (nuSymbol_nonneg_of_archHorizon_le (by rw [abs_of_nonneg (by linarith [hτ.1])]; exact hτ.1))
  have h2 := mul_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ c * (c / N * ∫ u, φ u ^ 2)))
    hwin
  linarith

/-- Along every schedule `0 < c_N ≤ N` the normalized form of a twisted window has nonnegative
lower limit. -/
theorem eventually_twisted_horizon_form_ge {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {A : ℝ} (hA : 0 ≤ A)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : ∀ N : ℕ, c N ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, -ε ≤ (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
      (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) := by
  obtain ⟨C₀, hC₀, hbound⟩ := twisted_horizon_form_ge hφ hφsupp hφ2 hA hχ
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hlim : Tendsto (fun N : ℕ => C₀ * ((Lh : ℝ) + Bh) ^ 2 / (N : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hN1
  have := hbound h hh hsupp Bh Lh hB hLh N hN1 (c N) (hc N) (hcN N)
  rw [neg_div] at this
  linarith

/-! ### Coercivity at the critical curve -/

theorem MeanZeroTwist.apply_add_mul {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) (r q : ℕ) :
    χ (r + q * m) = χ r := by
  induction q with
  | zero => simp
  | succ q ih => rw [show r + (q + 1) * m = r + q * m + m by ring, hχ.periodic, ih]

/-- A periodic twist is bounded by `Σ_{j<m} |χ(j)|`. -/
theorem MeanZeroTwist.abs_le_sum {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) (n : ℕ) :
    |χ n| ≤ ∑ j ∈ range m, |χ j| := by
  have e := hχ.apply_add_mul (n % m) (n / m)
  rw [Nat.mod_add_div'] at e
  rw [e]
  exact Finset.single_le_sum (f := fun j => |χ j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.mod_lt _ hχ.pos))

/-- The centred square of a periodic twist is a mean-zero twist. -/
theorem MeanZeroTwist.sq_sub {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    MeanZeroTwist (fun n => χ n ^ 2 - (∑ r ∈ range m, χ r ^ 2) / m) m where
  pos := hχ.pos
  periodic n := by simp only [hχ.periodic]
  mean_zero := by
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast hχ.pos.ne'
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ hm, sub_self]

theorem horizonProfile_zero (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    horizonProfile g 0 x = ((g (Real.log x) / x : ℝ) : ℂ) := by
  rw [horizonProfile, if_pos hx, zero_sub, Complex.cpow_neg_one]
  push_cast
  ring

/-- **The mass of a twisted block**: `Σ x_n² → μ_χ ∫ h²`, `μ_χ = m⁻¹ Σ_{r<m} χ(r)²`. -/
theorem tendsto_sum_twistedWeights_sq {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, twistedWeights h χ N n ^ 2) atTop
      (𝓝 ((∑ r ∈ range m, χ r ^ 2) / m * ∫ y, h y ^ 2)) := by
  have hψ := hχ.sq_sub
  have hgd : ContDiff ℝ 2 (fun y => h y ^ 2) := hh.pow 2
  have hgs : ∀ y, y ∉ Set.Icc (-A) 0 → (fun y => h y ^ 2) y = 0 := fun y hy => by
    simp [hsupp y hy]
  have hc := tendsto_twistedRiemannSum hgd hA hgs hψ (s := 0) le_rfl (by norm_num)
  have hre := (Complex.continuous_re.tendsto 0).comp hc
  rw [Complex.zero_re] at hre
  have hmain := (tendsto_sum_horizonWeights_sq hh.continuous hsupp hA).const_mul
    ((∑ r ∈ range m, χ r ^ 2) / m)
  have hsum := hmain.add hre
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [twistedRiemannSum_eq _ _ 0 hN]
  have hterm : ∀ r ∈ Icc 1 N, horizonProfile (fun y => h y ^ 2) 0 (r / N) *
      ((χ r ^ 2 - (∑ r ∈ range m, χ r ^ 2) / m : ℝ) : ℂ) =
      (((N : ℝ) * (horizonWeights h N r ^ 2 *
        (χ r ^ 2 - (∑ r ∈ range m, χ r ^ 2) / m)) : ℝ) : ℂ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    rw [horizonProfile_zero _ (div_pos hr0 hN0), ← Complex.ofReal_mul]
    congr 1
    rw [horizonWeights, Real.log_div hr0.ne' hN0.ne', div_pow, Real.sq_sqrt hr0.le]
    field_simp
  rw [sum_congr rfl hterm, ← Complex.ofReal_sum, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← Finset.mul_sum, inv_mul_cancel_left₀ hN0.ne', mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [twistedWeights, mul_pow]
  ring

theorem sum_mul_twistedWeights_sq_le {h : ℝ → ℝ} {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {χ : ℕ → ℝ}
    {m : ℕ} (hχ : MeanZeroTwist χ m) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) * twistedWeights h χ N n ^ 2 ≤
      N * (Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2) := by
  have h1 := sum_mul_horizonWeights_sq_le hB N
  have hχ2 : ∀ n, χ n ^ 2 ≤ (∑ j ∈ range m, |χ j|) ^ 2 := fun n => by
    have := hχ.abs_le_sum n
    nlinarith [abs_nonneg (χ n), sq_abs (χ n)]
  calc ∑ n ∈ Icc 1 N, (n : ℝ) * twistedWeights h χ N n ^ 2
      = ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 * χ n ^ 2 := by
        refine sum_congr rfl fun n _ => ?_
        rw [twistedWeights, mul_pow]; ring
    _ ≤ ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2 :=
        sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hχ2 n) (by positivity)
    _ = (∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2) * (∑ j ∈ range m, |χ j|) ^ 2 := by
        rw [sum_mul]
    _ ≤ N * Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = N * (Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2) := by ring

/-- The mean-value theorem from below on a window `[U, 2U]`, `U = 2^j N e^{−A}`, for a twisted block. -/
theorem meanSquare_window_twisted_ge {h : ℝ → ℝ} {A Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {χ : ℕ → ℝ}
    {m : ℕ} (hχ : MeanZeroTwist χ m) {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 < s)
    (hS1 : s / 2 < ∑ n ∈ Icc 1 N, twistedWeights h χ N n ^ 2) {j : ℕ}
    (hj : 832 * (Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2) * Real.exp A / s < 2 ^ j) :
    2 ^ j * Real.exp (-A) * s / 4 ≤
      (∫ τ in (2 ^ j * (N * Real.exp (-A)))..(2 * (2 ^ j * (N * Real.exp (-A)))),
        ‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hMV := integral_window_ge N (twistedWeights h χ N) (2 ^ j * (N * Real.exp (-A)))
  have hS2 := sum_mul_twistedWeights_sq_le hB hχ N
  rw [le_div_iff₀ hN0]
  have hj' : 208 * (Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2) < 2 ^ j * Real.exp (-A) * s / 4 := by
    rw [div_lt_iff₀ hs] at hj
    have he : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
    have h1 := mul_lt_mul_of_pos_right hj (Real.exp_pos (-A))
    rw [mul_assoc _ (Real.exp A), he, mul_one] at h1
    linarith
  have hU0 : 0 < 2 ^ j * ((N : ℝ) * Real.exp (-A)) := by positivity
  have hUS := mul_le_mul_of_nonneg_left hS1.le hU0.le
  have hk := mul_le_mul_of_nonneg_left hj'.le hN0.le
  nlinarith [hk, hS2, hMV, hUS]

theorem norm_sq_paperFT_centredAtomicTest {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 =
      (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * ‖dirichletPoly N x τ‖ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [paperFT_centredAtomicTest hφ hφc x hc hN, norm_mul, norm_mul, norm_mul]
  have he : ‖Complex.exp (-(Complex.I * (τ : ℂ) * (Real.log N : ℂ)))‖ = 1 := by
    rw [show -(Complex.I * (τ : ℂ) * (Real.log N : ℂ)) = ((-(τ * Real.log N) : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [he, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hc hN0)]
  ring

/-- On a window `[U, 2U]` above the archimedean horizon the recentred tilted-spline block has
`|T̂|² ν ≥ w² w_min ν_min |D_x|²`. -/
theorem integral_window_centred_ge {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ)
    (hfc : HasCompactSupport (centredAtomicTest tiltedUnitSpline x c N)) (L : ℝ) {U : ℝ}
    (hU : 0 < U)
    (hνm0 : 0 ≤ (Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi) :
    (c / N) ^ 2 * (Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * U) ^ 8)⁻¹) *
        ((Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi) *
          ∫ τ in U..(2 * U), ‖dirichletPoly N x τ‖ ^ 2 ≤
      ∫ τ in U..(2 * U), ‖paperFT (cx (centredAtomicTest tiltedUnitSpline x c N)) τ‖ ^ 2 *
        nuSymbol (Real.exp L) τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by linarith)
    (((continuous_norm_sq_dirichletPoly N x).const_mul _).intervalIntegrable _ _)
    ((integrable_normSq_paperFT_mul_nuSymbol
      (contDiff_centredAtomicTest contDiff_tiltedUnitSpline x c N) hfc L).intervalIntegrable)
    fun τ hτ => ?_
  have hτ0 : 0 < τ := lt_of_lt_of_le hU hτ.1
  have hl := tiltedUnitSpline_lower (c / N * τ)
  have hwt : Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * U) ^ 8)⁻¹ ≤
      ‖paperFT (cx tiltedUnitSpline) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 := by
    refine le_trans ?_ (by push_cast at hl ⊢; exact hl)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 8)
    rw [abs_of_pos (mul_pos hw hτ0)]
    nlinarith [hτ.2]
  have hν : (Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi ≤
      nuSymbol (Real.exp L) τ := by
    refine le_trans ?_ (nuSymbol_ge (Real.exp_pos L).le τ)
    rw [abs_of_pos hτ0]
    gcongr
    exact hτ.1
  rw [norm_sq_paperFT_centredAtomicTest contDiff_tiltedUnitSpline.continuous
    hasCompactSupport_tiltedUnitSpline x hc hN]
  have hD : 0 ≤ ‖dirichletPoly N x τ‖ ^ 2 := by positivity
  calc (c / N) ^ 2 * (Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * U) ^ 8)⁻¹) *
        ((Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi) *
          ‖dirichletPoly N x τ‖ ^ 2
      = (c / N) ^ 2 * (Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c / N) * U) ^ 8)⁻¹ *
          ‖dirichletPoly N x τ‖ ^ 2) *
          ((Real.log (1 + U / 4) - 10) / (2 * Real.pi) - Real.exp L ^ 2 / Real.pi) := by ring
    _ ≤ (c / N) ^ 2 * (‖paperFT (cx tiltedUnitSpline) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          ‖dirichletPoly N x τ‖ ^ 2) * nuSymbol (Real.exp L) τ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwt hD)
          (by positivity)) hν hνm0 (by positivity)

/-- **Twisted windows are coercive.** For a nonzero window profile and a nonzero mean-zero
periodic twist there is `a > 0` such that along every schedule `1 ≤ c_N ≤ N`, eventually
`c_N⁻¹⟨W x, x⟩/∫g² ≥ −ε + a log N/c_N⁸` (tilted spline). -/
theorem twisted_horizon_layer_coercive {A : ℝ} (hA : 0 ≤ A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hpos : 0 < ∫ y, h y ^ 2) {χ : ℕ → ℝ} {m : ℕ}
    (hχ : MeanZeroTwist χ m) (hχ0 : 0 < ∑ r ∈ range m, χ r ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) → (∀ᶠ N : ℕ in atTop, c N ≤ N) → ∀ ε > 0,
      ∀ᶠ N : ℕ in atTop, -ε + a * Real.log N / c N ^ (8 : ℝ) ≤
        (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
          (atomDilate tiltedUnitSpline (c N / N))) /
            ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  have hM0 : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hχ.pos
  obtain ⟨s, hsdef⟩ : ∃ s, s = (∑ r ∈ range m, χ r ^ 2) / m * ∫ y, h y ^ 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact mul_pos (div_pos hχ0 hm0) hpos
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 832 * (Bh ^ 2 * (∑ j ∈ range m, |χ j|) ^ 2) * Real.exp A / s < 2 ^ j :=
    pow_unbounded_of_one_lt _ one_lt_two
  have hsh : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ *
      (1 / (4 * Real.pi)) * (2 ^ j * Real.exp (-A) * s / 4) := ⟨_, rfl⟩
  have ha₀0 : 0 < a₀ := by
    have : 0 < Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ :=
      mul_pos (div_pos (pow_pos hsh 8) (by norm_num)) (inv_pos.mpr (by positivity))
    rw [ha₀]; positivity
  obtain ⟨C₀, hC₀, hbound⟩ := twisted_horizon_form_ge_window contDiff_tiltedUnitSpline
    tiltedUnitSpline_support hM0 hA hχ
  refine ⟨a₀ / ∫ u, tiltedUnitSpline u ^ 2, div_pos ha₀0 hM0, fun c hc1 hcle ε hε => ?_⟩
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hlim : Tendsto (fun N : ℕ => C₀ * ((Lh : ℝ) + Bh) ^ 2 / (N : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hev1 := hlim.eventually (gt_mem_nhds hε)
  have hev3 := (tendsto_sum_twistedWeights_sq hh hA hsupp hχ).eventually
    (lt_mem_nhds (show s / 2 < (∑ r ∈ range m, χ r ^ 2) / m * ∫ y, h y ^ 2 by
      rw [← hsdef]; linarith))
  have hev4 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 * (A + 12 + 2 * Real.exp (2 * (A + 1)) ^ 2)))
  have hev5 := (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos (-A))).eventually
    (eventually_ge_atTop (archHorizon (A + 1)))
  filter_upwards [hev1, hev3, hev4, hev5, hcle, eventually_ge_atTop 1] with N h1 h3 h4 h5 h6 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hτpos : 0 < archHorizon (A + 1) := by unfold archHorizon; positivity
  have hTU : archHorizon (A + 1) ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) := by
    have : (N : ℝ) * Real.exp (-A) ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) :=
      le_mul_of_one_le_left (by positivity) h2j
    exact h5.trans this
  have hU0 : 0 < 2 ^ j * ((N : ℝ) * Real.exp (-A)) := lt_of_lt_of_le hτpos hTU
  have hwb := hbound h hh hsupp Bh Lh hB hLh N hN (c N) (hc0 N) h6 _ hTU
  have hfc : HasCompactSupport (centredAtomicTest tiltedUnitSpline (twistedWeights h χ N) (c N) N) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (tsupport_centredAtomicTest_subset tiltedUnitSpline_support (twistedWeights_eq_zero hsupp χ N)
        (hc0 N) hN)
  have hνm := nuMin_ge (X := Real.exp (2 * (A + 1))) hN j h4
  have hνm0 : 0 ≤ (Real.log (1 + 2 ^ j * ((N : ℝ) * Real.exp (-A)) / 4) - 10) / (2 * Real.pi) -
      Real.exp (2 * (A + 1)) ^ 2 / Real.pi :=
    le_trans (by have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity) hνm
  have hW := integral_window_centred_ge (hc0 N) hN (twistedWeights h χ N) hfc (2 * (A + 1)) hU0
    hνm0
  have hD := meanSquare_window_twisted_ge (A := A) hB hχ hN hs0 (by rw [hsdef] at h3 ⊢; exact h3) hj
  have hWt := windowWeight_ge (hc1 N) hN A j
  have hcp : 0 < c N ^ (8 : ℝ) := Real.rpow_pos_of_pos (hc0 N) _
  set D2 := ∫ τ in (2 ^ j * ((N : ℝ) * Real.exp (-A)))..(2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))),
    ‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 with hD2
  set I := ∫ τ in (2 ^ j * ((N : ℝ) * Real.exp (-A)))..(2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))),
    ‖paperFT (cx (centredAtomicTest tiltedUnitSpline (twistedWeights h χ N) (c N) N)) τ‖ ^ 2 *
      nuSymbol (Real.exp (2 * (A + 1))) τ with hI
  set Wm := Real.sinh 1 ^ 8 / 64 * ((1 + 2 * (c N / N) * (2 ^ j * ((N : ℝ) * Real.exp (-A)))) ^ 8)⁻¹
    with hWm
  set νm := (Real.log (1 + 2 ^ j * ((N : ℝ) * Real.exp (-A)) / 4) - 10) / (2 * Real.pi) -
      Real.exp (2 * (A + 1)) ^ 2 / Real.pi with hνmdef
  set M := ∫ u, tiltedUnitSpline u ^ 2 with hM
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hcN0 : c N ≠ 0 := (hc0 N).ne'
  have hWm0 : 0 ≤ Wm := by rw [hWm]; positivity
  have hD20 : 0 ≤ D2 := intervalIntegral.integral_nonneg (by linarith) fun τ _ => by positivity
  have hq0 : 0 ≤ 2 ^ j * Real.exp (-A) * s / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hs0.le) (by norm_num)
  have hchain : a₀ / M * Real.log N / c N ^ (8 : ℝ) ≤ (c N * (c N / N * M))⁻¹ * I := by
    have e : (c N * (c N / N * M))⁻¹ * ((c N / N) ^ 2 * Wm * νm * D2) = Wm * νm * (D2 / N) / M := by
      field_simp
    calc a₀ / M * Real.log N / c N ^ (8 : ℝ)
        = (Real.sinh 1 ^ 8 / 64 * ((1 + 2 ^ (j + 1) * Real.exp (-A)) ^ 8)⁻¹ *
            (c N ^ (8 : ℝ))⁻¹) * (Real.log N / (4 * Real.pi)) *
              (2 ^ j * Real.exp (-A) * s / 4) / M := by
          rw [ha₀]; field_simp
      _ ≤ Wm * νm * (D2 / N) / M := by
          refine div_le_div_of_nonneg_right ?_ hM0.le
          exact mul_le_mul (mul_le_mul hWt hνm (div_nonneg hlogN (by positivity)) hWm0) hD
            hq0 (mul_nonneg hWm0 hνm0)
      _ = (c N * (c N / N * M))⁻¹ * ((c N / N) ^ 2 * Wm * νm * D2) := e.symm
      _ ≤ (c N * (c N / N * M))⁻¹ * I :=
          mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr (mul_nonneg (hc0 N).le
            (mul_nonneg (div_nonneg (hc0 N).le hN0.le) hM0.le)))
  rw [neg_div] at hwb
  have : a₀ / M * Real.log N / c N ^ (8 : ℝ) = a₀ / M * Real.log N / c N ^ (8 : ℝ) := rfl
  linarith

/-- **The second-order term of a twisted window is positive.** Along `c⁸/log N → K`, eventually
`c⁻¹⟨W x, x⟩/∫g² ≥ a/K − ε`; in particular the twisted block is eventually positive at every
multiple of the critical curve. -/
theorem twisted_horizon_layer_criticalCurve_ge {A : ℝ} (hA : 0 ≤ A) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hpos : 0 < ∫ y, h y ^ 2)
    {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) (hχ0 : 0 < ∑ r ∈ range m, χ r ^ 2) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) → (∀ᶠ N : ℕ in atTop, c N ≤ N) →
      ∀ K : ℝ, 0 < K → Tendsto (fun N : ℕ => c N ^ (8 : ℝ) / Real.log N) atTop (𝓝 K) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, a / K - ε ≤
        (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
          (atomDilate tiltedUnitSpline (c N / N))) /
            ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  obtain ⟨a, ha, hco⟩ := twisted_horizon_layer_coercive hA hh hsupp hpos hχ hχ0
  refine ⟨a, ha, fun c hc1 hcle K hK hcrit ε hε => ?_⟩
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (8 : ℝ)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by simp only [inv_div]
  have hev := (hinv.const_mul a).eventually (lt_mem_nhds (show a * K⁻¹ - ε / 2 < a * K⁻¹ by
    linarith))
  filter_upwards [hco c hc1 hcle (ε / 2) (half_pos hε), hev] with N h1 h2
  have : a * Real.log N / c N ^ (8 : ℝ) = a * (Real.log N / c N ^ (8 : ℝ)) := by ring
  rw [div_eq_mul_inv a K]
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
