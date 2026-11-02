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

Twisted windows see no zero (`tendsto_twistedLedger`) and carry no negative direction: every
negative direction of the horizon layer lives on untwisted windows, where it is Weil's form of the
synthesized test.
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
    ring
  rw [e] at h
  exact (div_nonneg (by linarith) (by positivity)).trans h

/-- **Weil's form above the archimedean horizon.** For a real test supported in `[−a, a]`,
`Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a B` whenever `|f̂|² ≤ B` on `[−τ₀(a), τ₀(a)]`. -/
theorem exists_weilQuad_ge_of_lowFrequency (a : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport f ⊆ Set.Icc (-a) a →
      ∀ B : ℝ, 0 ≤ B → (∀ τ : ℝ, |τ| ≤ archHorizon a → ‖paperFT (cx f) τ‖ ^ 2 ≤ B) →
        -(2 * (‖paperFT (cx f) (Complex.I / 2)‖ * ‖paperFT (cx f) (-Complex.I / 2)‖)) - M * B ≤
          weilQuad f := by
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * a)).le
  have hτ₀ := archHorizon_nonneg a
  have hL0 : 0 ≤ Real.log (2 + archHorizon a) := Real.log_nonneg (by linarith)
  refine ⟨2 * archHorizon a * (Aν + Real.log (2 + archHorizon a)),
    mul_nonneg (by positivity) (by linarith), fun f hf hfs B hB hlow => ?_⟩
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
  have hint : Integrable (fun τ : ℝ => ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ) := by
    have hk := RHTower.integrable_paperFT_mul_mu_add_PX
      (EF.weilTest_contDiff hcx hcx.continuous hcxc) (EF.weilTest_hasCompactSupport hcxc hcxc)
      (2 * a)
    refine hk.re.congr (Eventually.of_forall fun τ => ?_)
    simp only
    rw [RHTower.paperFT_weilTest_self_ofReal hcx.continuous hcxc τ, ← Complex.ofReal_mul,
      Complex.ofReal_re, nuSymbol]
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
  have hout : 0 ≤ ∫ τ in sᶜ, ‖paperFT (cx f) τ‖ ^ 2 * nuSymbol (Real.exp (2 * a)) τ := by
    refine setIntegral_nonneg measurableSet_Icc.compl fun τ hτ => ?_
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
    (hx : ∀ n, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0) {c : ℝ} (hc : 0 < c)
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
    ∀ n, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → twistedWeights h χ N n = 0 :=
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
  have hs0 : 0 ≤ s.re := by simp [hsdef]; norm_num
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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
