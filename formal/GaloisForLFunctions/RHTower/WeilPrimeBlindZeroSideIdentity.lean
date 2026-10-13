import GaloisForLFunctions.RHTower.WeilConeNullEnergyBlindTestCarrier

/-!
# The explicit formula on prime-blind tests, and PBAP as positivity of the zero side

Let `F` be a real test with `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}` (`ExpDecayTest`) whose autocorrelation
vanishes at every `log n`, `n ≥ 2`.

**Theorem** (`archPoleEnergy_eq_re_W_of_blind`).  The pole and archimedean energy of `F` equals
the zero side of the explicit formula:
`archPoleEnergy F = Re Σ_ρ m_ρ F̂(γ_ρ) · conj F̂(conj γ_ρ)`,
the sum running over all nontrivial zeros of `ζ`, on and off the critical line.  The prime side
is absent because `F` is prime-blind; no compact support is needed.

**Corollary** (`re_W_nonneg_of_primeBlindPositive`).  Prime-blind positivity (a nonempty Weil
cone) forces the zero side to be nonnegative on every prime-blind test of the decay class.  A
zero on the critical line contributes `m_ρ |F̂(γ_ρ)|² ≥ 0`.  So under PBAP the off-line zeros can
never outweigh the critical zeros on a prime-blind test: PBAP reads as a positivity property of the
zero configuration of `ζ` restricted to the prime-blind tests.

**Proof.**  For the truncations `F_L` the corpus explicit formula gives
`archPoleEnergy F_L = Re W_ζ(F_L, F_L) + T_Λ(F_L ⋆ F̃_L)`.  The energy is continuous under
truncation, and the prime pairing tends to `0` by summation by parts against Chebyshev's bound and
blindness.  On the zero side, `(1 + |Re z|)|F̂_L(z)| ≤ M` on the critical strip uniformly in `L`.
Since `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`, dominated convergence gives `W_ζ(F_L, F_L) → W_ζ(F, F)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- Uniform decay of the transforms of the truncations on the critical strip. -/
theorem one_add_abs_re_mul_norm_paperFT_truncTest_le {F : ℝ → ℝ} (hF : ExpDecayTest F)
    {Λ : ℝ} (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (hΛ0 : 0 ≤ Λ) (L : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) z‖ ≤ ∫ u, tailMajorant F Λ u := by
  set L₀ : ℝ := min L 0 with hL₀
  have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_le hF.1 hΛ
    (integrable_tailMajorant hF hΛ0) (min_le_left L 0) hz
  have h0 : (fun u => (truncTest F L₀ u : ℂ)) = fun _ => 0 := by
    funext u
    rw [truncTest_eq_zero (le_trans (min_le_right L 0) (abs_nonneg u))]
    simp
  have hft0 : paperFT (fun u => (truncTest F L₀ u : ℂ)) z = 0 := by
    rw [h0]; unfold paperFT; simp
  have htail : tailBound F Λ L₀ = ∫ u, tailMajorant F Λ u := by
    unfold tailBound
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hu : u ∈ {u : ℝ | L₀ - 1 ≤ |u|} := by
      show L₀ - 1 ≤ |u|
      linarith [min_le_right L 0, abs_nonneg u]
    exact Set.indicator_of_mem hu _
  rw [hft0, zero_sub, norm_neg, htail] at h
  exact h

/-- A summand of the zero side is bounded by the size of the transform at the zero. -/
private theorem norm_Wsummand_le {f : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (ρ : zetaZeroConfig.carrier)
    (h1 : (1 + |(ρ : ℂ).im|) * ‖paperFT f (gammaOf ρ)‖ ≤ M)
    (h2 : (1 + |(ρ : ℂ).im|) * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ M) :
    ‖zetaZeroConfig.Wsummand f f ρ‖ ≤
      (5 / 4) * M ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨hmem.2.1, hmem.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt hstrip
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  set y := (ρ : ℂ).im with hy
  have hp : 0 < 1 + |y| := by positivity
  have hn1 : ‖paperFT f (gammaOf ρ)‖ ≤ M / (1 + |y|) := by
    rw [le_div_iff₀ hp, mul_comm]; exact h1
  have hn2 : ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ M / (1 + |y|) := by
    rw [le_div_iff₀ hp, mul_comm]; exact h2
  have hnormSq : Complex.normSq (gammaOf (ρ : ℂ)) ≤ y ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, hre]
    have : (gammaOf (ρ : ℂ)).im ^ 2 ≤ 1 / 4 := by
      have := sq_abs (gammaOf (ρ : ℂ)).im
      nlinarith [abs_nonneg (gammaOf (ρ : ℂ)).im]
    nlinarith
  have hden : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤ (5 / 4) * (1 + |y|) ^ 2 := by
    nlinarith [sq_abs y, abs_nonneg y]
  have hpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  unfold ZeroConfig.Wsummand
  rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
        ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (M / (1 + |y|)) * (M / (1 + |y|)) := by gcongr
    _ = (zetaZeroConfig.mult ρ : ℝ) * M ^ 2 / (1 + |y|) ^ 2 := by field_simp
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * M ^ 2 / ((4 / 5) * (1 + Complex.normSq (gammaOf ρ))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
    _ = _ := by field_simp

/-- **The zero side is continuous under truncation.** -/
theorem tendsto_W_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    Tendsto (fun L : ℝ =>
      zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))) atTop
      (𝓝 (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set M : ℝ := ∫ u, tailMajorant F Λ u with hM
  have hM0 : 0 ≤ M := integral_nonneg fun u => tailMajorant_nonneg F hΛ0 u
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  unfold ZeroConfig.W
  refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (hsum.mul_left ((5 / 4) * M ^ 2))
    (fun ρ => ?_) (Eventually.of_forall fun L ρ => ?_)
  · -- pointwise convergence at each zero
    have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
      (WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩).le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    unfold ZeroConfig.Wsummand
    exact ((tendsto_paperFT_truncTest hF hIm).const_mul _).mul
      ((Complex.continuous_conj.tendsto _).comp (tendsto_paperFT_truncTest hF hIm'))
  · -- the uniform bound
    have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
      (WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩).le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
    have h1 := one_add_abs_re_mul_norm_paperFT_truncTest_le hF hΛ hΛ0 L hIm
    have h2 := one_add_abs_re_mul_norm_paperFT_truncTest_le hF hΛ hΛ0 L hIm'
    rw [hre] at h1
    rw [Complex.conj_re, hre] at h2
    have := norm_Wsummand_le hM0 ρ h1 h2
    simpa [mul_assoc] using this

/-- **The explicit formula on the decay class.**  For every real test of the decay class, the pole
and archimedean energy equals the real part of the zero side plus the Abel prime pairing with
`Λ`. -/
theorem archPoleEnergy_eq_re_W_add_abelPrimePairing {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    archPoleEnergy F = (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re +
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F := by
  have hW := (Complex.continuous_re.tendsto _).comp (tendsto_W_truncTest hF)
  have hprime := tendsto_atomPairing_truncTest_abelPrimePairing hF (A := 7)
    (w := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (fun N => abs_primeWeightPartialSum_vonMangoldt_le N)
  exact tendsto_nhds_unique (tendsto_archPoleEnergy_truncTest hF)
    ((hW.add hprime).congr fun L => (archPoleEnergy_truncTest_eq hF.1 L).symm)

/-- **The explicit formula on prime-blind tests.**  For a prime-blind test of the decay class, the
pole and archimedean energy equals the real part of the zero side. -/
theorem archPoleEnergy_eq_re_W_of_blind {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) :
    archPoleEnergy F = (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  rw [archPoleEnergy_eq_re_W_add_abelPrimePairing hF, abelPrimePairing_eq_zero_of_blind _ hblind,
    add_zero]

/-- **PBAP makes the zero side nonnegative on prime-blind tests.** -/
theorem re_W_nonneg_of_primeBlindPositive (hP : WeilOneSided.PrimeBlindPositive) {F : ℝ → ℝ}
    (hF : ExpDecayTest F) (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) :
    0 ≤ (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  rw [← archPoleEnergy_eq_re_W_of_blind hF hblind]
  exact archPoleEnergy_nonneg_of_primeBlindPositive hP hF hblind

/-- **A detection receiver.**  A prime-blind test of the decay class on which the zero side is
negative refutes prime-blind positivity, and with it RH. -/
theorem not_riemannHypothesis_of_re_W_neg {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hneg : (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re < 0) :
    ¬ RiemannHypothesis := fun hRH =>
  absurd (re_W_nonneg_of_primeBlindPositive
    (WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mp
      ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH⟩) hF hblind) (not_le.mpr hneg)

/-- **Every Weil-positive boundary measure reproduces the zero side on prime-blind tests.**  For
every full-cone Weil-positive `lam` and every prime-blind test `F` of the decay class,
`∫ |F̂|² dμ_lam = Re Σ_ρ m_ρ F̂(γ_ρ) · conj F̂(conj γ_ρ)`.  A cone point is a positive measure on
the real line that agrees with the zero configuration of `ζ` on every prime-blind test. -/
theorem integral_norm_sq_paperFT_eq_re_W {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂boundaryMeasure hW =
      (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  rw [integral_norm_sq_paperFT_eq_archPoleEnergy hF hblind hW,
    archPoleEnergy_eq_re_W_of_blind hF hblind]

/-- **Weil positivity on the decay class under RH.**  If RH holds, then for every real test of the
decay class the zero side is the boundary-measure energy of `Λ`, and
`archPoleEnergy F − abelPrimePairing Λ F = ∫ |F̂|² dμ_Λ ≥ 0`. -/
theorem archPoleEnergy_sub_abelPrimePairing_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    0 ≤ archPoleEnergy F -
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F := by
  rw [← integral_norm_sq_paperFT_eq_archPoleEnergy_sub hF
    (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH)]
  exact integral_nonneg fun r => by positivity

/-- **Under RH the zero side is a positive spectral energy on the decay class.** -/
theorem re_W_eq_integral_of_riemannHypothesis (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (hF : ExpDecayTest F) :
    (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re =
      ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2
        ∂boundaryMeasure (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) := by
  rw [integral_norm_sq_paperFT_eq_archPoleEnergy_sub hF,
    archPoleEnergy_eq_re_W_add_abelPrimePairing hF]
  ring

end RHTower.WeilSpectral
