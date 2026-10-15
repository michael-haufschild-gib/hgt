import GaloisForLFunctions.RHTower.CHMDStage13TwoPointPacketsAndPolarNodeElimination

/-!
# CHMD Stage 14: Unconditional Zero-Side Explicit Formula for `evenWeilDensity`, `cosineShiftFn`, and the `sechHalf` Toeplitz Form

This module establishes the fourteenth stage of the **Causal Hyperbolic–Modular Duality (CHMD)**
formalization in `RHTower`, proving the **unconditional explicit-formula bridge** connecting the
prime/archimedean/pole spectral functional `evenWeilDensity Λ`, the 1D correlation function
`cosineShiftFn Λ Φ`, and the decisive `sechHalf` Toeplitz quadratic form directly to the nontrivial
zero configuration `zetaZeroConfig.W` of $\zeta(s)$—with **zero hypotheses**:

1. **Unconditional Equality of `atomPairing` and `abelPrimePairing` on `EvenStrip`**:
   - Because every `EvenStrip Φ` has strip width $b = 5/4 > 1$, its inverse Fourier transform
     `stripTest Φ` has exponential decay $O(e^{-(5/4)|x|})$. Consequently, as the truncation radius
     $L \to \infty$, `atomPairing Λ (crossCorr (truncTest (stripTest Φ) L) (truncTest (stripTest Φ) L))`
     converges both to `atomPairing Λ (crossCorr (stripTest Φ) (stripTest Φ))` (by dominated
     convergence on $b > 1$) and to `abelPrimePairing Λ (stripTest Φ)` (by summation by parts on
     `ExpDecayTest`). By uniqueness of limits,
     $$\operatorname{atomPairing}\ \Lambda\ \bigl(\operatorname{crossCorr}(\operatorname{stripTest}\ \Phi)\ (\operatorname{stripTest}\ \Phi)\bigr)
       = \operatorname{abelPrimePairing}\ \Lambda\ (\operatorname{stripTest}\ \Phi)$$
     unconditionally (`atomPairing_stripTest_eq_abelPrimePairing`).

2. **Unconditional Zero-Side Formula for `evenWeilDensity Λ (specSq Φ)`**:
   - Combining `evenWeilDensity_specSq`, `archPoleEnergy_eq_re_W_add_abelPrimePairing`, and
     `paperFT_stripTest` on the critical strip $|\operatorname{Im} z| < 1/2 < 5/4$, we prove that
     for every `EvenStrip Φ`,
     $$\operatorname{evenWeilDensity}\ \Lambda\ (\operatorname{specSq}\ \Phi)
       = \Bigl(\operatorname{zetaZeroConfig.W}\ (\operatorname{stripTest}\ \Phi)\ (\operatorname{stripTest}\ \Phi)\Bigr).\operatorname{re}
       = \Bigl(\sum'_{\rho : \operatorname{zetaZeroConfig.carrier}}
           (m_\rho : \mathbb{C}) \cdot \operatorname{specSq}\ \Phi\ (\operatorname{gammaOf}\ \rho)\Bigr).\operatorname{re}$$
     with **zero hypotheses** (`evenWeilDensity_specSq_vonMangoldt_eq_re_W`,
     `Wsummand_stripTest_eq_mult_mul_specSq`, `W_stripTest_eq_tsum_specSq`,
     `evenWeilDensity_specSq_vonMangoldt_eq_re_tsum_specSq`).

3. **Unconditional Zero-Side Formula for the Decisive `sechHalf` Toeplitz Quadratic Form**:
   - Applying this theorem to `cosComb t c Φ` and `sinComb t c Φ` (which are both `EvenStrip`), we
     obtain the unconditional zero-side representation of the Toeplitz quadratic form:
     $$\sum_{i, j} c_i c_j \operatorname{cosineShiftFn}\ \Lambda\ \Phi\ (t_j - t_i)
       = \Bigl(\operatorname{zetaZeroConfig.W}\ (\operatorname{stripTest}(\operatorname{cosComb}\ t\ c\ \Phi))\ (\operatorname{stripTest}(\operatorname{cosComb}\ t\ c\ \Phi))\Bigr).\operatorname{re}
       + \Bigl(\operatorname{zetaZeroConfig.W}\ (\operatorname{stripTest}(\operatorname{sinComb}\ t\ c\ \Phi))\ (\operatorname{stripTest}(\operatorname{sinComb}\ t\ c\ \Phi))\Bigr).\operatorname{re}$$
     (`sum_sum_cosineShiftFn_vonMangoldt_eq_re_W_add_re_W`,
     `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_re_W_add_re_W`).
   - At every critical-line zero $\rho$ ($\operatorname{Re}(\rho) = 1/2$, so
     $\operatorname{gammaOf}\ \rho = (\operatorname{Im}\ \rho : \mathbb{C}) \in \mathbb{R}$), the
     combined `cosComb + sinComb` summand for `sechHalf` has real part
     $$m_\rho \cdot \operatorname{trigPacketWeight}\ t\ c\ \Bigl(\sqrt{(\operatorname{Im}\ \rho)^2 + 2}\Bigr)
       \cdot \operatorname{sechSqHalf}(\operatorname{Im}\ \rho) \ge 0$$
     (`re_Wsummand_cosComb_add_sinComb_sechHalf_of_criticalLine`,
     `re_Wsummand_cosComb_add_sinComb_sechHalf_nonneg_of_criticalLine`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDStage14

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage1 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13

/-! ## Section 1: Unconditional Equality of `atomPairing` and `abelPrimePairing` on `EvenStrip` -/

/-- Every `EvenStrip Φ` yields an `ExpDecayTest (stripTest Φ)`. -/
theorem expDecayTest_of_evenStrip {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    ExpDecayTest (stripTest Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  exact expDecayTest_stripTest (by norm_num : (1 / 2 : ℝ) < 5 / 4) hε hs

/-- **Unconditional Equality of `atomPairing` and `abelPrimePairing` on `EvenStrip`**:
for every `EvenStrip Φ`, the prime autocorrelation series
`atomPairing Λ (crossCorr (stripTest Φ) (stripTest Φ))` equals `abelPrimePairing Λ (stripTest Φ)`. -/
theorem atomPairing_stripTest_eq_abelPrimePairing {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (stripTest Φ) (stripTest Φ)) =
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (stripTest Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have hE : ExpDecayTest (stripTest Φ) := expDecayTest_stripTest (by norm_num) hε hs
  obtain ⟨_, hC', hdec⟩ := decayBound_stripTest (by norm_num : (1 / 2 : ℝ) < 5 / 4) hε hs
  have hlim1 :
      Tendsto
        (fun L : ℝ =>
          atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (crossCorr (truncTest (stripTest Φ) L) (truncTest (stripTest Φ) L)))
        atTop
        (𝓝 (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (stripTest Φ) (stripTest Φ)))) := by
    refine tendsto_atomPairing_truncTest_of_growth
      abs_vonMangoldt_le_sqrt_mul_one_add_log hE (by norm_num : (1 : ℝ) < 5 / 4) hC' fun x => ?_
    have hx := (hdec x).1
    rwa [show (1 / 2 : ℝ) + (5 / 4 - 1 / 2) = 5 / 4 by ring] at hx
  have hlim2 :
      Tendsto
        (fun L : ℝ =>
          atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (crossCorr (truncTest (stripTest Φ) L) (truncTest (stripTest Φ) L)))
        atTop
        (𝓝 (abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (stripTest Φ))) :=
    tendsto_atomPairing_truncTest_abelPrimePairing hE (A := 7)
      (w := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (fun N => abs_primeWeightPartialSum_vonMangoldt_le N)
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## Section 2: Unconditional Zero-Side Explicit Formula for `evenWeilDensity Λ (specSq Φ)` -/

/-- **Unconditional Zero-Side Formula for `evenWeilDensity Λ (specSq Φ)`**:
for every `EvenStrip Φ`, `evenWeilDensity Λ (specSq Φ)` equals the real part of the nontrivial
zero sum `zetaZeroConfig.W` of `stripTest Φ`. -/
theorem evenWeilDensity_specSq_vonMangoldt_eq_re_W {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq Φ) =
      (zetaZeroConfig.W (fun u => (stripTest Φ u : ℂ)) (fun u => (stripTest Φ u : ℂ))).re := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have hE : ExpDecayTest (stripTest Φ) := expDecayTest_stripTest (by norm_num) hε hs
  rw [evenWeilDensity_specSq (by norm_num : (1 / 2 : ℝ) < 5 / 4) hε hs hΦ.sym,
    atomPairing_stripTest_eq_abelPrimePairing hΦ,
    archPoleEnergy_eq_re_W_add_abelPrimePairing hE, add_sub_cancel_right]

/-- For every `EvenStrip Φ` and every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`paperFT (fun u => (stripTest Φ u : ℂ)) (gammaOf ρ) = Φ (gammaOf ρ)`. -/
theorem paperFT_stripTest_gammaOf_of_evenStrip {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    (ρ : zetaZeroConfig.carrier) :
    Zeta23.paperFT (fun u => (stripTest Φ u : ℂ)) (Zeta23.gammaOf ρ) =
      Φ (Zeta23.gammaOf ρ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact paperFT_stripTest (by norm_num : (0 : ℝ) < 5 / 4) hε hs hΦ.sym (by linarith)

/-- For every `EvenStrip Φ` and every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`paperFT (fun u => (stripTest Φ u : ℂ)) (conj (gammaOf ρ)) = Φ (conj (gammaOf ρ))`. -/
theorem paperFT_stripTest_conj_gammaOf_of_evenStrip {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    (ρ : zetaZeroConfig.carrier) :
    Zeta23.paperFT (fun u => (stripTest Φ u : ℂ)) (conj (Zeta23.gammaOf ρ)) =
      Φ (conj (Zeta23.gammaOf ρ)) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(conj (Zeta23.gammaOf (ρ : ℂ))).im| < 1 / 2 := by
    rw [Complex.conj_im, abs_neg]
    exact WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  exact paperFT_stripTest (by norm_num : (0 : ℝ) < 5 / 4) hε hs hΦ.sym (by linarith)

/-- **Exact Summand Evaluation on `EvenStrip`**:
for every `EvenStrip Φ` and every nontrivial zero `ρ : zetaZeroConfig.carrier`,
`zetaZeroConfig.Wsummand (stripTest Φ) (stripTest Φ) ρ = (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (gammaOf ρ)`. -/
theorem Wsummand_stripTest_eq_mult_mul_specSq {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun u => (stripTest Φ u : ℂ)) (fun u => (stripTest Φ u : ℂ)) ρ =
      (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (Zeta23.gammaOf ρ) := by
  unfold ZeroConfig.Wsummand specSq
  rw [paperFT_stripTest_gammaOf_of_evenStrip hΦ ρ,
    paperFT_stripTest_conj_gammaOf_of_evenStrip hΦ ρ, mul_assoc]

/-- **Exact Zero-Side Series Evaluation on `EvenStrip`**:
for every `EvenStrip Φ`,
`zetaZeroConfig.W (stripTest Φ) (stripTest Φ) = ∑' ρ, (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (gammaOf ρ)`. -/
theorem W_stripTest_eq_tsum_specSq {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    zetaZeroConfig.W (fun u => (stripTest Φ u : ℂ)) (fun u => (stripTest Φ u : ℂ)) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (Zeta23.gammaOf ρ) := by
  unfold ZeroConfig.W
  exact tsum_congr (Wsummand_stripTest_eq_mult_mul_specSq hΦ)

/-- **Unconditional Zero-Side Spectral Series Formula for `evenWeilDensity Λ (specSq Φ)`**:
for every `EvenStrip Φ`,
`evenWeilDensity Λ (specSq Φ) = (∑' ρ, (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (gammaOf ρ)).re`. -/
theorem evenWeilDensity_specSq_vonMangoldt_eq_re_tsum_specSq {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq Φ) =
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq Φ (Zeta23.gammaOf ρ)).re := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_re_W hΦ, W_stripTest_eq_tsum_specSq hΦ]

/-- **Unconditional Zero-Side Formula for `cosineShiftFn Λ sechHalf 0`**:
at $y = 0$, `cosineShiftFn Λ sechHalf 0` equals the real part of the zero-side sum of
`specSq sechHalf (gammaOf ρ)`. -/
theorem cosineShiftFn_sechHalf_vonMangoldt_zero_eq_re_tsum_specSq :
    cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf 0 =
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq sechHalf (Zeta23.gammaOf ρ)).re := by
  have h0 : rhoCosShift 0 sechHalf = specSq sechHalf := by
    funext z; unfold rhoCosShift; simp
  unfold cosineShiftFn
  rw [h0, evenWeilDensity_specSq_vonMangoldt_eq_re_tsum_specSq evenStrip_sechHalf]

/-! ## Section 3: Unconditional Zero-Side Formula for the Toeplitz Quadratic Form and Pointwise `cosineShiftFn` -/

/-- **Unconditional Zero-Side Formula for the Toeplitz Quadratic Form of Any `EvenStrip Φ`**:
for every `EvenStrip Φ` and every finite wave packet `(t, c)`, the Toeplitz quadratic form of
`cosineShiftFn Λ Φ` equals the sum of the real parts of `zetaZeroConfig.W` on
`stripTest (cosComb t c Φ)` and `stripTest (sinComb t c Φ)`. -/
theorem sum_sum_cosineShiftFn_vonMangoldt_eq_re_W_add_re_W {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ (t j - t i)) =
      (zetaZeroConfig.W
        (fun u => (stripTest (cosComb t c Φ) u : ℂ))
        (fun u => (stripTest (cosComb t c Φ) u : ℂ))).re +
      (zetaZeroConfig.W
        (fun u => (stripTest (sinComb t c Φ) u : ℂ))
        (fun u => (stripTest (sinComb t c Φ) u : ℂ))).re := by
  rw [sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional
      abs_vonMangoldt_le_sqrt_mul_one_add_log hΦ t c,
    evenWeilDensity_specSq_vonMangoldt_eq_re_W (evenStrip_cosComb t c hΦ),
    evenWeilDensity_specSq_vonMangoldt_eq_re_W (evenStrip_sinComb t c hΦ)]

/-- **Unconditional Zero-Side Series Formula for the Toeplitz Quadratic Form of Any `EvenStrip Φ`**:
expresses the Toeplitz quadratic form directly in terms of `specSq (cosComb t c Φ) (gammaOf ρ)` and
`specSq (sinComb t c Φ) (gammaOf ρ)`. -/
theorem sum_sum_cosineShiftFn_vonMangoldt_eq_re_tsum_add_re_tsum {Φ : ℂ → ℂ} (hΦ : EvenStrip Φ)
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) Φ (t j - t i)) =
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq (cosComb t c Φ) (Zeta23.gammaOf ρ)).re +
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq (sinComb t c Φ) (Zeta23.gammaOf ρ)).re := by
  rw [sum_sum_cosineShiftFn_vonMangoldt_eq_re_W_add_re_W hΦ t c,
    W_stripTest_eq_tsum_specSq (evenStrip_cosComb t c hΦ),
    W_stripTest_eq_tsum_specSq (evenStrip_sinComb t c hΦ)]

/-- **Unconditional Zero-Side Formula for the Decisive `sechHalf` Toeplitz Quadratic Form**:
for every finite wave packet `(t, c)`, the `sechHalf` Toeplitz quadratic form for `Λ` equals the
sum of the zero-side `cosComb` and `sinComb` series. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_re_tsum_add_re_tsum
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i)) =
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ)).re +
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re :=
  sum_sum_cosineShiftFn_vonMangoldt_eq_re_tsum_add_re_tsum evenStrip_sechHalf t c

/-- **Unconditional Zero-Side Equivalence for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every finite wave packet `(t, c)`, the combined
zero-side series of `cosComb t c sechHalf` and `sinComb t c sechHalf` is nonnegative. -/
theorem riemannHypothesis_iff_forall_zeroSide_cosComb_add_sinComb_sechHalf_nonneg :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        0 ≤ (∑' ρ : zetaZeroConfig.carrier,
              (zetaZeroConfig.mult ρ : ℂ) *
                specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ)).re +
            (∑' ρ : zetaZeroConfig.carrier,
              (zetaZeroConfig.mult ρ : ℂ) *
                specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  exact forall_congr' fun N => forall_congr' fun t => forall_congr' fun c => by
    rw [sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_re_tsum_add_re_tsum]

/-- At every nontrivial zero `ρ : zetaZeroConfig.carrier` (on or off the critical line),
`specSq (cosComb t c Φ) (gammaOf ρ) + specSq (sinComb t c Φ) (gammaOf ρ)` expands as the double sum
of `c_i c_j * rhoCosShift (t_j - t_i) Φ (gammaOf ρ)`. -/
theorem specSq_cosComb_add_specSq_sinComb_gammaOf {N : ℕ} (t c : Fin N → ℝ) (Φ : ℂ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    specSq (cosComb t c Φ) (Zeta23.gammaOf ρ) + specSq (sinComb t c Φ) (Zeta23.gammaOf ρ) =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) Φ (Zeta23.gammaOf ρ) := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h54 : |(Zeta23.gammaOf (ρ : ℂ)).im| ≤ 5 / 4 := by linarith
  exact specSq_cosComb_add_specSq_sinComb t c Φ (abs_im_lt_sqrt_two h54)

/-! ## Section 4: Critical-Line Zero Summand Evaluation and Pointwise Nonnegativity -/

/-- When a zero `ρ` lies on the critical line (`(ρ : ℂ).re = 1 / 2`), its spectral coordinate
`gammaOf ρ` is the real ordinate `((ρ : ℂ).im : ℂ)`. -/
theorem gammaOf_eq_ofReal_im_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    Zeta23.gammaOf s = (s.im : ℂ) := by
  unfold Zeta23.gammaOf
  apply Complex.ext
  · simp [Complex.div_I]
  · simp [Complex.div_I, hs]

/-- **Critical-Line Zero Summand Evaluation for `sechHalf`**:
at any nontrivial zero `ρ : zetaZeroConfig.carrier` with `(ρ : ℂ).re = 1 / 2`, the real part of the
combined `cosComb + sinComb` summand for `sechHalf` is the manifestly nonnegative product
`zetaZeroConfig.mult ρ * trigPacketWeight t c (√((Im ρ)² + 2)) * sechSqHalf (Im ρ)`. -/
theorem re_Wsummand_cosComb_add_sinComb_sechHalf_of_criticalLine {N : ℕ} (t c : Fin N → ℝ)
    (ρ : zetaZeroConfig.carrier) (hcrit : (ρ : ℂ).re = 1 / 2) :
    ((zetaZeroConfig.mult ρ : ℂ) * specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ) +
      (zetaZeroConfig.mult ρ : ℂ) * specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re =
      (zetaZeroConfig.mult ρ : ℝ) *
        (trigPacketWeight t c (Real.sqrt ((ρ : ℂ).im ^ 2 + 2)) * sechSqHalf (ρ : ℂ).im) := by
  rw [← mul_add, gammaOf_eq_ofReal_im_of_re_eq_half hcrit,
    show (zetaZeroConfig.mult ρ : ℂ) = ((zetaZeroConfig.mult ρ : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, specSq_cosComb_add_sinComb_sechHalf_ofReal_re]

/-- **Unconditional Nonnegativity of Every Critical-Line Zero Summand**:
for every nontrivial zero `ρ : zetaZeroConfig.carrier` on the critical line (`(ρ : ℂ).re = 1 / 2`)
and every finite wave packet `(t, c)`, the combined `cosComb + sinComb` summand for `sechHalf` has
nonnegative real part. -/
theorem re_Wsummand_cosComb_add_sinComb_sechHalf_nonneg_of_criticalLine {N : ℕ}
    (t c : Fin N → ℝ) (ρ : zetaZeroConfig.carrier) (hcrit : (ρ : ℂ).re = 1 / 2) :
    0 ≤ ((zetaZeroConfig.mult ρ : ℂ) * specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ) +
      (zetaZeroConfig.mult ρ : ℂ) * specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re := by
  rw [re_Wsummand_cosComb_add_sinComb_sechHalf_of_criticalLine t c ρ hcrit]
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (trigPacketWeight_nonneg t c _) (sechSqHalf_pos _).le)

end RHTower.CHMDStage14

end
