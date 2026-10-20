import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».LacunaryCriticalBlockPositivity

/-!
# Multi-Scale Low-Mode / Cross-Window Critical Positivity and the Grid-Tent Relative Schur Bridge

This module closes the multi-scale and low-mode positivity bridge across four regimes:

1. **Scale-Free Polar and Gamma Channel Bounds (`sq_sum_abs_div_succ_le_pi_sq_div_six`,
   `abs_criticalTruncatedPolarProduct_le_all_scales`, `neg_le_criticalTruncatedGammaPolar_all_scales`):**
   Using Cauchy–Schwarz against `∑_{d ≥ 1} d^{-2} = π²/6` (`hasSum_zeta_two`), the polar readout
   sum satisfies `(∑_{n ∈ S} |b_n|/(n+1))² ≤ (π²/6) ∑_{n ∈ S} b_n²` on **every** finite support
   `S ⊂ ℕ` (including `n = 0`, i.e., mode scale `n + 1 = 1 < M₀`), removing the `M ≥ 2` barrier
   from the Gamma and polar channels.

2. **Two-Band (Low-Mode + High-Mode) Archimedean Lévy Coercivity
   (`ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split`):**
   For any disjoint decomposition `S = S_low ∪ S_high` where `S_low ⊂ ℕ` is an arbitrary low-mode
   support (including modes `M < M₀` down to `n = 0`) and `∀ n ∈ S_high, M ≤ n + 1` (`M ≥ 2`),
   evaluating the high-band Plancherel mass of `g^V = g_low^V + (g_{c,high} - h_high^V)` above the
   cutoff `R = η(A_c/2, D_c) M` proves
   `ENNReal.ofReal (s_T (log M - c_T) (E_high - (16 U / A_c) E_low)) ≤ sourceLevyEnergy (criticalTruncatedSource V (S_low ∪ S_high) b)`
   for all `V ≥ criticalTwoBandTruncationThreshold`.

3. **Cross-Window Prime Channel Bounds and Multi-Scale Complete Positivity
   (`abs_criticalTruncatedPrimeEnergy_le_of_low_and_window`,
   `abs_criticalTruncatedPrimeEnergy_le_of_lowWindow_lacunary`,
   `exists_low_and_polynomial_window_compact_weil_pos`,
   `exists_lowWindow_lacunary_compact_weil_pos`):**
   - **Low-Scale Modes + High-Scale Polynomial Window (`[M, LM]`, `L ≤ M^δ`):**
     Via scaled polarization `b^± = α b_low ± α⁻¹ b_high` with `α = √(3 + log(LM))` on the joint
     window `ScaleWindow (S_low ∪ S_high) 1 (LM)`, the cross-window prime coupling is bounded by
     `C_TW (3 + log(LM))² E_low + C_TW E_high`, increasing the high-window prime coefficient from
     `C_TW (3 + log L)` to `C_TW (4 + log L)` with no lacunary gap requirement between `S_low` and `S_high`.
   - **Low-Scale Window (`[1, L_low]`) + Arbitrary-Depth Lacunary Block Family (`[M_0, M_0^{8^{J-1}}]`):**
     Decomposing `S_low` into singletons `{n}` (`DyadicScaleBlock {n} (n+1)`) and applying
     `abs_truncatedBlockCoupling_le_of_pow_le` against `IsLacunaryBlockFamily J M S` (`L_low^8 ≤ M 0`)
     bounds the cross-window coupling beyond any `δ`-polynomial width by
     `50 K_CB L_low E_low + 100 K_CB E_high`, uniformly in the block count `J` and truncation `V`.

4. **Zero-Side Relative Schur Complement Bridge to `gridTentPattern` and `smoothGridTentDetector`
   (`smoothGridTentDetector_pos_of_relative_multiScale_margin`,
   `riemannHypothesis_iff_eventually_smoothGridTentDetector_within_schur_cone`):**
   Combining `SourceRelativeSchurMarginAndPerturbationCalculus` with smooth multi-scale critical
   sources and `smoothGridTentDetector`, every single-scale grid tent detector within the sharp
   relative zero-square-mass radius `ε < (√(1 + δ) - 1)²` of a `δ`-coercive source inherits strict
   positivity of `zetaZeroConfig.W`, `configurationSquareMass - configurationReflectionDefect`,
   `compactFullWeilEnergy`, and `fullZeroForm`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ComplexConjugate ENNReal
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Scale-Free Polar and Gamma Channel Bounds on Arbitrary Supports `S ⊂ ℕ` -/

/-- **Scale-free Euler–Basel bound for reciprocal square scales.**
For every finite set `S : Finset ℕ` (including `0 ∈ S`), `∑_{n ∈ S} 1/(n+1)² ≤ π²/6`. -/
theorem sum_one_div_succ_sq_le_pi_sq_div_six (S : Finset ℕ) :
    ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hz : Summable fun d : ℕ => 1 / (d : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hrew : ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 =
      ∑ d ∈ S.image (fun k : ℕ => k + 1), 1 / (d : ℝ) ^ 2 := by
    rw [Finset.sum_image fun x _ y _ h => Nat.add_right_cancel h]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hrew, ← hasSum_zeta_two.tsum_eq]
  exact hz.sum_le_tsum _ fun d _ => by positivity

/-- **Scale-free Cauchy–Schwarz bound for polar readouts.**
For every finite set `S : Finset ℕ` (with no lower scale restriction `M ≥ 2`, allowing `0 ∈ S`),
`(∑_{n ∈ S} |b_n|/(n+1))² ≤ (π²/6) ∑_{n ∈ S} b_n²`. -/
theorem sq_sum_abs_div_succ_le_pi_sq_div_six (S : Finset ℕ) (b : ℕ → ℝ) :
    (∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ Real.pi ^ 2 / 6 * ∑ n ∈ S, b n ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
  have h1 : ∑ n ∈ S, |b n| * (1 / ((n + 1 : ℕ) : ℝ)) = ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by ring
  have h2 : ∑ n ∈ S, |b n| ^ 2 = ∑ n ∈ S, b n ^ 2 :=
    Finset.sum_congr rfl fun n _ => sq_abs (b n)
  rw [h1, h2] at hcs
  calc (∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) ^ 2
      ≤ (∑ n ∈ S, b n ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := hcs
    _ ≤ (∑ n ∈ S, b n ^ 2) * (Real.pi ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (sum_one_div_succ_sq_le_pi_sq_div_six S)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = Real.pi ^ 2 / 6 * ∑ n ∈ S, b n ^ 2 := by ring

/-- Scale-free Gamma + polar channel constant `|Ω(0)| U + 48 π² a_R a_E`, valid on every `S ⊂ ℕ`. -/
def criticalAllScaleGammaPolarConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    48 * Real.pi ^ 2 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant

theorem criticalAllScaleGammaPolarConstant_nonneg : 0 ≤ criticalAllScaleGammaPolarConstant := by
  unfold criticalAllScaleGammaPolarConstant criticalCollarMassUpper
    criticalTruncatedReadoutConstant criticalTruncatedEndpointConstant
  have h1 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
    integral_nonneg fun _ => abs_nonneg _
  have h3 : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
  have h4 := smoothTransitionSlope_nonneg
  have h5 := factorialUnitIntervalUpper_pos.le
  positivity

/-- **Scale-free polar product bound.** For every `S : Finset ℕ`, `b : ℕ → ℝ`, and `V ≥ 1`,
`|R^V E^V| ≤ 24 π² a_R a_E ∑_{n ∈ S} b_n²`. -/
theorem abs_criticalTruncatedPolarProduct_le_all_scales (S : Finset ℕ) (b : ℕ → ℝ)
    {V : ℝ} (hV : 1 ≤ V) :
    |criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b| ≤
      24 * Real.pi ^ 2 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant *
        ∑ n ∈ S, b n ^ 2 := by
  have hV0 : 0 < V := by linarith
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  set a := criticalTruncatedReadoutConstant
  set c := criticalTruncatedEndpointConstant
  have ha : 0 ≤ a := by
    unfold a criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ c := by
    unfold c criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  rw [abs_mul]
  have h1 := abs_criticalTruncatedPolarReadout_le hV0 S b
  have h2 := abs_criticalTruncatedPolarEndpoint_le hV S b
  have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hT2 := sq_sum_abs_div_succ_le_pi_sq_div_six S b
  calc |criticalTruncatedPolarReadout V S b| * |criticalTruncatedPolarEndpoint V S b|
      ≤ a * (12 * T) * (c * (12 * T)) := h12
    _ = 144 * a * c * T ^ 2 := by ring
    _ ≤ 144 * a * c * (Real.pi ^ 2 / 6 * ∑ n ∈ S, b n ^ 2) :=
        mul_le_mul_of_nonneg_left hT2 (by positivity)
    _ = 24 * Real.pi ^ 2 * a * c * ∑ n ∈ S, b n ^ 2 := by ring

/-- **Scale-free Gamma + polar lower bound on arbitrary finite supports `S ⊂ ℕ`.** -/
theorem neg_le_criticalTruncatedGammaPolar_all_scales (S : Finset ℕ) (b : ℕ → ℝ)
    {V : ℝ} (hV : 1 ≤ V) :
    -(criticalAllScaleGammaPolarConstant * ∑ n ∈ S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
        2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) := by
  set E := ∑ n ∈ S, b n ^ 2
  set ac := sourceAutocorrelation (criticalTruncatedSource V S b) 0
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hpol := (abs_le.mp (abs_criticalTruncatedPolarProduct_le_all_scales S b hV)).1
  unfold criticalAllScaleGammaPolarConstant
  linarith

/-! ## Section 2: Two-Band (Low-Mode + High-Mode) Archimedean Lévy Coercivity -/

/-- Disjoint union additivity for `realPhaseCombination`. -/
theorem realPhaseCombination_union {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (b : ℕ → ℝ) (v : ℝ) :
    realPhaseCombination (S₁ ∪ S₂) b v =
      realPhaseCombination S₁ b v + realPhaseCombination S₂ b v := by
  unfold realPhaseCombination
  exact Finset.sum_union hdisj

/-- Disjoint union additivity for `criticalCollaredSource`. -/
theorem criticalCollaredSource_union {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (b : ℕ → ℝ) (x : ℝ) :
    criticalCollaredSource (S₁ ∪ S₂) b x =
      criticalCollaredSource S₁ b x + criticalCollaredSource S₂ b x := by
  by_cases hx : x ≤ 0
  · simp only [criticalCollaredSource, criticalFactorialSource,
      indicator_of_mem (show x ∈ Iic 0 from hx), factorialPhaseCombination_re_eq,
      realPhaseCombination_union hdisj]
    ring
  · simp only [criticalCollaredSource, criticalFactorialSource,
      indicator_of_notMem (show x ∉ Iic 0 from hx), mul_zero, add_zero]

/-- Disjoint union additivity for `criticalTruncatedSource`. -/
theorem criticalTruncatedSource_union (V : ℝ) {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedSource V (S₁ ∪ S₂) b x =
      criticalTruncatedSource V S₁ b x + criticalTruncatedSource V S₂ b x := by
  unfold criticalTruncatedSource
  rw [criticalCollaredSource_union hdisj]
  ring

/-- Two-band truncation threshold `max(2 + L, 16 U / A_c)`. -/
def criticalTwoBandTruncationThreshold : ℝ :=
  max (2 + factorialWindowLength) (16 * criticalCollarMassUpper / criticalCollarMassLower)

theorem criticalTruncationThreshold_le_twoBand :
    criticalTruncationThreshold ≤ criticalTwoBandTruncationThreshold := by
  unfold criticalTruncationThreshold criticalTwoBandTruncationThreshold
  refine max_le_max le_rfl ?_
  have hA : 0 < criticalCollarMassLower := criticalCollarMassLower_pos
  have hU : 0 ≤ criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  exact div_le_div_of_nonneg_right (by linarith) hA.le

/-- Low-mode Plancherel penalty ratio `16 U / A_c` in the two-band Archimedean Lévy law. -/
def criticalLowModePenaltyRatio : ℝ :=
  16 * criticalCollarMassUpper / criticalCollarMassLower

theorem criticalLowModePenaltyRatio_pos : 0 < criticalLowModePenaltyRatio := by
  unfold criticalLowModePenaltyRatio
  have := criticalCollarMassLower_pos
  have : 0 < criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  positivity

/-- **Two-Band (Low-Mode + High-Mode) Archimedean Lévy Coercivity.**
For any disjoint decomposition `S = S_low ∪ S_high` where `S_low ⊂ ℕ` is an arbitrary low-mode
set (including `n = 0`) and `∀ n ∈ S_high, M ≤ n + 1` (`M ≥ 2`, `c_T ≤ log M`), and every truncation
`V ≥ criticalTwoBandTruncationThreshold`, the Lévy energy of `criticalTruncatedSource V (S_low ∪ S_high) b`
dominates `s_T (log M - c_T) (E_high - (16 U / A_c) E_low)` for every coefficient vector `b`. -/
theorem ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hM_log : criticalTruncatedArchLogOffset ≤ Real.log M)
    (hS_high : ∀ n ∈ S_high, M ≤ n + 1)
    {V : ℝ} (hV : criticalTwoBandTruncationThreshold ≤ V) :
    ENNReal.ofReal (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
      ((∑ n ∈ S_high, b n ^ 2) - criticalLowModePenaltyRatio * ∑ n ∈ S_low, b n ^ 2)) ≤
      sourceLevyEnergy (criticalTruncatedSource V (S_low ∪ S_high) b) := by
  set A := criticalCollarMassLower
  set D := criticalCollarLowFreqConstant
  set U := criticalCollarMassUpper
  set η := lowFreqRelativeCutoff (A / 2) D
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  set S := S_low ∪ S_high
  set g := criticalTruncatedSource V S b
  set g_low := criticalTruncatedSource V S_low b
  set gc_high := criticalCollaredSource S_high b
  set h_high := criticalTruncationTail V S_high b
  have hA : 0 < A := criticalCollarMassLower_pos
  have hD : 0 < D := criticalCollarLowFreqConstant_pos
  have hη : 0 < η := lowFreqRelativeCutoff_pos (by positivity) hD
  have hE_low : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU : 0 ≤ U := by
    unfold U criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  have hL := factorialWindowLength_pos
  have hV1 : 2 + factorialWindowLength ≤ V := (le_max_left _ _).trans hV
  have hV2 : 16 * U / A ≤ V := (le_max_right _ _).trans hV
  have hVpos : 0 < V := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - criticalTruncatedArchLogOffset = Real.log R - 3 := by
    unfold criticalTruncatedArchLogOffset
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]
    ring
  rw [hlogR]
  have hR_nonneg : 0 ≤ Real.log R - 3 := by linarith
  rcases eq_or_lt_of_le hR_nonneg with hzero | hpos
  · rw [← hzero, mul_zero, zero_mul, ENNReal.ofReal_zero]
    exact zero_le _
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  have hg := admissibleSource_criticalTruncatedSource V S b
  have hg_low := admissibleSource_criticalTruncatedSource V S_low b
  have hg_high := admissibleSource_criticalTruncatedSource V S_high b
  have hgc_high := admissibleSource_criticalCollaredSource S_high b
  have hh_high := admissibleSource_criticalTruncationTail V S_high b
  have hhigh := sourceLevyEnergy_ge_highBand hg hR1
  have hmi := integrable_levySourceSpectralDensity hg
  have hhi := integrable_levySourceSpectralDensity hh_high
  have hli := integrable_levySourceSpectralDensity hg_low
  have hsplit : ∀ t, levySourceSpectralDensity g t ≤
      2 * levySourceSpectralDensity gc_high t +
        4 * levySourceSpectralDensity h_high t +
        4 * levySourceSpectralDensity g_low t := by
    intro t
    have hfun1 : (fun x => (g x : ℂ)) =
        (fun x => (g_low x : ℂ)) + (1 : ℂ) • fun x => (criticalTruncatedSource V S_high b x : ℂ) := by
      funext x
      have hu := criticalTruncatedSource_union V hdisj b x
      simp only [Pi.add_apply, Pi.smul_apply, one_smul, g, g_low, S]
      rw [hu]
      push_cast
      ring
    have hfun2 : (fun x => (criticalTruncatedSource V S_high b x : ℂ)) =
        (fun x => (gc_high x : ℂ)) + (-1 : ℂ) • fun x => (h_high x : ℂ) := by
      funext x
      have ht := criticalTruncatedSource_add_tail V S_high b x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gc_high, h_high]
      rw [← ht]
      push_cast
      ring
    unfold levySourceSpectralDensity
    rw [hfun1, RHTower.WeilSpectral.paperFT_add_smul_real hg_low.1 hg_high.1, one_mul,
      hfun2, RHTower.WeilSpectral.paperFT_add_smul_real hgc_high.1 hh_high.1, neg_one_mul,
      ← sub_eq_add_neg]
    set u1 := ‖paperFT (fun y => (g_low y : ℂ)) t‖
    set u2 := ‖paperFT (fun y => (gc_high y : ℂ)) t‖
    set u3 := ‖paperFT (fun y => (h_high y : ℂ)) t‖
    have htr1 : ‖paperFT (fun y => (g_low y : ℂ)) t +
        (paperFT (fun y => (gc_high y : ℂ)) t - paperFT (fun y => (h_high y : ℂ)) t)‖ ≤
        u1 + (u2 + u3) :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    have hnn : 0 ≤ ‖paperFT (fun y => (g_low y : ℂ)) t +
        (paperFT (fun y => (gc_high y : ℂ)) t - paperFT (fun y => (h_high y : ℂ)) t)‖ :=
      norm_nonneg _
    have hsq1 : ‖paperFT (fun y => (g_low y : ℂ)) t +
        (paperFT (fun y => (gc_high y : ℂ)) t - paperFT (fun y => (h_high y : ℂ)) t)‖ ^ 2 ≤
        (u1 + (u2 + u3)) ^ 2 := pow_le_pow_left₀ hnn htr1 2
    nlinarith [sq_nonneg (u2 - u1 - u3), sq_nonneg (u1 - u3)]
  have hlowc : ∀ t ∈ Icc (-R) R, levySourceSpectralDensity gc_high t ≤
      2 * D ^ 2 / M * E_high := by
    intro t ht
    refine norm_sq_paperFT_criticalCollaredSource_le S_high b hM hS_high ?_
    have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
    calc |t| ≤ R := abs_le.mpr ht
      _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
  have htail := integral_criticalTruncationTail_sq_le (V := V) (by linarith) S_high b
  have hhtot := integral_levySourceSpectralDensity hh_high
  have hltot := integral_levySourceSpectralDensity hg_low
  have hhnn : ∀ t, 0 ≤ levySourceSpectralDensity h_high t := fun _ => sq_nonneg _
  have hlnn : ∀ t, 0 ≤ levySourceSpectralDensity g_low t := fun _ => sq_nonneg _
  have hglow_sq : ∫ x, g_low x ^ 2 ≤ U * E_low := by
    have hsq : sourceAutocorrelation g_low 0 = ∫ y, g_low y ^ 2 := by
      unfold sourceAutocorrelation; simp only [sub_zero, sq]
    rw [← hsq]
    exact sourceAutocorrelation_criticalTruncatedSource_zero_le V S_low b
  have hlow : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
      A / 2 * E_high + 4 * (U / V * E_high) + 4 * (U * E_low) := by
    have hc : IntegrableOn (fun _ : ℝ => 2 * (2 * D ^ 2 / M * E_high)) (Icc (-R) R) :=
      integrableOn_const (by simp)
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
        ∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E_high) +
          4 * levySourceSpectralDensity h_high t +
          4 * levySourceSpectralDensity g_low t) :=
      setIntegral_mono_on hmi.integrableOn
        ((hc.add (hhi.integrableOn.const_mul 4)).add (hli.integrableOn.const_mul 4))
        measurableSet_Icc fun t ht => (hsplit t).trans (by gcongr; exact hlowc t ht)
    have h2 : (∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E_high) +
          4 * levySourceSpectralDensity h_high t +
          4 * levySourceSpectralDensity g_low t)) ≤
        (2 * R) * (2 * (2 * D ^ 2 / M * E_high)) +
          4 * (2 * Real.pi * ∫ x, h_high x ^ 2) +
          4 * (2 * Real.pi * ∫ x, g_low x ^ 2) := by
      rw [integral_add (hc.add (hhi.integrableOn.const_mul 4)) (hli.integrableOn.const_mul 4),
        integral_add hc (hhi.integrableOn.const_mul 4), setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, integral_const_mul,
        integral_const_mul, ← hhtot, ← hltot]
      rw [show R - -R = 2 * R by ring]
      refine add_le_add (add_le_add le_rfl ?_) ?_
      · exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hhi (Eventually.of_forall hhnn)) (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hli (Eventually.of_forall hlnn)) (by norm_num)
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E_high)) ≤ (A / 2) / 2 * E_high := by
      have := low_band_plancherel_energy_le_half_arch (A := A / 2) hD hE_high hM
      calc 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E_high)) =
            (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E_high / (M : ℝ)) := by ring
        _ ≤ _ := this
    calc 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * (2 * D ^ 2 / M * E_high)) +
            4 * (2 * Real.pi * ∫ x, h_high x ^ 2) +
            4 * (2 * Real.pi * ∫ x, g_low x ^ 2)) := by
          gcongr; exact h1.trans h2
      _ = 2 * (1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E_high))) +
            4 * (∫ x, h_high x ^ 2) + 4 * (∫ x, g_low x ^ 2) := by field_simp
      _ ≤ 2 * ((A / 2) / 2 * E_high) + 4 * (U / V * E_high) + 4 * (U * E_low) := by gcongr
      _ = A / 2 * E_high + 4 * (U / V * E_high) + 4 * (U * E_low) := by ring
  have hUV : 4 * (U / V * E_high) ≤ A / 4 * E_high := by
    have : U / V ≤ A / 16 := by
      rw [div_le_iff₀ hVpos]
      have := (div_le_iff₀ hA).mp hV2
      linarith
    nlinarith
  have hmass_tot := integral_criticalTruncatedSource_sq_ge hV1 S b
  have hE_union : ∑ n ∈ S, b n ^ 2 = E_low + E_high := Finset.sum_union hdisj
  have hmass : A * E_high ≤ ∫ y, g y ^ 2 := by
    rw [hE_union] at hmass_tot
    nlinarith
  have htot := integral_levySourceSpectralDensity hg
  have hsplit2 := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmi
  have hhighmass : A / 4 * (E_high - criticalLowModePenaltyRatio * E_low) ≤
      1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g t := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t = ∫ y, g y ^ 2 := by
      rw [htot]; field_simp; rfl
    rw [← hsplit2, mul_add] at h1
    have hpen : A / 4 * (criticalLowModePenaltyRatio * E_low) = 4 * (U * E_low) := by
      unfold criticalLowModePenaltyRatio A U
      field_simp [hA.ne']
      ring
    linarith
  refine le_trans ?_ hhigh
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  rw [show criticalTruncatedArchLogSlope * (Real.log R - 3) *
      (E_high - criticalLowModePenaltyRatio * E_low) =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) *
        (A / 4 * (E_high - criticalLowModePenaltyRatio * E_low)) by
      unfold criticalTruncatedArchLogSlope A; ring, ENNReal.ofReal_mul hc0]
  gcongr

end GaloisForLFunctions.ArithmeticPositivityTheory
