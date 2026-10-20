import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».LacunaryCriticalBlockPositivity

/-!
# Multi-Scale Low-Mode / Cross-Window Critical Positivity and Unconditional Grid-Tent Transfer

This module closes the multi-scale and low-mode positivity bridge across four unconditional results:

1. **Scale-Free Polar and Gamma Channel Bounds (`sum_one_div_succ_sq_le_pi_sq_div_six`,
   `sq_sum_abs_div_succ_le_pi_sq_div_six`, `abs_criticalTruncatedPolarProduct_le_all_scales`,
   `neg_le_criticalTruncatedGammaPolar_all_scales`):**
   Using Cauchy–Schwarz against `∑_{d ≥ 1} d^{-2} = π²/6` (`hasSum_zeta_two`), the polar readout
   sum satisfies `(∑_{n ∈ S} |b_n|/(n+1))² ≤ (π²/6) ∑_{n ∈ S} b_n²` on **every** finite support
   `S ⊂ ℕ` (including `0 ∈ S`, i.e., mode scale `n + 1 = 1 < M₀`), removing the `M ≥ 2` barrier
   from the Gamma and polar channels.

2. **Two-Band (Low-Mode + High-Mode) Archimedean Lévy Coercivity
   (`ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split`):**
   For any disjoint decomposition `S = S_low ∪ S_high` where `S_low ⊂ ℕ` is an arbitrary low-mode
   support (including modes `M < M₀` down to `n = 0`) and `∀ n ∈ S_high, M ≤ n + 1` (`M ≥ 2`),
   evaluating the high-band Plancherel mass of `g^V = g_low^V + (g_{c,high} - h_high^V)` above the
   cutoff `R = η(A_c/2, D_c) M` proves unconditionally for every coefficient vector `b : ℕ → ℝ`
   that `ENNReal.ofReal (s_T (log M - c_T) (E_high - (16 U / A_c) E_low)) ≤ sourceLevyEnergy (criticalTruncatedSource V (S_low ∪ S_high) b)`
   for all `V ≥ criticalTwoBandTruncationThreshold`.

3. **Unconditional Cross-Window Prime Bounds and Complete Energy Lower Bounds
   (`abs_criticalTruncatedPrimeEnergy_le_of_low_and_window`,
   `abs_criticalTruncatedPrimeEnergy_le_of_lowWindow_lacunary`,
   `compactFullWeilEnergy_criticalTruncatedTest_ge_of_low_and_window`,
   `compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary`):**
   - **Low-Scale Modes + High-Scale Window (`[M, LM]`):**
     Via scaled bilinear polarization `b^± = α b_low ± α⁻¹ b_high` with `α = √(3 + log(LM))` on
     `ScaleWindow (S_low ∪ S_high) 1 (LM)`, the cross-window prime coupling is bounded by
     `C_TW (3 + log(LM))² E_low + C_TW E_high` for every `b : ℕ → ℝ`, increasing the high-window
     prime coefficient from `C_TW (3 + log L)` to `C_TW (4 + log L)` with no lacunary gap required
     between `S_low` and `S_high`.
   - **Low-Scale Window (`[1, L_low]`) + Arbitrary-Depth Lacunary Block Family (`[M_0, M_0^{8^{J-1}}]`):**
     Decomposing `S_low` into dyadic slices `dyadicSlice S_low k` (`DyadicScaleBlock (dyadicSlice S_low k) (2^k)`)
     and summing the geometric decay `∑_k (2^k)^{-1/8} ≤ 13` against `IsLacunaryBlockFamily J M S` (`L_low^8 ≤ M 0`)
     bounds the cross-window coupling beyond any `δ`-polynomial width by the scale-free `O(1)` bound
     `650 K_CB E_low + 100 K_CB E_high` (so the total low-window prime coefficient is
     `C_TW (3 + log L_low) + 650 K_CB = O(log L_low) = O(A)`, with zero `O(L_low) = O(e^A)` loss)
     for every `b : ℕ → ℝ`, uniformly in `L_low`, `J`, and `V`.

4. **Unconditional Spatial Translation Invariance & Direct Grid-Tent / Smooth-Detector Transfer
   (`compactFullWeilEnergy_translate_eq`,
   `tendsto_compactFullWeilEnergy_gridTentPattern_criticalTruncatedTest`,
   `gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge`,
   `exists_lacunary_gridTentPattern_and_smoothDetector_pos`,
   `exists_polynomial_window_gridTentPattern_and_smoothDetector_pos`):**
   Every spatial translate `x ↦ g(x + τ)` preserves `compactFullWeilEnergy` and `fullZeroForm`
   identically, and for every compact doubly collared source `g = criticalTruncatedTest hVpos S b`
   (across polynomial windows, lacunary block families, and two-band low/high unions), its
   envelope-rescaled profile `G(x) = e^{-3x/2} g(x)` is Lipschitz so that the single-scale grid
   tent patterns `gridTentPattern G n (-(R+1)) M_n` and their smoothed `C_c²` detectors
   `smoothGridTentDetector G n (-(R+1)) M_n q` unconditionally converge to `compactFullWeilEnergy g`
   and inherit strict positivity across all five form realizations.
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
For every finite set `S : Finset ℕ` (including `0 ∈ S`), `∑_{n ∈ S} (1/(n+1))² ≤ π²/6`. -/
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
    exact zero_le
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
      simp only [Pi.add_apply, one_smul, g, g_low, S]
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
    have h1 := norm_add_le (paperFT (fun y => (g_low y : ℂ)) t)
      (paperFT (fun y => (gc_high y : ℂ)) t - paperFT (fun y => (h_high y : ℂ)) t)
    have h2 := norm_sub_le (paperFT (fun y => (gc_high y : ℂ)) t)
      (paperFT (fun y => (h_high y : ℂ)) t)
    have htr1 : ‖paperFT (fun y => (g_low y : ℂ)) t +
        (paperFT (fun y => (gc_high y : ℂ)) t - paperFT (fun y => (h_high y : ℂ)) t)‖ ≤
        u1 + (u2 + u3) := by linarith
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
    have hc_hi : IntegrableOn (fun t : ℝ => 2 * (2 * D ^ 2 / M * E_high) +
        4 * levySourceSpectralDensity h_high t) (Icc (-R) R) :=
      hc.add (hhi.integrableOn.const_mul 4)
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
        ∫ t in Icc (-R) R, ((2 * (2 * D ^ 2 / M * E_high) +
          4 * levySourceSpectralDensity h_high t) +
          4 * levySourceSpectralDensity g_low t) :=
      setIntegral_mono_on hmi.integrableOn (hc_hi.add (hli.integrableOn.const_mul 4))
        measurableSet_Icc fun t ht => (hsplit t).trans (by gcongr; exact hlowc t ht)
    have h2 : (∫ t in Icc (-R) R, ((2 * (2 * D ^ 2 / M * E_high) +
          4 * levySourceSpectralDensity h_high t) +
          4 * levySourceSpectralDensity g_low t)) ≤
        (2 * R) * (2 * (2 * D ^ 2 / M * E_high)) +
          4 * (2 * Real.pi * ∫ x, h_high x ^ 2) +
          4 * (2 * Real.pi * ∫ x, g_low x ^ 2) := by
      rw [integral_add hc_hi (hli.integrableOn.const_mul 4),
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
    have hA_ne : criticalCollarMassLower ≠ 0 := hA.ne'
    have hpen : A / 4 * (criticalLowModePenaltyRatio * E_low) = 4 * (U * E_low) := by
      dsimp only [A, U]
      unfold criticalLowModePenaltyRatio
      field_simp [hA_ne]
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

/-! ## Section 3: Unconditional Cross-Window Prime Channel Bounds and Complete Energy Lower Bounds -/

private theorem integrableOn_truncatedWeight_mul_phase (V : ℝ) (S S' : Finset ℕ)
    (b c : ℕ → ℝ) (r : ℕ) :
    IntegrableOn (fun v => criticalTruncatedWeight ((r : ℝ) / V) v *
      (realPhaseCombination S b v * realPhaseCombination S' c (r * v))) (Ioi 1) := by
  have hφ := integrableOn_criticalTruncatedWeight ((r : ℝ) / V)
  have hg : Continuous (fun v => realPhaseCombination S b v * realPhaseCombination S' c (r * v)) :=
    (continuous_realPhaseCombination _ _).mul
      ((continuous_realPhaseCombination _ _).comp (continuous_const.mul continuous_id))
  set C := (2 * ∑ n ∈ S, |b n|) * (2 * ∑ n ∈ S', |c n|)
  refine (hφ.norm.const_mul C).mono' (hφ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_mul]
  exact mul_le_mul (abs_realPhaseCombination_le_two_mul _ _ _)
    (abs_realPhaseCombination_le_two_mul _ _ _) (abs_nonneg _)
    (by have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n); positivity)

/-- Left disjoint-union additivity of `truncatedBlockCoupling`. -/
theorem truncatedBlockCoupling_union_left (V : ℝ) {S₁ S₂ : Finset ℕ} (hdisj : Disjoint S₁ S₂)
    (S₃ : Finset ℕ) (b : ℕ → ℝ) :
    truncatedBlockCoupling V (S₁ ∪ S₂) S₃ b =
      truncatedBlockCoupling V S₁ S₃ b + truncatedBlockCoupling V S₂ S₃ b := by
  unfold truncatedBlockCoupling
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_add, ← integral_add (integrableOn_truncatedWeight_mul_phase V S₁ S₃ b b r)
    (integrableOn_truncatedWeight_mul_phase V S₂ S₃ b b r)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [realPhaseCombination_union hdisj]
  ring

/-- Right disjoint-union additivity of `truncatedBlockCoupling`. -/
theorem truncatedBlockCoupling_union_right (V : ℝ) (S₁ : Finset ℕ) {S₂ S₃ : Finset ℕ}
    (hdisj : Disjoint S₂ S₃) (b : ℕ → ℝ) :
    truncatedBlockCoupling V S₁ (S₂ ∪ S₃) b =
      truncatedBlockCoupling V S₁ S₂ b + truncatedBlockCoupling V S₁ S₃ b := by
  unfold truncatedBlockCoupling
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_add, ← integral_add (integrableOn_truncatedWeight_mul_phase V S₁ S₂ b b r)
    (integrableOn_truncatedWeight_mul_phase V S₁ S₃ b b r)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [realPhaseCombination_union hdisj]
  ring

/-- Expansion of `criticalTruncatedPrimeEnergy` over a disjoint union `S₁ ∪ S₂`. -/
theorem criticalTruncatedPrimeEnergy_union {V : ℝ} (hV : 0 < V) {S₁ S₂ : Finset ℕ}
    (hdisj : Disjoint S₁ S₂) (b : ℕ → ℝ) :
    criticalTruncatedPrimeEnergy V (S₁ ∪ S₂) b =
      criticalTruncatedPrimeEnergy V S₁ b + criticalTruncatedPrimeEnergy V S₂ b +
        truncatedBlockCoupling V S₁ S₂ b + truncatedBlockCoupling V S₂ S₁ b := by
  rw [← truncatedBlockCoupling_self hV (S₁ ∪ S₂) b,
    truncatedBlockCoupling_union_left V hdisj,
    truncatedBlockCoupling_union_right V S₁ hdisj,
    truncatedBlockCoupling_union_right V S₂ hdisj,
    truncatedBlockCoupling_self hV S₁ b,
    truncatedBlockCoupling_self hV S₂ b]
  ring

/-- Bilinear scaling of `truncatedBlockCoupling` when `c` scales `b` on `S₁` and `S₂`. -/
theorem truncatedBlockCoupling_scale (V : ℝ) (S₁ S₂ : Finset ℕ) (b c : ℕ → ℝ) (α₁ α₂ : ℝ)
    (h₁ : ∀ n ∈ S₁, c n = α₁ * b n) (h₂ : ∀ n ∈ S₂, c n = α₂ * b n) :
    truncatedBlockCoupling V S₁ S₂ c = α₁ * α₂ * truncatedBlockCoupling V S₁ S₂ b := by
  have hp1 (v : ℝ) : realPhaseCombination S₁ c v = α₁ * realPhaseCombination S₁ b v := by
    unfold realPhaseCombination
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => by rw [h₁ n hn]; ring
  have hp2 (v : ℝ) : realPhaseCombination S₂ c v = α₂ * realPhaseCombination S₂ b v := by
    unfold realPhaseCombination
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => by rw [h₂ n hn]; ring
  unfold truncatedBlockCoupling
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hint : (∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
      (realPhaseCombination S₁ c v * realPhaseCombination S₂ c (r * v))) =
      (α₁ * α₂) * ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
        (realPhaseCombination S₁ b v * realPhaseCombination S₂ b (r * v)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [hp1 v, hp2 (r * v)]
    ring
  rw [hint]
  ring

/-- Rescaled coefficient vector `b^±(n) = α b_n` on `S_low` and `± α⁻¹ b_n` outside `S_low`. -/
def scaledSplitCoeffs (S_low : Finset ℕ) (b : ℕ → ℝ) (α s : ℝ) (n : ℕ) : ℝ :=
  if n ∈ S_low then α * b n else s * α⁻¹ * b n

theorem sum_sq_scaledSplitCoeffs {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high)
    (b : ℕ → ℝ) (α s : ℝ) (hs : s ^ 2 = 1) :
    ∑ n ∈ S_low ∪ S_high, (scaledSplitCoeffs S_low b α s n) ^ 2 =
      α ^ 2 * (∑ n ∈ S_low, b n ^ 2) + (α⁻¹) ^ 2 * ∑ n ∈ S_high, b n ^ 2 := by
  rw [Finset.sum_union hdisj]
  have h1 : ∑ n ∈ S_low, (scaledSplitCoeffs S_low b α s n) ^ 2 =
      α ^ 2 * ∑ n ∈ S_low, b n ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [scaledSplitCoeffs, if_pos hn]
    ring
  have h2 : ∑ n ∈ S_high, (scaledSplitCoeffs S_low b α s n) ^ 2 =
      (α⁻¹) ^ 2 * ∑ n ∈ S_high, b n ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnot : n ∉ S_low := Finset.disjoint_right.mp hdisj hn
    simp only [scaledSplitCoeffs, if_neg hnot]
    calc (s * α⁻¹ * b n) ^ 2 = s ^ 2 * ((α⁻¹) ^ 2 * b n ^ 2) := by ring
      _ = (α⁻¹) ^ 2 * b n ^ 2 := by rw [hs, one_mul]
  rw [h1, h2]

/-- **Scaled Bilinear Polarization Identity for the Cross-Window Prime Coupling.** -/
theorem truncatedBlockCoupling_add_symm_eq_polarization {V : ℝ} (hV : 0 < V)
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ) {α : ℝ} (hα : α ≠ 0) :
    truncatedBlockCoupling V S_low S_high b + truncatedBlockCoupling V S_high S_low b =
      (criticalTruncatedPrimeEnergy V (S_low ∪ S_high) (scaledSplitCoeffs S_low b α 1) -
        criticalTruncatedPrimeEnergy V (S_low ∪ S_high) (scaledSplitCoeffs S_low b α (-1))) / 2 := by
  set bp := scaledSplitCoeffs S_low b α 1
  set bm := scaledSplitCoeffs S_low b α (-1)
  have hlow_p : ∀ n ∈ S_low, bp n = α * b n := fun n hn => by simp [bp, scaledSplitCoeffs, hn]
  have hlow_m : ∀ n ∈ S_low, bm n = α * b n := fun n hn => by simp [bm, scaledSplitCoeffs, hn]
  have hhigh_p : ∀ n ∈ S_high, bp n = α⁻¹ * b n := fun n hn => by
    have hnot : n ∉ S_low := Finset.disjoint_right.mp hdisj hn
    simp [bp, scaledSplitCoeffs, hnot]
  have hhigh_m : ∀ n ∈ S_high, bm n = (-α⁻¹) * b n := fun n hn => by
    have hnot : n ∉ S_low := Finset.disjoint_right.mp hdisj hn
    simp [bm, scaledSplitCoeffs, hnot]
  rw [criticalTruncatedPrimeEnergy_union hV hdisj bp,
    criticalTruncatedPrimeEnergy_union hV hdisj bm,
    ← truncatedBlockCoupling_self hV S_low bp,
    ← truncatedBlockCoupling_self hV S_low bm,
    ← truncatedBlockCoupling_self hV S_high bp,
    ← truncatedBlockCoupling_self hV S_high bm,
    truncatedBlockCoupling_scale V S_low S_low b bp α α hlow_p hlow_p,
    truncatedBlockCoupling_scale V S_low S_low b bm α α hlow_m hlow_m,
    truncatedBlockCoupling_scale V S_high S_high b bp α⁻¹ α⁻¹ hhigh_p hhigh_p,
    truncatedBlockCoupling_scale V S_high S_high b bm (-α⁻¹) (-α⁻¹) hhigh_m hhigh_m,
    truncatedBlockCoupling_scale V S_low S_high b bp α α⁻¹ hlow_p hhigh_p,
    truncatedBlockCoupling_scale V S_low S_high b bm α (-α⁻¹) hlow_m hhigh_m,
    truncatedBlockCoupling_scale V S_high S_low b bp α⁻¹ α hhigh_p hlow_p,
    truncatedBlockCoupling_scale V S_high S_low b bm (-α⁻¹) α hhigh_m hlow_m]
  have h1 : α * α⁻¹ = 1 := mul_inv_cancel₀ hα
  have h2 : α⁻¹ * α = 1 := inv_mul_cancel₀ hα
  have h3 : α * -α⁻¹ = -1 := by rw [mul_neg, h1]
  have h4 : -α⁻¹ * α = -1 := by rw [neg_mul, h2]
  have h5 : -α⁻¹ * -α⁻¹ = α⁻¹ * α⁻¹ := neg_mul_neg _ _
  rw [h1, h2, h3, h4, h5]
  ring

/-- **Unconditional Prime Channel Bound for Low-Scale Modes + High-Scale Window `[M, LM]`.**
For every `V > 0`, every disjoint pair `S_low, S_high ⊂ ℕ` with `∀ n ∈ S_low, n + 1 ≤ L * M` and
`ScaleWindow S_high M L` (`M, L ≥ 1`), and every `b : ℕ → ℝ`, the prime channel on `S_low ∪ S_high`
is bounded by `2 C_TW (3 + log(LM))² E_low + C_TW (4 + log L) E_high` with no lacunary gap hypothesis. -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_low_and_window {V : ℝ} (hV : 0 < V)
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high)
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hS_low : ∀ n ∈ S_low, n + 1 ≤ L * M) (hS_high : ScaleWindow S_high M L) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V (S_low ∪ S_high) b| ≤
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log ((L * M : ℕ) : ℝ)) ^ 2 *
        (∑ n ∈ S_low, b n ^ 2) +
      criticalTruncatedWindowPrimeSlope * (4 + Real.log L) * ∑ n ∈ S_high, b n ^ 2 := by
  set W := criticalTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := criticalTruncatedWindowPrimeSlope_nonneg
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_low : 0 ≤ E_low := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_high : 0 ≤ E_high := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hLM : 1 ≤ L * M := Nat.mul_pos hL hM
  have hLM_real : (1 : ℝ) ≤ ((L * M : ℕ) : ℝ) := by exact_mod_cast hLM
  set B := 3 + Real.log ((L * M : ℕ) : ℝ)
  have hB1 : 1 ≤ B := by
    have := Real.log_nonneg hLM_real
    unfold B; linarith
  have hBpos : 0 < B := by linarith
  set α := Real.sqrt B
  have hα_pos : 0 < α := Real.sqrt_pos.mpr hBpos
  have hα_sq : α ^ 2 = B := Real.sq_sqrt hBpos.le
  have hα_inv_sq : B * (α⁻¹) ^ 2 = 1 := by
    rw [inv_pow, hα_sq, mul_inv_cancel₀ hBpos.ne']
  have hwin_low : ScaleWindow S_low 1 (L * M) := fun n hn =>
    ⟨by omega, by have := hS_low n hn; omega⟩
  have hwin_union : ScaleWindow (S_low ∪ S_high) 1 (L * M) := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact hwin_low n hn
    · exact ⟨by omega, by have := (hS_high n hn).2; omega⟩
  have hP_low := abs_criticalTruncatedPrimeEnergy_le_of_window hV le_rfl hLM hwin_low b
  have hP_high := abs_criticalTruncatedPrimeEnergy_le_of_window hV hM hL hS_high b
  have hP_plus := abs_criticalTruncatedPrimeEnergy_le_of_window hV le_rfl hLM hwin_union
    (scaledSplitCoeffs S_low b α 1)
  have hP_minus := abs_criticalTruncatedPrimeEnergy_le_of_window hV le_rfl hLM hwin_union
    (scaledSplitCoeffs S_low b α (-1))
  rw [sum_sq_scaledSplitCoeffs hdisj b α 1 (by norm_num)] at hP_plus
  rw [sum_sq_scaledSplitCoeffs hdisj b α (-1) (by norm_num)] at hP_minus
  have hcross_eq := truncatedBlockCoupling_add_symm_eq_polarization hV hdisj b hα_pos.ne'
  have hcross_le : |truncatedBlockCoupling V S_low S_high b +
      truncatedBlockCoupling V S_high S_low b| ≤ W * B ^ 2 * E_low + W * E_high := by
    rw [hcross_eq, abs_div, abs_two]
    have h1 := (abs_sub _ _).trans (add_le_add hP_plus hP_minus)
    have h2 : W * B * (α ^ 2 * E_low + (α⁻¹) ^ 2 * E_high) = W * B ^ 2 * E_low + W * E_high := by
      calc W * B * (α ^ 2 * E_low + (α⁻¹) ^ 2 * E_high)
          = W * B * α ^ 2 * E_low + W * (B * (α⁻¹) ^ 2) * E_high := by ring
        _ = W * B ^ 2 * E_low + W * E_high := by rw [hα_sq, hα_inv_sq]; ring
    linarith
  have hB_le_sq : W * B * E_low ≤ W * B ^ 2 * E_low := by
    have : B ≤ B ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hW) hE_low
  rw [criticalTruncatedPrimeEnergy_union hV hdisj b, add_assoc (criticalTruncatedPrimeEnergy V S_low b +
    criticalTruncatedPrimeEnergy V S_high b)]
  have htri1 := abs_add_le (criticalTruncatedPrimeEnergy V S_low b +
    criticalTruncatedPrimeEnergy V S_high b)
    (truncatedBlockCoupling V S_low S_high b + truncatedBlockCoupling V S_high S_low b)
  have htri2 := abs_add_le (criticalTruncatedPrimeEnergy V S_low b)
    (criticalTruncatedPrimeEnergy V S_high b)
  linarith [hP_low, hP_high, hcross_le, htri1, htri2]

/-- Expansion of `truncatedBlockCoupling` over singletons on the left. -/
theorem truncatedBlockCoupling_eq_sum_singletons_left (V : ℝ) (S S' : Finset ℕ) (b : ℕ → ℝ) :
    truncatedBlockCoupling V S S' b = ∑ n ∈ S, truncatedBlockCoupling V {n} S' b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    unfold truncatedBlockCoupling realPhaseCombination
    simp
  | @insert a s ha ih =>
    have hd : Disjoint ({a} : Finset ℕ) s := Finset.disjoint_singleton_left.mpr ha
    rw [Finset.sum_insert ha, ← Finset.singleton_union, truncatedBlockCoupling_union_left V hd, ih]

/-- Expansion of `truncatedBlockCoupling` over singletons on the right. -/
theorem truncatedBlockCoupling_eq_sum_singletons_right (V : ℝ) (S S' : Finset ℕ) (b : ℕ → ℝ) :
    truncatedBlockCoupling V S S' b = ∑ n ∈ S', truncatedBlockCoupling V S {n} b := by
  classical
  induction S' using Finset.induction_on with
  | empty =>
    unfold truncatedBlockCoupling realPhaseCombination
    simp
  | @insert a s ha ih =>
    have hd : Disjoint ({a} : Finset ℕ) s := Finset.disjoint_singleton_left.mpr ha
    rw [Finset.sum_insert ha, ← Finset.singleton_union,
      truncatedBlockCoupling_union_right V S hd, ih]

/-- Expansion of `truncatedBlockCoupling` over a disjoint `biUnion` on the right. -/
theorem truncatedBlockCoupling_biUnion_right (V : ℝ) (S₀ : Finset ℕ) {I : Finset ℕ}
    {S : ℕ → Finset ℕ} (hd : (I : Set ℕ).PairwiseDisjoint S) (b : ℕ → ℝ) :
    truncatedBlockCoupling V S₀ (I.biUnion S) b =
      ∑ i ∈ I, truncatedBlockCoupling V S₀ (S i) b := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    unfold truncatedBlockCoupling realPhaseCombination
    simp
  | @insert a s ha ih =>
    have hds : (s : Set ℕ).PairwiseDisjoint S :=
      hd.subset (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have hdisj : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hd (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    rw [Finset.biUnion_insert, truncatedBlockCoupling_union_right V S₀ hdisj, ih hds,
      Finset.sum_insert ha]

/-- Expansion of `truncatedBlockCoupling` over a disjoint `biUnion` on the left. -/
theorem truncatedBlockCoupling_biUnion_left (V : ℝ) {I : Finset ℕ}
    {S : ℕ → Finset ℕ} (hd : (I : Set ℕ).PairwiseDisjoint S) (S₀ : Finset ℕ) (b : ℕ → ℝ) :
    truncatedBlockCoupling V (I.biUnion S) S₀ b =
      ∑ i ∈ I, truncatedBlockCoupling V (S i) S₀ b := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    unfold truncatedBlockCoupling realPhaseCombination
    simp
  | @insert a s ha ih =>
    have hds : (s : Set ℕ).PairwiseDisjoint S :=
      hd.subset (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have hdisj : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hd (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    rw [Finset.biUnion_insert, truncatedBlockCoupling_union_left V hdisj, ih hds,
      Finset.sum_insert ha]

/-- Every singleton `{n}` is a dyadic scale block at `n + 1`. -/
theorem dyadicScaleBlock_singleton (n : ℕ) : DyadicScaleBlock ({n} : Finset ℕ) (n + 1) := by
  intro k hk
  rw [Finset.mem_singleton.mp hk]
  omega

/-- Dyadic slice `S.filter (fun n => 2^k ≤ n + 1 ∧ n + 1 < 2^(k + 1))` of a support `S` at scale `2^k`. -/
def dyadicSlice (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter (fun n => 2 ^ k ≤ n + 1 ∧ n + 1 < 2 ^ (k + 1))

theorem dyadicScaleBlock_dyadicSlice (S : Finset ℕ) (k : ℕ) :
    DyadicScaleBlock (dyadicSlice S k) (2 ^ k) := by
  intro n hn
  have h := (Finset.mem_filter.mp hn).2
  refine ⟨h.1, ?_⟩
  calc n + 1 ≤ 2 ^ (k + 1) := h.2.le
    _ = 2 * 2 ^ k := by ring

theorem pairwiseDisjoint_dyadicSlice (S : Finset ℕ) (I : Set ℕ) :
    I.PairwiseDisjoint (dyadicSlice S) := by
  intro k₁ _ k₂ _ hne
  have key : ∀ a b, a < b → Disjoint (dyadicSlice S a) (dyadicSlice S b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro n hna hnb
    have ha := (Finset.mem_filter.mp hna).2.2
    have hb := (Finset.mem_filter.mp hnb).2.1
    have hpow : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key k₁ k₂ hlt
  · exact (key k₂ k₁ hlt).symm

/-- Dyadic exponents `k ≤ L_low` with `2^k ≤ L_low` covering a low-scale window `ScaleWindow S_low 1 L_low`. -/
def lowDyadicIndices (L_low : ℕ) : Finset ℕ :=
  (Finset.range (L_low + 1)).filter (fun k => 2 ^ k ≤ L_low)

theorem biUnion_dyadicSlice_lowDyadicIndices {S_low : Finset ℕ} {L_low : ℕ}
    (hlow : ScaleWindow S_low 1 L_low) :
    (lowDyadicIndices L_low).biUnion (dyadicSlice S_low) = S_low := by
  ext n
  simp only [Finset.mem_biUnion, lowDyadicIndices, dyadicSlice, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨_, _, hn, _⟩
    exact hn
  · intro hn
    have hwin := hlow n hn
    set k := Nat.log 2 (n + 1)
    have hk_le : 2 ^ k ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have hk_lt : n + 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have hk_pow : 2 ^ k ≤ L_low := by omega
    have hk_self : k < 2 ^ k := Nat.lt_two_pow_self
    refine ⟨k, ⟨by omega, hk_pow⟩, hn, hk_le, hk_lt⟩

/-- Geometric sum bound `∑_{k ∈ lowDyadicIndices L_low} ((2^k)^{-1/16})^2 ≤ 13`, independent of `L_low`. -/
theorem sum_lowDyadicIndices_weight_sq_le (L_low : ℕ) :
    ∑ k ∈ lowDyadicIndices L_low, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 ≤ 13 := by
  have hterm : ∀ k : ℕ, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 ≤ (12 / 13 : ℝ) ^ k := by
    intro k
    have h13 : (13 / 12 : ℝ) ≤ (2 : ℝ) ^ (1 / 8 : ℝ) := by
      have hpow : ((13 / 12 : ℝ) ^ (8 : ℕ)) ≤ 2 := by norm_num
      have h1 : (13 / 12 : ℝ) = ((13 / 12 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
        rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    have hinv : ((2 : ℝ) ^ (1 / 8 : ℝ))⁻¹ ≤ 12 / 13 := by
      have := inv_anti₀ (by positivity : (0 : ℝ) < 13 / 12) h13
      linarith
    have heq : ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 = (((2 : ℝ) ^ (1 / 8 : ℝ))⁻¹) ^ k := by
      rw [inv_pow, inv_pow, Nat.cast_pow, Nat.cast_ofNat,
        ← Real.rpow_natCast (((2 : ℝ) ^ k) ^ (1 / 16 : ℝ)),
        ← Real.rpow_mul (by positivity), show (1 / 16 : ℝ) * (2 : ℕ) = 1 / 8 by norm_num,
        ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by positivity),
        mul_comm (k : ℝ) (1 / 8 : ℝ), Real.rpow_mul (by positivity), Real.rpow_natCast]
    rw [heq]
    exact pow_le_pow_left₀ (by positivity) hinv k
  calc ∑ k ∈ lowDyadicIndices L_low, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2
      ≤ ∑ k ∈ Finset.range (L_low + 1), ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
    _ ≤ ∑ k ∈ Finset.range (L_low + 1), (12 / 13 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ((12 / 13 : ℝ) ^ (L_low + 1) - 1) / (12 / 13 - 1) :=
        geom_sum_eq (by norm_num) (L_low + 1)
    _ ≤ 13 := by
        have hpos : 0 ≤ (12 / 13 : ℝ) ^ (L_low + 1) := by positivity
        have hsub : ((12 / 13 : ℝ) ^ (L_low + 1) - 1) / (12 / 13 - 1) =
            13 * (1 - (12 / 13 : ℝ) ^ (L_low + 1)) := by ring
        linarith

/-- If `ScaleWindow S_low 1 L_low` and `IsLacunaryBlockFamily J M S` with `L_low^8 ≤ M 0`, then
`S_low` and `(Finset.range J).biUnion S` are automatically disjoint. -/
theorem disjoint_lowWindow_lacunary {S_low : Finset ℕ} {L_low J : ℕ} {M : ℕ → ℕ}
    {S : ℕ → Finset ℕ} (hlow : ScaleWindow S_low 1 L_low)
    (hlac : IsLacunaryBlockFamily J M S) (hsep : L_low ^ 8 ≤ M 0) :
    Disjoint S_low ((Finset.range J).biUnion S) := by
  rw [Finset.disjoint_left]
  intro n hn_low hn_high
  have h1 : n + 1 ≤ L_low := by have := (hlow n hn_low).2; omega
  have h2 : M 0 ≤ n + 1 := hlac.lower hn_high
  have h3 : 3 ≤ M 0 := hlac.1
  rcases le_or_gt L_low 1 with hL1 | hL2
  · omega
  · have hpow : L_low < L_low ^ 8 := by
      calc L_low = L_low ^ 1 := (pow_one _).symm
        _ < L_low ^ 8 := Nat.pow_lt_pow_right hL2 (by norm_num)
    omega

/-- **Unconditional Cross-Window Prime Bound for Low-Scale Window `[1, L_low]` + High-Scale
Lacunary Block Family Spanning Beyond `δ`-Polynomial Width.**
For every `V > 0`, every low-scale window `ScaleWindow S_low 1 L_low` (`L_low ≥ 1`), every
lacunary block family `IsLacunaryBlockFamily J M S` with `L_low^8 ≤ M 0`, and every `b : ℕ → ℝ`,
decomposing `S_low` into dyadic slices `dyadicSlice S_low k` (`DyadicScaleBlock (dyadicSlice S_low k) (2^k)`)
and summing `∑_k (2^k)^{-1/8} ≤ 13` bounds the prime channel on `S_low ∪ ⋃_{i < J} S_i` by
`(C_TW (3 + log L_low) + 650 K_CB) E_low + (lacunaryPrimeConstant + 100 K_CB) E_high`
(with scale-free `O(1)` cross-window coupling and total low-window factor `O(log L_low) = O(A)`),
uniformly in `L_low`, `V`, and the number of blocks `J`. -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_lowWindow_lacunary {V : ℝ} (hV : 0 < V)
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V (S_low ∪ (Finset.range J).biUnion S) b| ≤
      (criticalTruncatedWindowPrimeSlope * (3 + Real.log L_low) +
        650 * truncatedCrossBlockConstant) * (∑ n ∈ S_low, b n ^ 2) +
      (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant) *
        ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 := by
  set I := Finset.range J
  set J_low := lowDyadicIndices L_low
  set S_high := I.biUnion S
  set K := truncatedCrossBlockConstant
  have hK : 0 ≤ K := truncatedCrossBlockConstant_nonneg
  set X_low : ℕ → ℝ := fun k => ∑ n ∈ dyadicSlice S_low k, b n ^ 2
  set s_low : ℕ → ℝ := fun k => Real.sqrt (X_low k)
  set w_low : ℕ → ℝ := fun k => (((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹
  set X : ℕ → ℝ := fun i => ∑ n ∈ S i, b n ^ 2
  set s : ℕ → ℝ := fun i => Real.sqrt (X i)
  set w : ℕ → ℝ := fun i => ((M i : ℝ) ^ (1 / 16 : ℝ))⁻¹
  have hX_low (k : ℕ) : 0 ≤ X_low k := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw_low (k : ℕ) : 0 ≤ w_low k := by simp only [w_low]; positivity
  have hX (i : ℕ) : 0 ≤ X i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw (i : ℕ) : 0 ≤ w i := by simp only [w]; positivity
  have hd_low := pairwiseDisjoint_dyadicSlice S_low (J_low : Set ℕ)
  have hd := hlac.pairwiseDisjoint
  have hbi_low := biUnion_dyadicSlice_lowDyadicIndices hlow
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_low_eq : E_low = ∑ k ∈ J_low, X_low k := by
    calc E_low = ∑ n ∈ J_low.biUnion (dyadicSlice S_low), b n ^ 2 := by
          dsimp only [E_low, J_low]; rw [hbi_low]
      _ = ∑ k ∈ J_low, X_low k := Finset.sum_biUnion hd_low
  have hE_high_eq : E_high = ∑ i ∈ I, X i := Finset.sum_biUnion hd
  have hP_low := abs_criticalTruncatedPrimeEnergy_le_of_window hV le_rfl hL_low hlow b
  have hP_high := abs_criticalTruncatedPrimeEnergy_le_of_lacunary hV hlac b
  have hpair : ∀ k ∈ J_low, ∀ i ∈ I,
      |truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b| ≤
        50 * K * (w_low k * s_low k) * (w i * s i) ∧
      |truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b| ≤
        50 * K * (w_low k * s_low k) * (w i * s i) := by
    intro k hk i hi
    have hi_lt := Finset.mem_range.mp hi
    have hk_le : 2 ^ k ≤ L_low := (Finset.mem_filter.mp hk).2
    have hM0_le : M 0 ≤ M i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact le_rfl
      · exact hlac.le_of_lt hpos hi_lt
    have hpow : (2 ^ k) ^ 8 ≤ M i :=
      (Nat.pow_le_pow_left hk_le 8).trans (hsep.trans hM0_le)
    have h2k_1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hMi_1 : 1 ≤ M i := by have := hlac.three_le i hi_lt; omega
    have h1 := abs_truncatedBlockCoupling_le_of_pow_le hV (dyadicScaleBlock_dyadicSlice S_low k)
      (hlac.2.2 i hi_lt) h2k_1 hMi_1 (Or.inl hpow) b
    have h2 := abs_truncatedBlockCoupling_le_of_pow_le hV (hlac.2.2 i hi_lt)
      (dyadicScaleBlock_dyadicSlice S_low k) hMi_1 h2k_1 (Or.inr hpow) b
    refine ⟨h1.trans (le_of_eq ?_), h2.trans (le_of_eq ?_)⟩
    · simp only [w_low, s_low, X_low, w, s, X, K]; ring
    · simp only [w_low, s_low, X_low, w, s, X, K]; ring
  set A_low := ∑ k ∈ J_low, w_low k * s_low k
  set B_high := ∑ i ∈ I, w i * s i
  have hbi1 (k : ℕ) : truncatedBlockCoupling V (dyadicSlice S_low k) S_high b =
      ∑ i ∈ I, truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b :=
    truncatedBlockCoupling_biUnion_right V (dyadicSlice S_low k) hd b
  have hbi2 (k : ℕ) : truncatedBlockCoupling V S_high (dyadicSlice S_low k) b =
      ∑ i ∈ I, truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b :=
    truncatedBlockCoupling_biUnion_left V hd (dyadicSlice S_low k) b
  have hcross1 : |truncatedBlockCoupling V S_low S_high b| ≤ 50 * K * A_low * B_high := by
    rw [← hbi_low, truncatedBlockCoupling_biUnion_left V hd_low S_high b]
    simp_rw [hbi1]
    calc |∑ k ∈ J_low, ∑ i ∈ I, truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b|
        ≤ ∑ k ∈ J_low, ∑ i ∈ I, |truncatedBlockCoupling V (dyadicSlice S_low k) (S i) b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ J_low, ∑ i ∈ I, 50 * K * (w_low k * s_low k) * (w i * s i) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => (hpair k hk i hi).1
      _ = 50 * K * A_low * B_high := by
          dsimp only [A_low, B_high]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcross2 : |truncatedBlockCoupling V S_high S_low b| ≤ 50 * K * A_low * B_high := by
    rw [← hbi_low, truncatedBlockCoupling_biUnion_right V S_high hd_low b]
    simp_rw [hbi2]
    calc |∑ k ∈ J_low, ∑ i ∈ I, truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b|
        ≤ ∑ k ∈ J_low, ∑ i ∈ I, |truncatedBlockCoupling V (S i) (dyadicSlice S_low k) b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ J_low, ∑ i ∈ I, 50 * K * (w_low k * s_low k) * (w i * s i) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => (hpair k hk i hi).2
      _ = 50 * K * A_low * B_high := by
          dsimp only [A_low, B_high]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hA_sq : A_low ^ 2 ≤ 13 * E_low := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq J_low w_low s_low
    have hs2 : ∑ k ∈ J_low, s_low k ^ 2 = E_low := by
      rw [hE_low_eq]
      exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hX_low k)
    rw [hs2] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (sum_lowDyadicIndices_weight_sq_le L_low)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hB_sq : B_high ^ 2 ≤ 2 * E_high := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq I w s
    have hs2 : ∑ i ∈ I, s i ^ 2 = E_high := by
      rw [hE_high_eq]
      exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hX i)
    rw [hs2] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right hlac.sum_weight_sq_le
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have h2AB : 100 * K * A_low * B_high ≤ 50 * K * (A_low ^ 2 + B_high ^ 2) := by
    nlinarith [sq_nonneg (A_low - B_high)]
  rw [criticalTruncatedPrimeEnergy_union hV hdisj b]
  have htri : |criticalTruncatedPrimeEnergy V S_low b + criticalTruncatedPrimeEnergy V S_high b +
      truncatedBlockCoupling V S_low S_high b + truncatedBlockCoupling V S_high S_low b| ≤
      |criticalTruncatedPrimeEnergy V S_low b| + |criticalTruncatedPrimeEnergy V S_high b| +
        |truncatedBlockCoupling V S_low S_high b| + |truncatedBlockCoupling V S_high S_low b| := by
    linarith [abs_add_le (criticalTruncatedPrimeEnergy V S_low b +
        criticalTruncatedPrimeEnergy V S_high b + truncatedBlockCoupling V S_low S_high b)
        (truncatedBlockCoupling V S_high S_low b),
      abs_add_le (criticalTruncatedPrimeEnergy V S_low b +
        criticalTruncatedPrimeEnergy V S_high b) (truncatedBlockCoupling V S_low S_high b),
      abs_add_le (criticalTruncatedPrimeEnergy V S_low b) (criticalTruncatedPrimeEnergy V S_high b)]
  nlinarith

/-- **Unconditional Real Weil Energy Lower Bound on Low-Mode + High-Scale Window `[M, LM]`.**
Holds for every coefficient vector `b : ℕ → ℝ` without any hypothesis on `E_low` vs `E_high`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest_ge_of_low_and_window
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    {M L : ℕ} (hM : 2 ≤ M) (hM_log : criticalTruncatedArchLogOffset ≤ Real.log M)
    (hL : 1 ≤ L) (hS_low : ∀ n ∈ S_low, n + 1 ≤ L * M) (hS_high : ScaleWindow S_high M L)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTwoBandTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant -
        2 * criticalTruncatedWindowPrimeSlope * (4 + Real.log L)) *
      (∑ n ∈ S_high, b n ^ 2) -
    (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
        criticalLowModePenaltyRatio +
        criticalAllScaleGammaPolarConstant +
        4 * criticalTruncatedWindowPrimeSlope * (3 + Real.log ((L * M : ℕ) : ℝ)) ^ 2) *
      (∑ n ∈ S_low, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ S_high) b) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set S := S_low ∪ S_high
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_union : ∑ n ∈ S, b n ^ 2 = E_low + E_high := Finset.sum_union hdisj
  set X := criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
    (E_high - criticalLowModePenaltyRatio * E_low)
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split hdisj b hM hM_log
      (fun n hn => (hS_high n hn).1) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hgp := neg_le_criticalTruncatedGammaPolar_all_scales S b hV1
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_low_and_window hVpos hdisj
    (by omega) hL hS_low hS_high b)).2
  rw [hE_union] at hgp
  set Y := EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
    2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
    2 * criticalTruncatedPrimeEnergy V S b
  have htot_er : ((X + Y : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V S b := by
    unfold criticalTruncatedCompleteEnergy
    rw [EReal.coe_add]
    exact add_le_add hlev le_rfl
  rw [← compactFullWeilEnergy_criticalTruncatedTest hVpos] at htot_er
  have htot := EReal.coe_le_coe_iff.mp htot_er
  dsimp only [X, Y] at htot
  linarith

/-- **Unconditional Real Weil Energy Lower Bound on Low-Scale Window + High-Scale Lacunary Block Family.**
Holds for every coefficient vector `b : ℕ → ℝ` and every block count `J`, with low-window prime
penalty `2 * (C_TW (3 + log L_low) + 650 K_CB) = O(log L_low) = O(A)` (zero `O(L_low) = O(e^A)` loss). -/
theorem compactFullWeilEnergy_criticalTruncatedTest_ge_of_lowWindow_lacunary
    {S_low : Finset ℕ} {L_low J : ℕ} (hL_low : 1 ≤ L_low) (hlow : ScaleWindow S_low 1 L_low)
    {M : ℕ → ℕ} {S : ℕ → Finset ℕ} (hlac : IsLacunaryBlockFamily J M S)
    (hsep : L_low ^ 8 ≤ M 0) (hM_log : criticalTruncatedArchLogOffset ≤ Real.log (M 0))
    (b : ℕ → ℝ) {V : ℝ} (hVpos : 0 < V) (hV : criticalTwoBandTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        criticalAllScaleGammaPolarConstant -
        2 * (lacunaryPrimeConstant + 100 * truncatedCrossBlockConstant)) *
      (∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) -
    (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) *
        criticalLowModePenaltyRatio +
        criticalAllScaleGammaPolarConstant +
        2 * (criticalTruncatedWindowPrimeSlope * (3 + Real.log L_low) +
          650 * truncatedCrossBlockConstant)) *
      (∑ n ∈ S_low, b n ^ 2) ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos (S_low ∪ (Finset.range J).biUnion S) b) := by
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hM2 : 2 ≤ M 0 := by have := hlac.1; omega
  have hdisj := disjoint_lowWindow_lacunary hlow hlac hsep
  set S_high := (Finset.range J).biUnion S
  set T := S_low ∪ S_high
  set E_low := ∑ n ∈ S_low, b n ^ 2
  set E_high := ∑ n ∈ S_high, b n ^ 2
  have hE_union : ∑ n ∈ T, b n ^ 2 = E_low + E_high := Finset.sum_union hdisj
  set X := criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) *
    (E_high - criticalLowModePenaltyRatio * E_low)
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V T b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy_of_low_high_split hdisj b hM2 hM_log
      (fun n hn => hlac.lower hn) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hgp := neg_le_criticalTruncatedGammaPolar_all_scales T b hV1
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_lowWindow_lacunary hVpos
    hL_low hlow hlac hsep b)).2
  rw [hE_union] at hgp
  set Y := EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V T b) 0 +
    2 * (criticalTruncatedPolarReadout V T b * criticalTruncatedPolarEndpoint V T b) -
    2 * criticalTruncatedPrimeEnergy V T b
  have htot_er : ((X + Y : ℝ) : EReal) ≤ criticalTruncatedCompleteEnergy V T b := by
    unfold criticalTruncatedCompleteEnergy
    rw [EReal.coe_add]
    exact add_le_add hlev le_rfl
  rw [← compactFullWeilEnergy_criticalTruncatedTest hVpos] at htot_er
  have htot := EReal.coe_le_coe_iff.mp htot_er
  dsimp only [X, Y] at htot
  linarith

/-! ## Section 4: Unconditional Spatial Translation Invariance & Direct Grid-Tent / Smooth-Detector Transfer -/

/-- Spatial translation `x ↦ g(x + τ)` of a compactly supported continuous real source `g ∈ C_c(ℝ, ℝ)`. -/
def translatedCompactSource (g : C_c(ℝ, ℝ)) (τ : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun x => g (x + τ), g.continuous.comp (continuous_id.add continuous_const)⟩,
    HasCompactSupport.intro (g.hasCompactSupport.image (continuous_id.sub continuous_const))
      fun x hx => by
        by_contra hne
        exact hx ⟨x + τ, subset_tsupport g hne, add_sub_cancel_right x τ⟩⟩

@[simp] theorem translatedCompactSource_apply (g : C_c(ℝ, ℝ)) (τ x : ℝ) :
    translatedCompactSource g τ x = g (x + τ) := rfl

/-- **Exact Spatial Translation Invariance of `EF.weilTest`.** -/
theorem weilTest_translatedCompactSource_eq (g : C_c(ℝ, ℝ)) (τ : ℝ) :
    EF.weilTest (fun x => (translatedCompactSource g τ x : ℂ))
      (fun x => (translatedCompactSource g τ x : ℂ)) =
    EF.weilTest (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) := by
  ext x
  simp only [RHTower.weilTest_apply, translatedCompactSource_apply]
  have hshift : (fun t : ℝ => (g (t + τ) : ℂ) * (starRingEnd ℂ) (g (t - x + τ) : ℂ)) =
      fun t : ℝ => (fun y : ℝ => (g y : ℂ) * (starRingEnd ℂ) (g (y - x) : ℂ)) (t + τ) := by
    funext t
    dsimp only
    rw [show t - x + τ = t + τ - x by ring]
  rw [hshift]
  exact integral_add_right_eq_self
    (fun y : ℝ => (g y : ℂ) * (starRingEnd ℂ) (g (y - x) : ℂ)) τ

/-- **Exact Spatial Translation Invariance of `compactFullWeilEnergy` and `fullZeroForm`.**
Translating any `g ∈ C_c(ℝ, ℝ)` to any spatial interval (including across `x = 0`, where
`v = e^{-x}` crosses `1` into low multiplicative scales) leaves `compactFullWeilEnergy g`
and `fullZeroForm g` identically unchanged. -/
theorem compactFullWeilEnergy_translatedCompactSource_eq (g : C_c(ℝ, ℝ)) (τ : ℝ) :
    compactFullWeilEnergy (translatedCompactSource g τ) = compactFullWeilEnergy g ∧
    fullZeroForm (translatedCompactSource g τ) = fullZeroForm g := by
  have h1 : compactFullWeilEnergy (translatedCompactSource g τ) = compactFullWeilEnergy g := by
    unfold compactFullWeilEnergy
    rw [weilTest_translatedCompactSource_eq]
  refine ⟨h1, ?_⟩
  rw [fullZeroForm_eq_compactFullWeilEnergy, fullZeroForm_eq_compactFullWeilEnergy, h1]

/-- **Unconditional Grid-Tent Convergence for Compact Doubly Collared Critical Sources.**
For every truncation `V ≥ 1`, every finite set `S : Finset ℕ` (whether a single window, a
lacunary block family, or a low/high multi-scale union), and every `b : ℕ → ℝ`, the single-scale
grid tent patterns of `G(x) = e^{-3x/2} g^V(x)` on `[-(log(2V) + 1), log(2V) + 1]` converge in
`compactFullWeilEnergy` and `fullZeroForm` to `compactFullWeilEnergy (criticalTruncatedTest hVpos S b)`. -/
theorem tendsto_compactFullWeilEnergy_gridTentPattern_criticalTruncatedTest
    {V : ℝ} (hVpos : 0 < V) (hV1 : 1 ≤ V) (S : Finset ℕ) (b : ℕ → ℝ) :
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos S b x
    Tendsto (fun n : ℕ =>
      compactFullWeilEnergy (gridTentPattern G n (-(R + 1))
        ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊))
      atTop (𝓝 (compactFullWeilEnergy (criticalTruncatedTest hVpos S b))) := by
  dsimp only
  set g := criticalTruncatedTest hVpos S b
  set R := Real.log (2 * V)
  have hR0 : 0 ≤ R := Real.log_nonneg (by linarith)
  have hgR : ∀ x, R < |x| → g x = 0 := by
    intro x hx
    apply criticalTruncatedSource_eq_zero hVpos S b
    intro hmem
    have : |x| ≤ R := abs_le.mpr ⟨hmem.1, hmem.2.trans hR0⟩
    linarith
  set Mg := 2 * ∑ n ∈ S, |b n|
  have hMg : ∀ x, |g x| ≤ Mg := by
    intro x
    change |criticalTruncatedSource V S b x| ≤ _
    rw [criticalTruncatedSource_eq, abs_mul, abs_mul, abs_mul]
    have h1 : |criticalUpperCutoff (Real.exp (-x) / V)| ≤ 1 := by
      rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
    have h2 : |Real.smoothTransition (Real.exp (-x) - 1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
    have h3 : |Real.smoothTransition (Real.exp (-x) - 1)| *
        (|Real.exp (x / 2)| * |realPhaseCombination S b (Real.exp (-x))|) ≤ Mg := by
      by_cases hx : x ≤ 0
      · have hexp : |Real.exp (x / 2)| ≤ 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (by linarith)
        have hph := abs_realPhaseCombination_le_two_mul S b (Real.exp (-x))
        calc _ ≤ 1 * (1 * Mg) := mul_le_mul h2 (mul_le_mul hexp hph (abs_nonneg _) zero_le_one)
              (by positivity) zero_le_one
          _ = Mg := by ring
      · rw [Real.smoothTransition.zero_of_nonpos (by
          have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
          rw [Real.exp_zero] at this; linarith), abs_zero, zero_mul]
        have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n)
        unfold Mg; positivity
    calc |criticalUpperCutoff (Real.exp (-x) / V)| *
          (|Real.smoothTransition (Real.exp (-x) - 1)| *
            (|Real.exp (x / 2)| * |realPhaseCombination S b (Real.exp (-x))|))
        ≤ 1 * Mg := mul_le_mul h1 h3 (by positivity) zero_le_one
      _ = Mg := one_mul _
  obtain ⟨Kg, hKg0⟩ := exists_lipschitz_criticalTruncatedSource hVpos S b
  have hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y| := hKg0
  have hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤
      Real.exp (3 * R / 2) * (Kg + 3 / 2 * Mg) * |x - y| := by
    intro x y
    have h := expWeight_mul_lipschitz (F := fun z => g (-z)) hR0
      (fun u v => by simpa only [show -u - -v = -(u - v) by ring, abs_neg] using hKg (-u) (-v))
      (fun u => hMg (-u))
      (fun u hu => hgR (-u) (by rwa [abs_neg])) (-x) (-y)
    simpa only [show 3 * -x / 2 = -(3 * x / 2) by ring,
      show 3 * -y / 2 = -(3 * y / 2) by ring, neg_neg,
      show -x - -y = -(x - y) by ring, abs_neg] using h
  exact tendsto_compactFullWeilEnergy_gridTentPattern g hR0 hgR hMg hKg hGL

/-- **General Positivity Transfer from Compact Doubly Collared Critical Sources to
`gridTentPattern` and `smoothGridTentDetector` Across All Five Form Realizations.** -/
theorem gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge
    {V : ℝ} (hVpos : 0 < V) (hV1 : 1 ≤ V) (S : Finset ℕ) (b : ℕ → ℝ)
    {μ : ℝ} (hμ : 0 < μ) (hge : 2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos S b)) :
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos S b x
    ∀ᶠ n : ℕ in atTop,
      let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
      μ ≤ compactFullWeilEnergy P ∧
      μ ≤ fullZeroForm P ∧
      ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
        let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
        ContDiff ℝ 2 D ∧
        HasCompactSupport D ∧
        μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
          (EF.weilTest D D)).re ∧
        μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
        configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
          configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set R := Real.log (2 * V)
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos S b x
  have hlim := tendsto_compactFullWeilEnergy_gridTentPattern_criticalTruncatedTest hVpos hV1 S b
  have hgt : μ < compactFullWeilEnergy (criticalTruncatedTest hVpos S b) := by linarith
  filter_upwards [hlim.eventually (eventually_gt_nhds hgt)] with n hn
  set M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
  have hP_ge : μ ≤ compactFullWeilEnergy P := le_of_lt hn
  have hP_zf : μ ≤ fullZeroForm P := by
    rw [fullZeroForm_eq_compactFullWeilEnergy P]
    exact hP_ge
  refine ⟨hP_ge, hP_zf, fun q hq => ?_⟩
  set D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
  obtain ⟨hD_diff, hD_cpt⟩ := smoothGridTentDetector_admissible G n (-(R + 1)) M q
  obtain ⟨hD_approx, hD_W, hD_refl⟩ := smoothGridTentDetector_fullWeil_approximation G n (-(R + 1)) M q
  have hD_weil_ge : μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
      (EF.weilTest D D)).re := by
    have h1 := (abs_le.mp hD_approx).1
    linarith
  have hD_zeta_ge : μ / 2 ≤ (zetaZeroConfig.W D D).re := by
    rw [hD_W]
    exact hD_weil_ge
  have hD_gap : configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
      configurationSquareMass zetaZeroConfig D := by
    linarith [hD_refl, hD_zeta_ge]
  exact ⟨hD_diff, hD_cpt, hD_weil_ge, hD_zeta_ge, hD_gap⟩

/-- **Unconditional Grid-Tent and Smooth-Detector Positivity Across Arbitrary-Depth Lacunary Block
Families (`[M_0, M_0^{8^{J-1}}]`, Beyond Any `δ`-Polynomial Width).**
There exists `M₀` such that for every lacunary block family `IsLacunaryBlockFamily J M S` with
`M₀ ≤ M 0` (spanning arbitrarily many blocks `J`), every truncation `V ≥ criticalTruncationThreshold`,
and every nonzero `b`, the single-scale grid tent patterns `gridTentPattern` and their smoothed
`C_c²` detectors `smoothGridTentDetector` unconditionally achieve strict positivity across all
five form realizations (`compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional`,
`zetaZeroConfig.W`, and `configurationSquareMass - configurationReflectionDefect`). -/
theorem exists_lacunary_gridTentPattern_and_smoothDetector_pos :
    ∃ M₀ : ℕ, ∀ (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ), IsLacunaryBlockFamily J M S → M₀ ≤ M 0 →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
        (∃ n ∈ (Finset.range J).biUnion S, b n ≠ 0) →
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) *
            criticalTruncatedTest hVpos ((Finset.range J).biUnion S) b x
          ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
            let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
            μ ≤ compactFullWeilEnergy P ∧
            μ ≤ fullZeroForm P ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                (EF.weilTest D D)).re ∧
              μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
              configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
                configurationSquareMass zetaZeroConfig D := by
  obtain ⟨M₀, hM₀⟩ := exists_compactFullWeilEnergy_pos_of_lacunary
  refine ⟨M₀, fun J M S hlac hM V hVpos hV b hb => ?_⟩
  have hpos := hM₀ J M S hlac hM V hVpos hV b hb
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set T := (Finset.range J).biUnion S
  set μ := compactFullWeilEnergy (criticalTruncatedTest hVpos T b) / 2
  have hμ : 0 < μ := by unfold μ; linarith
  refine ⟨μ, hμ, gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge
    hVpos hV1 T b hμ (by unfold μ; linarith)⟩

/-- **Unconditional Grid-Tent and Smooth-Detector Positivity Across Polynomial Scale Windows `[M, LM]`.** -/
theorem exists_polynomial_window_gridTentPattern_and_smoothDetector_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos S b x
          let μ : ℝ := criticalTruncatedArchLogSlope / 8 * Real.log M * ∑ n ∈ S, b n ^ 2
          0 < μ ∧ ∀ᶠ n : ℕ in atTop,
            let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
            μ ≤ compactFullWeilEnergy P ∧
            μ ≤ fullZeroForm P ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
                (EF.weilTest D D)).re ∧
              μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
              configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
                configurationSquareMass zetaZeroConfig D := by
  obtain ⟨δ, hδ, M₀, hwin⟩ := exists_polynomial_window_compact_weil_and_fullZeroForm_pos
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM V hVpos hV S hS b hb => ?_⟩
  obtain ⟨hpos, hge, _, _⟩ := hwin M hM L hL hLM V hVpos hV S hS b hb
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set μ := criticalTruncatedArchLogSlope / 8 * Real.log M * ∑ n ∈ S, b n ^ 2
  have hμ : 0 < μ := by unfold μ; linarith
  refine ⟨hμ, gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge
    hVpos hV1 S b hμ (by unfold μ; linarith)⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
