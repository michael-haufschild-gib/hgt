import GaloisForLFunctions.RHTower.GaussianPrimeChebyshevBias
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».MultiScaleLowModeAndGridTentSchurBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineClockResonance

/-!
# Dense Scale Windows, the Exact Dilation-Ring Majorant, Spaced Cross-Block Bounds, and Multi-Window Positivity

This module resolves the open problem on dense scale windows (`[M, LM]`), cross-block prime
asymmetry, and multi-window unions across four main results:

1. **Exact `Θ(log L)` Asymptotics and `ε`-Free Dyadic Conversion for the Dilation-Ring Majorant
   (`windowRingMajorant_bounds`, `tendsto_windowRingMajorant_div_log`,
   `abs_criticalPrimeEnergy_le_of_window_direct`,
   `abs_criticalTruncatedPrimeEnergy_le_of_window_direct`,
   `exists_direct_polynomial_window_all_five_forms_pos`):**
   The scale-window dilation correlation bound produces the dilation-ring majorant
   `M_win(L) = ∑_{r ≥ 2} (Λ(r)/r) min(1, √(L/r))`. Instead of perturbing `min(1, √(L/r)) ≤ (L/r)^ε`
   at `ε = 1/(2 + log L)` (which loses a factor `6e > 16`), splitting `M_win(L)` directly at `r ≤ L`
   and decomposing `r > L` into dyadic blocks `(2^k L, 2^{k+1} L]` via Mertens' first theorem
   (`RHTower.abs_sum_Ioc_vonMangoldt_div_sub_log_le`, `RHTower.sum_Ioc_vonMangoldt_div_dyadic_le`)
   proves that for every `L ≥ 1`,
   `log L - (log 4 + 4) ≤ M_win(L) ≤ log L + (4 log 2 + 9(log 4 + 4))`,
   and consequently `M_win(L) / log L → 1` as `L → ∞`. This proves that the `Θ(log L)` width cost of
   the dilation-ring majorant is asymptotically exact while removing the `6e` factor from both
   `criticalPrimeEnergy` and `criticalTruncatedPrimeEnergy`, widening the unconditional single-window
   polynomial positivity exponent `δ` by a factor strictly exceeding `6e > 16`.

2. **Spaced-Row Cross-Block Theorem and Scale-Free Logarithmic / Upward-Uniform Coupling
   (`sum_row_dilationSum_branch_le`, `sum_row_dilationKernel_spaced_le`,
   `abs_bilinear_crossBlock_spaced_le`, `abs_sum_integral_crossBlock_logRatio_le`,
   `abs_truncatedBlockCoupling_le_logRatio`, `abs_truncatedBlockCoupling_up_uniform_le`):**
   In the cross-block decay law `τ(m, n) = (1 + log n) √(1/n + m √(m/n))`, the `m √(m/n)` factor
   grows like `M^{3/4}` on adjacent blocks `M' = 2M` because `sum_row_dilationKernel_le` multiplied
   the single-pair dilation sum by the block cardinality `|S'| ≤ M' + 1`. Exchanging `∑_{n' ∈ S'}`
   and `∑_{r ∈ R}` in the row sum and exploiting the `(11 r l / 12)`-spacing of the dilated partner
   frequencies `n' ↦ r l θ_j(n')` on `r l M' < 6 k M` together with the cancellation
   `(M' + 1)/(l M')² ≤ 2/M'` on `r l M' ≥ 6 k M` proves that the row sum satisfies the exact same
   scale-free bound `12 (A + 16B) (1 + log(1 + 6kM/M'))²` as the column sum. Consequently, for
   every pair of dyadic blocks `S` (at `M`) and `S'` (at `M'`), the prime coupling is bounded by
   `5 K(A,B) (1 + log(1 + 6M/M'))² ‖b_S‖₂ ‖c_{S'}‖₂`, depending only on the scale ratio `M/M'`
   (never growing as `M^{3/4}`), and in the upward order `M ≤ M'` is uniformly `O(‖b_S‖₂ ‖c_{S'}‖₂)`.

3. **Arithmetic Congruence Resonance Structure and the `√M` Collar-Drift Boundary
   (`harmonic_factorialShiftedFreq_affine_gap`, `resonant_scale_mod_eq_and_spacing`,
   `dilated_factorialAffineDefect_window_bounds`):**
   On a scale window `[M, LM]`, the harmonic shifted-frequency gap between `(k, n)` and `(lr, n')`
   splits into the affine clock difference `k(n+1) - lr(n'+1) + (k - lr)/12` and the collar-defect
   difference `lr · e_{n'+1} - k · e_{n+1}`. Scales `n` with a fixed integer offset
   `k(n+1) - lr(n'+1) = j` lie in a single congruence class modulo `lr` and are spaced by at least
   `lr / gcd(k, lr)`, while the dilated affine defect `r · e_{n'+1}` lies in
   `[r / (225 LM), r / (140 M)]`, remaining bounded by `L² / (140 M)` across `r ≤ L` (hence `O(1)`
   precisely in the sub-square-root window regime `L lesssim √M`).

4. **Lacunary Families of Polynomial Scale Windows and Arbitrary-Exponent Dense Windows Across All
   Five Form Realizations (`IsLacunaryWindowFamily`,
   `abs_criticalTruncatedPrimeEnergy_le_of_lacunaryWindows`,
   `criticalTruncatedCompleteEnergy_ge_of_lacunaryWindows`,
   `exists_lacunaryPolynomialWindows_all_five_forms_pos`,
   `arbitrary_polynomial_dense_window_coupled_all_five_forms_pos`):**
   Unifying polynomial scale windows and lacunary block families, for any family of scale windows
   `W_i ⊂ [M_i, L_i M_i]` (`i < J`) with `(L_i M_i)^8 ≤ M_{i+1}`, slicing each window `W_i` into
   dyadic slices `dyadicSlice (W_i) k` over `windowDyadicIndices (M_i) (L_i)` forces the dyadic
   exponents across distinct windows to satisfy `8k ≤ k'` (hence `(2^k)^8 ≤ 2^{k'}` and `k < k'`),
   so all cross-window prime couplings sum to at most `650 K_CB ∑_i E_i` independently of the
   window widths `L_i`, the number of windows `J`, and the truncation `V`. This yields unconditional
   strict positivity across all five form realizations on arbitrary-depth lacunary unions of
   polynomial scale windows, as well as on dense windows `[M_0, M_0^{1+Δ}]` of arbitrary polynomial
   width `Δ > 0` coupled to a polynomially higher window `[M_1, M_1^{1+δ}]`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ENNReal
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Section 1: Exact `Θ(log L)` Asymptotics and `ε`-Free Dyadic Conversion for the Dilation-Ring Majorant -/

/-- Term `(Λ(r)/r) min(1, √(L/r))` of the scale-window dilation-ring majorant at width `L`. -/
def windowRingMajorantTerm (L r : ℕ) : ℝ :=
  (Λ r : ℝ) / r * min 1 (Real.sqrt ((L : ℝ) / r))

/-- The scale-window dilation-ring majorant `M_win(L) = ∑_{r=0}^∞ (Λ(r)/r) min(1, √(L/r))`. -/
def windowRingMajorant (L : ℕ) : ℝ :=
  ∑' r : ℕ, windowRingMajorantTerm L r

/-- Explicit upper offset `4 log 2 + 9 (log 4 + 4)` in the `ε`-free dyadic bound for `M_win(L)`. -/
def windowRingMajorantUpperOffset : ℝ :=
  4 * Real.log 2 + 9 * (Real.log 4 + 4)

@[simp] theorem windowRingMajorantTerm_zero (L : ℕ) : windowRingMajorantTerm L 0 = 0 := by
  simp [windowRingMajorantTerm]

@[simp] theorem windowRingMajorantTerm_one (L : ℕ) : windowRingMajorantTerm L 1 = 0 := by
  simp [windowRingMajorantTerm]

theorem windowRingMajorantTerm_nonneg (L r : ℕ) : 0 ≤ windowRingMajorantTerm L r := by
  unfold windowRingMajorantTerm
  exact mul_nonneg (vonMangoldt_div_nonneg r) (le_min zero_le_one (Real.sqrt_nonneg _))

theorem windowRingMajorantTerm_le_vonMangoldt_div (L r : ℕ) :
    windowRingMajorantTerm L r ≤ (Λ r : ℝ) * (r : ℝ)⁻¹ := by
  unfold windowRingMajorantTerm
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_right (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg r))) (min_le_left 1 _)

theorem windowRingMajorantTerm_eq_of_le {L r : ℕ} (hr : 1 ≤ r) (hrL : r ≤ L) :
    windowRingMajorantTerm L r = (Λ r : ℝ) * (r : ℝ)⁻¹ := by
  unfold windowRingMajorantTerm
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : 1 ≤ Real.sqrt ((L : ℝ) / r) := by
    rw [Real.one_le_sqrt, one_le_div hr0]
    exact_mod_cast hrL
  rw [min_eq_left h1, mul_one, div_eq_mul_inv]

/-- Dyadic weight decay `min(1, √(L/r)) ≤ (3/4)^k` for `r ≥ L · 2^k` (`L ≥ 1`). -/
theorem windowRingMajorantTerm_le_dyadic {L k r : ℕ} (hL : 1 ≤ L) (hr : L * 2 ^ k ≤ r) :
    windowRingMajorantTerm L r ≤ (Λ r : ℝ) * (r : ℝ)⁻¹ * (3 / 4 : ℝ) ^ k := by
  unfold windowRingMajorantTerm
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ((min_le_right 1 _).trans ?_)
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)))
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hr_pos : 0 < r := lt_of_lt_of_le (Nat.mul_pos hL (Nat.two_pow_pos k)) hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr_pos
  have hr_le : (L : ℝ) * (2 : ℝ) ^ k ≤ r := by exact_mod_cast hr
  have hpow : (1 / 2 : ℝ) ^ k ≤ ((3 / 4 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) ^ 2) k
  have hdiv : (L : ℝ) / r ≤ ((3 / 4 : ℝ) ^ k) ^ 2 := by
    calc (L : ℝ) / r ≤ (L : ℝ) / ((L : ℝ) * (2 : ℝ) ^ k) :=
          div_le_div_of_nonneg_left hL0.le (by positivity) hr_le
      _ = (1 / 2 : ℝ) ^ k := by
          rw [div_mul_eq_div_div, div_self hL0.ne', (one_div_pow 2 k).symm]
      _ ≤ ((3 / 4 : ℝ) ^ k) ^ 2 := hpow
  calc Real.sqrt ((L : ℝ) / r) ≤ Real.sqrt (((3 / 4 : ℝ) ^ k) ^ 2) := Real.sqrt_le_sqrt hdiv
    _ = (3 / 4 : ℝ) ^ k := Real.sqrt_sq (by positivity)

/-- Partial-sum bound for `windowRingMajorantTerm L` via dyadic block decomposition. -/
theorem sum_range_windowRingMajorantTerm_le {L : ℕ} (hL : 1 ≤ L) (M : ℕ) :
    ∑ r ∈ Finset.range M, windowRingMajorantTerm L r ≤
      Real.log L + windowRingMajorantUpperOffset := by
  set c : ℝ := Real.log 4 + 4
  set B : ℝ := Real.log 2 + 2 * c
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold c; linarith
  have hB0 : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    unfold B; linarith
  have hhead : ∑ r ∈ Finset.Ioc 0 L, windowRingMajorantTerm L r ≤ Real.log L + c := by
    have h1 := (abs_le.mp (RHTower.abs_sum_Ioc_vonMangoldt_div_sub_log_le hL)).2
    have h2 : ∑ r ∈ Finset.Ioc 0 L, windowRingMajorantTerm L r ≤
        ∑ r ∈ Finset.Ioc 0 L, (Λ r : ℝ) * (r : ℝ)⁻¹ :=
      Finset.sum_le_sum fun r _ => windowRingMajorantTerm_le_vonMangoldt_div L r
    linarith
  have hblock : ∀ k : ℕ,
      ∑ r ∈ Finset.Ioc (L * 2 ^ k) (L * 2 ^ (k + 1)), windowRingMajorantTerm L r ≤
        B * (3 / 4 : ℝ) ^ k := by
    intro k
    have ha : 1 ≤ L * 2 ^ k := Nat.mul_pos hL (Nat.two_pow_pos k)
    calc ∑ r ∈ Finset.Ioc (L * 2 ^ k) (L * 2 ^ (k + 1)), windowRingMajorantTerm L r
        ≤ ∑ r ∈ Finset.Ioc (L * 2 ^ k) (L * 2 ^ (k + 1)),
            (Λ r : ℝ) * (r : ℝ)⁻¹ * (3 / 4 : ℝ) ^ k :=
          Finset.sum_le_sum fun r hr =>
            windowRingMajorantTerm_le_dyadic hL (Finset.mem_Ioc.mp hr).1.le
      _ = (∑ r ∈ Finset.Ioc (L * 2 ^ k) (2 * (L * 2 ^ k)), (Λ r : ℝ) * (r : ℝ)⁻¹) *
            (3 / 4 : ℝ) ^ k := by
          rw [← Finset.sum_mul, show L * 2 ^ (k + 1) = 2 * (L * 2 ^ k) by ring]
      _ ≤ B * (3 / 4 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (RHTower.sum_Ioc_vonMangoldt_div_dyadic_le ha) (by positivity)
  have hgeom : ∑ k ∈ Finset.range M, (3 / 4 : ℝ) ^ k ≤ 4 := by
    rw [geom_sum_eq (by norm_num)]
    have hpos : 0 ≤ (3 / 4 : ℝ) ^ M := by positivity
    have hsub : ((3 / 4 : ℝ) ^ M - 1) / (3 / 4 - 1) = 4 * (1 - (3 / 4 : ℝ) ^ M) := by ring
    linarith
  have hsub : Finset.range M ⊆ insert 0 (Finset.Ioc 0 (L * 2 ^ M)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [Finset.mem_insert, Finset.mem_Ioc]
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have h2 : 2 ^ M ≤ L * 2 ^ M := Nat.le_mul_of_pos_left _ hL
    omega
  calc ∑ r ∈ Finset.range M, windowRingMajorantTerm L r
      ≤ ∑ r ∈ insert 0 (Finset.Ioc 0 (L * 2 ^ M)), windowRingMajorantTerm L r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => windowRingMajorantTerm_nonneg L r
    _ = ∑ r ∈ Finset.Ioc 0 (L * 2 ^ M), windowRingMajorantTerm L r := by
        rw [Finset.sum_insert (by simp), windowRingMajorantTerm_zero, zero_add]
    _ = ∑ r ∈ Finset.Ioc 0 L, windowRingMajorantTerm L r +
          ∑ k ∈ Finset.range M,
            ∑ r ∈ Finset.Ioc (L * 2 ^ k) (L * 2 ^ (k + 1)), windowRingMajorantTerm L r :=
        RHTower.sum_Ioc_dyadic (windowRingMajorantTerm L) L M
    _ ≤ (Real.log L + c) + ∑ k ∈ Finset.range M, B * (3 / 4 : ℝ) ^ k :=
        add_le_add hhead (Finset.sum_le_sum fun k _ => hblock k)
    _ = Real.log L + c + B * ∑ k ∈ Finset.range M, (3 / 4 : ℝ) ^ k := by
        rw [← Finset.mul_sum]
    _ ≤ Real.log L + c + B * 4 := by linarith [mul_le_mul_of_nonneg_left hgeom hB0]
    _ = Real.log L + windowRingMajorantUpperOffset := by
        unfold windowRingMajorantUpperOffset B c; ring

/-- Direct `ε`-free summability of `windowRingMajorantTerm L` for every `L : ℕ`. -/
theorem summable_windowRingMajorantTerm (L : ℕ) : Summable (windowRingMajorantTerm L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have heq : windowRingMajorantTerm 0 = fun _ => 0 := by
      ext r; simp [windowRingMajorantTerm]
    rw [heq]
    exact summable_zero
  · exact summable_of_sum_range_le (windowRingMajorantTerm_nonneg L)
      (sum_range_windowRingMajorantTerm_le hL)

/-- **Two-sided `Θ(log L)` sandwich for the scale-window dilation-ring majorant.**
For every `L ≥ 1`,
`log L - (log 4 + 4) ≤ windowRingMajorant L ≤ log L + (4 log 2 + 9(log 4 + 4))`.
Thus the logarithmic width cost of the dilation-ring majorant is sharp up to an additive `O(1)`
constant, with no `r^{-ε}` perturbation required. -/
theorem windowRingMajorant_bounds {L : ℕ} (hL : 1 ≤ L) :
    Real.log L - (Real.log 4 + 4) ≤ windowRingMajorant L ∧
      windowRingMajorant L ≤ Real.log L + windowRingMajorantUpperOffset := by
  refine ⟨?_, Real.tsum_le_of_sum_range_le (windowRingMajorantTerm_nonneg L)
    (sum_range_windowRingMajorantTerm_le hL)⟩
  have hsum : ∑ r ∈ Finset.Ioc 0 L, (Λ r : ℝ) * (r : ℝ)⁻¹ =
      ∑ r ∈ Finset.Ioc 0 L, windowRingMajorantTerm L r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Ioc] at hr
    exact (windowRingMajorantTerm_eq_of_le hr.1 hr.2).symm
  have hmert := (abs_le.mp (RHTower.abs_sum_Ioc_vonMangoldt_div_sub_log_le hL)).1
  have hle : ∑ r ∈ Finset.Ioc 0 L, windowRingMajorantTerm L r ≤ windowRingMajorant L :=
    (summable_windowRingMajorantTerm L).sum_le_tsum _ fun r _ => windowRingMajorantTerm_nonneg L r
  linarith

theorem windowRingMajorantUpperOffset_pos : 0 < windowRingMajorantUpperOffset := by
  unfold windowRingMajorantUpperOffset
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-- **Exact asymptotic `M_win(L) / log L → 1` as `L → ∞`.** -/
theorem tendsto_windowRingMajorant_div_log :
    Tendsto (fun L : ℕ => windowRingMajorant L / Real.log L) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C := windowRingMajorantUpperOffset
  have hC : 0 < C := windowRingMajorantUpperOffset_pos
  have hlog : Tendsto (fun L : ℕ => Real.log L) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hlog.eventually_gt_atTop (C / ε)).and (eventually_ge_atTop 2))
  refine ⟨N₀, fun L hL => ?_⟩
  obtain ⟨hlogL_gt, hL2⟩ := hN₀ L hL
  have hL1 : 1 ≤ L := by omega
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL2)
  obtain ⟨hlow, hhigh⟩ := windowRingMajorant_bounds hL1
  have hc_le_C : Real.log 4 + 4 ≤ C := by
    unfold C windowRingMajorantUpperOffset
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have habs : |windowRingMajorant L - Real.log L| ≤ C :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.dist_eq, show windowRingMajorant L / Real.log L - 1 =
      (windowRingMajorant L - Real.log L) / Real.log L by field_simp,
    abs_div, abs_of_pos hlogL_pos]
  calc |windowRingMajorant L - Real.log L| / Real.log L
      ≤ C / Real.log L := div_le_div_of_nonneg_right habs hlogL_pos.le
    _ < ε := by
        have := (div_lt_iff₀ hε).mp hlogL_gt
        rw [div_lt_iff₀ hlogL_pos]
        linarith

/-- Direct (`ε`-free) logarithmic prime-window slope `(4/π⁴) K_W` of the critical prime channel,
improving `criticalWindowPrimeSlope` by the factor `6e > 16`. -/
def directWindowPrimeSlope : ℝ :=
  4 / Real.pi ^ 4 * criticalWindowConstant

/-- Direct (`ε`-free) logarithmic prime-window slope `(4/π⁴) K_TW` of compact doubly collared
sources, improving `criticalTruncatedWindowPrimeSlope` by the factor `6e > 16`. -/
def directTruncatedWindowPrimeSlope : ℝ :=
  4 / Real.pi ^ 4 * criticalTruncatedWindowConstant

theorem directWindowPrimeSlope_nonneg : 0 ≤ directWindowPrimeSlope := by
  unfold directWindowPrimeSlope
  have := criticalWindowConstant_nonneg
  positivity

theorem directTruncatedWindowPrimeSlope_nonneg : 0 ≤ directTruncatedWindowPrimeSlope := by
  unfold directTruncatedWindowPrimeSlope
  have := criticalTruncatedWindowConstant_nonneg
  positivity

/-- The `ε`-free slope `directTruncatedWindowPrimeSlope` is strictly smaller than
`criticalTruncatedWindowPrimeSlope` by the exact factor `6e > 16`. -/
theorem criticalTruncatedWindowPrimeSlope_eq_six_exp_mul_direct :
    criticalTruncatedWindowPrimeSlope =
      6 * Real.exp 1 * directTruncatedWindowPrimeSlope ∧
    16 * directTruncatedWindowPrimeSlope ≤ criticalTruncatedWindowPrimeSlope := by
  have heq : criticalTruncatedWindowPrimeSlope =
      6 * Real.exp 1 * directTruncatedWindowPrimeSlope := by
    unfold criticalTruncatedWindowPrimeSlope directTruncatedWindowPrimeSlope
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have h1 : (2.718 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9.trans_le' (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith) directTruncatedWindowPrimeSlope_nonneg

/-- **Direct `ε`-free window bound for `criticalPrimeEnergy`.**
For every scale window `ScaleWindow S M L` (`M, L ≥ 1`), bounding each prime atom directly by
`windowRingMajorantTerm L r` removes the `6e` factor of the `r^{-ε}` perturbation. -/
theorem abs_criticalPrimeEnergy_le_of_window_direct {S : Finset ℕ} {M L : ℕ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |criticalPrimeEnergy S b| ≤
      directWindowPrimeSlope * windowRingMajorant L * ∑ n ∈ S, b n ^ 2 ∧
    |criticalPrimeEnergy S b| ≤
      directWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset) *
        ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set C := directWindowPrimeSlope * E
  have hC : 0 ≤ C := mul_nonneg directWindowPrimeSlope_nonneg hE
  have hbd (r : ℕ) : |criticalPrimeAtom S b r| ≤ C * windowRingMajorantTerm L r := by
    unfold criticalPrimeAtom windowRingMajorantTerm
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      have hw := abs_criticalWindowCorrelation_le hM hL hS b (r := r) (by omega)
      rw [integral_criticalFactorialSource_mul_dilate_eq S b (by omega), abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg hΛ hsr.le), abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
      have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
      calc (Λ r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_ + _|)
          ≤ (Λ r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
              (4 / Real.pi ^ 4 * (criticalWindowConstant * min 1 (Real.sqrt (L / r))) * E)) := by
            gcongr
        _ = C * ((Λ r : ℝ) / r * min 1 (Real.sqrt (L / r))) := by
            unfold C directWindowPrimeSlope
            field_simp
            rw [hsq]
            ring
    · have : 0 ≤ C * ((Λ r : ℝ) / r * min 1 (Real.sqrt (L / r))) :=
        mul_nonneg hC (windowRingMajorantTerm_nonneg L r)
      simpa using this
  have hmaj : Summable fun r : ℕ => C * windowRingMajorantTerm L r :=
    (summable_windowRingMajorantTerm L).mul_left C
  have habs : Summable fun r => ‖criticalPrimeAtom S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj
  have hmain : |criticalPrimeEnergy S b| ≤
      directWindowPrimeSlope * windowRingMajorant L * E := by
    unfold criticalPrimeEnergy windowRingMajorant
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm habs).trans
      ((habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj).trans ?_)
    rw [tsum_mul_left]
    unfold C
    ring_nf
    exact le_rfl
  refine ⟨hmain, hmain.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (windowRingMajorant_bounds hL).2 directWindowPrimeSlope_nonneg) hE

/-- **Direct `ε`-free window bound for `criticalTruncatedPrimeEnergy` (uniform in `V > 0`).** -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_window_direct {V : ℝ} (hV : 0 < V)
    {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V S b| ≤
      directTruncatedWindowPrimeSlope * windowRingMajorant L * ∑ n ∈ S, b n ^ 2 ∧
    |criticalTruncatedPrimeEnergy V S b| ≤
      directTruncatedWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset) *
        ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set C := directTruncatedWindowPrimeSlope * E
  have hC : 0 ≤ C := mul_nonneg directTruncatedWindowPrimeSlope_nonneg hE
  have hbd (r : ℕ) : |criticalTruncatedPrimeAtom V S b r| ≤ C * windowRingMajorantTerm L r := by
    refine (abs_criticalTruncatedPrimeAtom_le_of_window hV hM hL hS b r).trans ?_
    split_ifs with hr
    · unfold C directTruncatedWindowPrimeSlope windowRingMajorantTerm
      exact le_of_eq (by ring)
    · exact mul_nonneg hC (windowRingMajorantTerm_nonneg L r)
  have hmaj : Summable fun r : ℕ => C * windowRingMajorantTerm L r :=
    (summable_windowRingMajorantTerm L).mul_left C
  have habs : Summable fun r => ‖criticalTruncatedPrimeAtom V S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj
  have hmain : |criticalTruncatedPrimeEnergy V S b| ≤
      directTruncatedWindowPrimeSlope * windowRingMajorant L * E := by
    unfold criticalTruncatedPrimeEnergy windowRingMajorant
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm habs).trans
      ((habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj).trans ?_)
    rw [tsum_mul_left]
    unfold C
    ring_nf
    exact le_rfl
  refine ⟨hmain, hmain.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (windowRingMajorant_bounds hL).2
      directTruncatedWindowPrimeSlope_nonneg) hE

/-- **Direct (`6e`-improved) complete energy lower bound on scale windows `[M, LM]`.** -/
theorem criticalTruncatedCompleteEnergy_ge_of_window_direct (S : Finset ℕ) (b : ℕ → ℝ)
    {M L : ℕ} (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) {V : ℝ}
    (hV : criticalTruncationThreshold ≤ V) :
    (((criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
        criticalTruncatedWindowBaseConstant -
        2 * directTruncatedWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset)) *
          ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalTruncatedCompleteEnergy V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hV0 : 0 < V := by linarith
  set X := criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy S b hM (fun n hn => (hS n hn).1) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  set ac := sourceAutocorrelation (criticalTruncatedSource V S b) 0
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 := neg_abs_le (EF.gammaBracket 0 * ac)
    rw [abs_mul, abs_of_nonneg hac0] at h1
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1
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
  have hpol : |criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b| ≤
      144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalTruncatedPolarReadout_le hV0 S b
    have h2 := abs_criticalTruncatedPolarEndpoint_le hV1 S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * T) * (c * (12 * T)) := h12
      _ = 144 * a * c * T ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_window_direct hV0
    (by omega) hL hS b).2).2
  have hpol' := (abs_le.mp hpol).1
  have hch : -((criticalTruncatedWindowBaseConstant +
      2 * directTruncatedWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset)) * E) ≤
      EF.gammaBracket 0 * ac +
        2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
        2 * criticalTruncatedPrimeEnergy V S b := by
    unfold criticalTruncatedWindowBaseConstant
    nlinarith
  unfold criticalTruncatedCompleteEnergy
  rw [show (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant -
      2 * directTruncatedWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset)) * E =
      X + -((criticalTruncatedWindowBaseConstant +
        2 * directTruncatedWindowPrimeSlope * (Real.log L + windowRingMajorantUpperOffset)) * E) by
      ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Widened Polynomial Scale-Window Positivity Across All Five Form Realizations.**
Removing the `6e` perturbation factor widens the polynomial scale-window exponent to
`δ_direct = s_T / (4 (directTruncatedWindowPrimeSlope + 1))` while preserving unconditional
positivity of `compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional`, and single-scale
`gridTentPattern` / `smoothGridTentDetector` actual-zeta reflection dominance. -/
theorem exists_direct_polynomial_window_all_five_forms_pos :
    let δ : ℝ := criticalTruncatedArchLogSlope / (4 * (directTruncatedWindowPrimeSlope + 1))
    0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos S b x
          let μ : ℝ := criticalTruncatedArchLogSlope / 8 * Real.log M * ∑ n ∈ S, b n ^ 2
          0 < μ ∧
          2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos S b) ∧
          compactFullWeilEnergy (criticalTruncatedTest hVpos S b) =
            fullZeroForm (criticalTruncatedTest hVpos S b) ∧
          ∀ᶠ n : ℕ in atTop,
            let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
            μ ≤ compactFullWeilEnergy P ∧
            μ ≤ fullZeroForm P ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              μ / 2 ≤ (weilFullFunctional (fun m => (Λ m : ℝ))
                (EF.weilTest D D)).re ∧
              μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
              configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
                configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set W := directTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := directTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set K := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant +
    2 * W * windowRingMajorantUpperOffset
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (4 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨hδ, M₀, fun M hM L hL hLM V hVpos hV S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ δ * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hgap : s / 4 * Real.log M ≤
      s * (Real.log M - criticalTruncatedArchLogOffset) - criticalTruncatedWindowBaseConstant -
        2 * W * (Real.log L + windowRingMajorantUpperOffset) := by
    have h1 : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
      calc 2 * W * Real.log L ≤ 2 * W * (δ * Real.log M) := by gcongr
        _ = s / 2 * Real.log M * (W / (W + 1)) := by unfold δ; field_simp; ring
        _ ≤ s / 2 * Real.log M * 1 := by
            gcongr
            rw [div_le_one (by linarith)]; linarith
        _ = s / 2 * Real.log M := by ring
    have h2 : K < s / 4 * Real.log M := by
      have := (div_lt_iff₀ hs).mp hlogM
      linarith
    unfold K at h2
    linarith
  have hcomp := criticalTruncatedCompleteEnergy_ge_of_window_direct S b hM2 hL hS hV
  rw [← compactFullWeilEnergy_criticalTruncatedTest hVpos] at hcomp
  have hweil : s / 4 * Real.log M * ∑ n ∈ S, b n ^ 2 ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S b) :=
    (mul_le_mul_of_nonneg_right hgap hE.le).trans (EReal.coe_le_coe_iff.mp hcomp)
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set μ := s / 8 * Real.log M * ∑ n ∈ S, b n ^ 2
  have hμ : 0 < μ := by unfold μ; positivity
  have h2μ : 2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos S b) := by
    unfold μ; linarith
  exact ⟨hμ, h2μ, (fullZeroForm_eq_compactFullWeilEnergy _).symm,
    gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge hVpos hV1 S b hμ h2μ⟩

/-! ## Section 2: Spaced-Row Cross-Block Theorem and Scale-Free Logarithmic / Upward-Uniform Coupling -/

/-- **Spaced row dilation sum.** Over a partner block `S'` at `M'`, with dilated branch frequencies
`r l θ_j(n')`, the dilation sums at a fixed `y ∈ [0, 3kM]` add up to at most
`2(A + 16B)(1 + log(1 + 6kM/M'))² + 10B`: dilations with `r l M' < 6kM` form a `(11 r l / 12)`-spaced
sum over `n' ∈ S'` against `∑ Λ(r)/r`, while dilations with `r l M' ≥ 6kM` see the `1/f²` tail where
`|S'| / (l M')² ≤ (M' + 1)/(M')² ≤ 2/M' ≤ 2` cancels the block cardinality against `1/(M')²`. -/
theorem sum_row_dilationSum_branch_le {F : ℕ → ℝ → ℝ} {A B : ℝ} (hA : ∀ m f, |F m f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |F m f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (hev : ∀ m f, F m (-f) = F m f)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS' : DyadicScaleBlock S' M') {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (j : Bool)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 3 * (k * M)) :
    ∑ n' ∈ S', primeDilationSum F R y (l * scaleBranch j n') ≤
      2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 10 * B := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
  have hr2 : ∀ r ∈ R, (2 : ℝ) ≤ r := fun r hr => by exact_mod_cast hR r hr
  set z : ℕ → ℕ → ℝ := fun r n' => (r : ℝ) * (l * scaleBranch j n')
  have hz_low (r : ℕ) (n' : ℕ) (hn' : n' ∈ S') : (r : ℝ) * (l * M') ≤ z r n' := by
    have hx := scaleBranch_mem_block hM' hS' j hn'
    have h1 : (l : ℝ) * M' ≤ l * scaleBranch j n' := mul_le_mul_of_nonneg_left hx.1 (by positivity)
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg r)
  have hsp (r : ℕ) (hr : r ∈ R) :
      ∀ m ∈ S', ∀ m' ∈ S', 11 / 12 * |(m : ℝ) - m'| ≤ |z r m - z r m'| := by
    intro m _ m' _
    have h1 := scaleBranch_spacing j m m'
    have hr_ge : (1 : ℝ) ≤ (r : ℝ) * l := by
      have := hr2 r hr
      nlinarith
    have heq : z r m - z r m' = ((r : ℝ) * l) * (scaleBranch j m - scaleBranch j m') := by
      simp only [z]; ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ) * l)]
    calc 11 / 12 * |(m : ℝ) - m'|
        ≤ 1 * |scaleBranch j m - scaleBranch j m'| := by linarith
      _ ≤ ((r : ℝ) * l) * |scaleBranch j m - scaleBranch j m'| :=
          mul_le_mul_of_nonneg_right hr_ge (abs_nonneg _)
  have hspC : 4 * B / (11 / 12 : ℝ) ^ 2 * (Real.pi ^ 2 / 3) ≤ 16 * B := by
    have hpi := Real.pi_lt_d2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : Real.pi ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le (by linarith) 2
    nlinarith
  have hpair (r : ℕ) (hr : r ∈ R) :
      ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) ≤ 2 * (A + 16 * B) := by
    have h1 := sum_abs_le_of_spaced_family (fun _ => hA r) (fun _ => hB r) hB0 S' (z r) y
      (by norm_num) (hsp r hr)
    have h2 := sum_abs_le_of_spaced_family (fun _ => hA r) (fun _ => hB r) hB0 S' (z r) (-y)
      (by norm_num) (hsp r hr)
    have e2 : ∀ n', |F r (y + z r n')| = |F r (-y - z r n')| := fun n' => by
      rw [← hev r (-y - z r n')]
      congr 2
      ring
    rw [Finset.sum_add_distrib]
    simp_rw [e2]
    linarith
  have hfar (r : ℕ) (hr : 6 * (k * M) ≤ (r : ℝ) * (l * M')) :
      ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) ≤ 10 * B * (1 / (r : ℝ) ^ 2) := by
    have hr_pos : 0 < (r : ℝ) * (l * M') := lt_of_lt_of_le (by positivity) hr
    have hcard : (S'.card : ℝ) ≤ M' + 1 := by exact_mod_cast hS'.card_le
    have hterm : ∀ n' ∈ S', |F r (y - z r n')| + |F r (y + z r n')| ≤
        5 * B / (l * M') ^ 2 * (1 / (r : ℝ) ^ 2) := by
      intro n' hn'
      have hz := hz_low r n' hn'
      have f1 : (r : ℝ) * (l * M') / 2 ≤ |y - z r n'| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      have f2 : (r : ℝ) * (l * M') ≤ |y + z r n'| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h1 : |F r (y - z r n')| ≤ B / ((r : ℝ) * (l * M') / 2) ^ 2 := by
        have hne : y - z r n' ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) f1)
        refine (hB r _ hne).trans ?_
        rw [← sq_abs (y - z r n')]
        exact div_le_div_of_nonneg_left hB0 (by positivity) (pow_le_pow_left₀ (by positivity) f1 2)
      have h2 : |F r (y + z r n')| ≤ B / ((r : ℝ) * (l * M')) ^ 2 := by
        have hne : y + z r n' ≠ 0 := abs_pos.mp (lt_of_lt_of_le hr_pos f2)
        refine (hB r _ hne).trans ?_
        rw [← sq_abs (y + z r n')]
        exact div_le_div_of_nonneg_left hB0 (by positivity) (pow_le_pow_left₀ hr_pos.le f2 2)
      calc |F r (y - z r n')| + |F r (y + z r n')|
          ≤ B / ((r : ℝ) * (l * M') / 2) ^ 2 + B / ((r : ℝ) * (l * M')) ^ 2 := add_le_add h1 h2
        _ = 5 * B / (l * M') ^ 2 * (1 / (r : ℝ) ^ 2) := by field_simp; ring
    have hM'2 : (M' + 1 : ℝ) * (5 * B / (l * M') ^ 2) ≤ 10 * B := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hlM' : (M' : ℝ) ^ 2 ≤ (l * M') ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      have hM'sq : (M' + 1 : ℝ) ≤ 2 * (M' : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((M' : ℝ) - 1)]
      nlinarith
    calc ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|)
        ≤ ∑ _n' ∈ S', 5 * B / (l * M') ^ 2 * (1 / (r : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = S'.card * (5 * B / (l * M') ^ 2 * (1 / (r : ℝ) ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M' + 1) * (5 * B / (l * M') ^ 2 * (1 / (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (M' + 1) * (5 * B / (l * M') ^ 2) * (1 / (r : ℝ) ^ 2) := by ring
      _ ≤ 10 * B * (1 / (r : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hM'2 (by positivity)
  unfold primeDilationSum
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not R (fun r : ℕ => (r : ℝ) * (l * M') < 6 * (k * M))]
  have hnear : ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * (l * M') < 6 * (k * M)),
      (Λ r : ℝ) / r * ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) ≤
      2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
    calc _ ≤ ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * (l * M') < 6 * (k * M)),
          (Λ r : ℝ) / r * (2 * (A + 16 * B)) :=
          Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left
            (hpair r (Finset.mem_filter.mp hr).1) (vonMangoldt_div_nonneg r)
      _ = 2 * (A + 16 * B) * ∑ r ∈ R.filter (fun r : ℕ => (r : ℝ) * (l * M') < 6 * (k * M)),
          (Λ r : ℝ) / r := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ ≤ 2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_le _ (by
            have : 0 ≤ 6 * (k * M) / (M' : ℝ) := by positivity
            linarith) fun r hr => ?_) (by positivity)
          have hr' := Finset.mem_filter.mp hr
          refine ⟨by have := hR r hr'.1; omega, ?_⟩
          have h1 : (r : ℝ) * M' ≤ (r : ℝ) * (l * M') :=
            mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg r)
          have h2 : (r : ℝ) ≤ 6 * (k * M) / M' := by
            rw [le_div_iff₀ (by positivity)]
            linarith [hr'.2]
          linarith
  have hfar' : ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * (l * M') < 6 * (k * M)),
      (Λ r : ℝ) / r * ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) ≤ 10 * B := by
    have hsq := sum_one_div_sq_le_two_div
      (R.filter fun r : ℕ => ¬ (r : ℝ) * (l * M') < 6 * (k * M))
      (X := 2) (by norm_num) fun r hr => hr2 r (Finset.mem_filter.mp hr).1
    calc _ ≤ ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * (l * M') < 6 * (k * M)),
          10 * B * (1 / (r : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hfr := hfar r (not_lt.mp (Finset.mem_filter.mp hr).2)
          have hs0 : 0 ≤ ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) :=
            Finset.sum_nonneg fun _ _ => by positivity
          calc _ ≤ 1 * ∑ n' ∈ S', (|F r (y - z r n')| + |F r (y + z r n')|) :=
                mul_le_mul_of_nonneg_right (vonMangoldt_div_le_one r) hs0
            _ ≤ _ := by rw [one_mul]; exact hfr
      _ = 10 * B * ∑ r ∈ R.filter (fun r : ℕ => ¬ (r : ℝ) * (l * M') < 6 * (k * M)),
          1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 10 * B * (2 / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 10 * B := by ring
  linarith

/-- **Spaced row bound of the prime-weighted dilation kernel.**
For `n ∈ S` (a dyadic block at `M`) and partners `n' ∈ S'` (a dyadic block at `M'`), the row sum of
the prime-weighted dilation kernel is bounded by `12(A + 16B)(1 + log(1 + 6kM/M'))²`, matching
`sum_col_dilationKernel_le` and eliminating the linear block-size factor `M' + 1`. -/
theorem sum_row_dilationKernel_spaced_le {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {n : ℕ} (hn : n ∈ S) :
    ∑ n' ∈ S', ∑ r ∈ R, (Λ r : ℝ) / r *
        |dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
  set F : ℕ → ℝ → ℝ := fun r => weightCosineTransform (φ r)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 1 ≤ 1 + Real.log (1 + 6 * (k * M) / M') :=
    le_add_of_nonneg_right (Real.log_nonneg (le_add_of_nonneg_right (by positivity)))
  have hbr (i j : Bool) :
      ∑ n' ∈ S', primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') ≤
        2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 10 * B := by
    have hx := scaleBranch_mem_block hM hS i hn
    have hy0 : 0 ≤ (k : ℝ) * scaleBranch i n := by
      have : (0 : ℝ) ≤ scaleBranch i n := le_trans (by positivity) hx.1
      positivity
    have hy : (k : ℝ) * scaleBranch i n ≤ 3 * (k * M) := by nlinarith [hx.2]
    exact sum_row_dilationSum_branch_le hA hB hB0 (fun m f => weightCosineTransform_neg _ _)
      R hR hM hM' hS' hk hl j hy0 hy
  calc _ ≤ ∑ n' ∈ S', ∑ i : Bool, ∑ j : Bool,
        primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n') / 2 :=
        Finset.sum_le_sum fun n' _ => sum_vonMangoldt_mul_abs_dyadicCrossKernel_le F R k l n n'
    _ = ∑ i : Bool, ∑ j : Bool,
        (∑ n' ∈ S', primeDilationSum F R (k * scaleBranch i n) (l * scaleBranch j n')) / 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
    _ ≤ ∑ _i : Bool, ∑ _j : Bool,
        (2 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 10 * B) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          div_le_div_of_nonneg_right (hbr i j) (by norm_num)
    _ = 4 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 + 20 * B := by
        simp only [Fintype.sum_bool]; ring
    _ ≤ 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := by
        have hsq : 1 ≤ (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 := one_le_pow₀ hL
        nlinarith

/-- **Scale-free per-harmonic cross-block bilinear bound.**
Combining `sum_row_dilationKernel_spaced_le` and `sum_col_dilationKernel_le` via Cauchy–Schwarz
bounds the `(k, l)` harmonic cross-block bilinear form by
`12(A + 16B)(1 + log(1 + 6kM/M'))² ‖b_S‖₂ ‖c_{S'}‖₂` for all `M, M' ≥ 1`. -/
theorem abs_bilinear_crossBlock_spaced_le {φ : ℕ → ℝ → ℝ} {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (Λ r : ℝ) / r *
        dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2 *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', c n' ^ 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  set ρ := 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (k * M) / M')) ^ 2
  have hρ : 0 ≤ ρ := by unfold ρ; positivity
  have hrow := fun n hn => sum_row_dilationKernel_spaced_le hA hB hB0 R hR hM hM' hS hS' hk hl
    (n := n) hn
  have hcol := fun n' hn' => sum_col_dilationKernel_le hA hB hB0 R hR hM hM' hS hS' hk hl
    (n' := n') hn'
  have hG : ∀ n n', 0 ≤ ∑ r ∈ R, (Λ r : ℝ) / r *
      |dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| := fun n n' =>
    Finset.sum_nonneg fun r _ => mul_nonneg (vonMangoldt_div_nonneg r) (abs_nonneg _)
  have hcs := sum_abs_mul_abs_mul_le_sqrt b c _ hG hρ hrow hcol
  have htrans : |∑ n ∈ S, ∑ n' ∈ S', b n * c n' * ∑ r ∈ R, (Λ r : ℝ) / r *
      dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| ≤
      ∑ n ∈ S, ∑ n' ∈ S', |b n| * |c n'| * ∑ r ∈ R, (Λ r : ℝ) / r *
        |dyadicCrossKernel (weightCosineTransform (φ r)) k ((l * r : ℕ) : ℝ) n n'| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (by positivity)
    rw [abs_mul, abs_of_nonneg (vonMangoldt_div_nonneg r)]
  refine htrans.trans (hcs.trans (le_of_eq ?_))
  rw [Real.sqrt_mul hρ, Real.sqrt_mul hρ]
  calc (Real.sqrt ρ * Real.sqrt (∑ n ∈ S, b n ^ 2)) *
        (Real.sqrt ρ * Real.sqrt (∑ n' ∈ S', c n' ^ 2))
      = (Real.sqrt ρ * Real.sqrt ρ) * Real.sqrt (∑ n ∈ S, b n ^ 2) *
          Real.sqrt (∑ n' ∈ S', c n' ^ 2) := by ring
    _ = ρ * Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', c n' ^ 2) := by
        rw [Real.mul_self_sqrt hρ]

/-- **Scale-free logarithmic cross-block correlation bound.**
For any two dyadic blocks `S` (at `M`) and `S'` (at `M'`), the prime-weighted dilation correlation
is bounded by `5 K(A,B) (1 + log(1 + 6M/M'))² ‖b_S‖₂ ‖c_{S'}‖₂`, depending only on the scale ratio
`M / M'` and never growing as a power of `min(M, M')`. -/
theorem abs_sum_integral_crossBlock_logRatio_le {R : Finset ℕ} {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ r ∈ R, IntegrableOn (φ r) (Ioi 1)) {A B : ℝ}
    (hA : ∀ m f, |weightCosineTransform (φ m) f| ≤ A)
    (hB : ∀ m f, f ≠ 0 → |weightCosineTransform (φ m) f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (hR : ∀ r ∈ R, 2 ≤ r) {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b c : ℕ → ℝ) :
    |∑ r ∈ R, (Λ r : ℝ) / r * ∫ v in Ioi 1, φ r v *
        (realPhaseCombination S b v * realPhaseCombination S' c (r * v))| ≤
      5 * crossBlockConstant A B * (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2 *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', c n' ^ 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 0)
  have hW : 0 ≤ A + 16 * B := by positivity
  set Lr := 1 + Real.log (1 + 6 * (M : ℝ) / M')
  have hLr1 : 1 ≤ Lr :=
    le_add_of_nonneg_right (Real.log_nonneg (le_add_of_nonneg_right (by positivity)))
  set X := Real.sqrt (∑ n ∈ S, b n ^ 2)
  set Y := Real.sqrt (∑ n' ∈ S', c n' ^ 2)
  set C := 5 * 39 * (A + 16 * B) * Lr ^ 2 * X * Y
  have hC : 0 ≤ C := by positivity
  have hprod : Summable fun p : ℕ × ℕ => crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2 :=
    summable_crossBlockHarmonicSeries.mul_of_nonneg summable_crossBlockDualSeries
      crossBlockHarmonicSeries_nonneg crossBlockDualSeries_nonneg
  have h := abs_sum_integral_weight_dilate_le_of_bilinear (fun r => (Λ r : ℝ) / r)
    hφ S S' b c (μ := fun p => C * (crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2))
    (hprod.mul_left C) (fun p => mul_nonneg hC (mul_nonneg (crossBlockHarmonicSeries_nonneg _)
      (crossBlockDualSeries_nonneg _))) fun p hk hl => by
      have hb := abs_bilinear_crossBlock_spaced_le hA hB hB0 R hR hM hM' hS hS' b c hk hl
      have hk1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast hk
      have hl1 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hl
      have hk0 : (0 : ℝ) < p.1 := by linarith
      have hM'1 : (1 : ℝ) ≤ M' := by exact_mod_cast hM'
      have hlog_split : 1 + Real.log (1 + 6 * ((p.1 : ℝ) * M) / M') ≤
          (1 + Real.log (7 * p.1)) * Lr := by
        have hpos : (0 : ℝ) < 1 + 6 * ((p.1 : ℝ) * M) / M' := by positivity
        have hle : (1 : ℝ) + 6 * ((p.1 : ℝ) * M) / M' ≤ (7 * p.1) * (1 + 6 * (M : ℝ) / M') := by
          have : (0 : ℝ) ≤ 6 * ((p.1 : ℝ) * M) / M' := by positivity
          have : 6 * ((p.1 : ℝ) * M) / (M' : ℝ) = p.1 * (6 * (M : ℝ) / M') := by ring
          nlinarith
        have h1 : 1 + Real.log (1 + 6 * ((p.1 : ℝ) * M) / M') ≤
            1 + Real.log ((7 * p.1) * (1 + 6 * (M : ℝ) / M')) := by
          have := Real.log_le_log hpos hle
          linarith
        refine h1.trans ?_
        rw [Real.log_mul (by positivity) (by positivity)]
        have := Real.log_nonneg (show (1 : ℝ) ≤ 7 * p.1 by linarith)
        have := Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 6 * (M : ℝ) / M'))
        unfold Lr
        nlinarith
      have hlog_sq : (1 + Real.log (1 + 6 * ((p.1 : ℝ) * M) / M')) ^ 2 ≤
          (1 + Real.log (7 * p.1)) ^ 2 * Lr ^ 2 := by
        have h0 : 0 ≤ 1 + Real.log (1 + 6 * ((p.1 : ℝ) * M) / M') := by
          have := Real.log_nonneg
            (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 6 * ((p.1 : ℝ) * M) / M'))
          linarith
        calc (1 + Real.log (1 + 6 * ((p.1 : ℝ) * M) / M')) ^ 2
            ≤ ((1 + Real.log (7 * p.1)) * Lr) ^ 2 := pow_le_pow_left₀ h0 hlog_split 2
          _ = (1 + Real.log (7 * p.1)) ^ 2 * Lr ^ 2 := mul_pow _ _ 2
      have hfactor : (1 + Real.log (7 * p.1)) ^ 2 ≤ 15 * crossBlockHarmonicFactor p.1 p.2 := by
        have h7 : Real.log 7 ≤ 6 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)]
        have hr18 : (1 : ℝ) ≤ (p.1 : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
        have hlk := Real.log_le_rpow_div hk0.le (by norm_num : (0 : ℝ) < 1 / 8)
        rw [div_div_eq_mul_div, div_one] at hlk
        have hlog15 : 1 + Real.log (7 * p.1) ≤ 15 * (p.1 : ℝ) ^ (1 / 8 : ℝ) := by
          rw [Real.log_mul (by norm_num) hk0.ne']
          linarith
        have hrpow : (p.1 : ℝ) ^ (1 / 8 : ℝ) ≤ Real.sqrt (p.1 * Real.sqrt p.1) := by
          have hs : Real.sqrt (p.1 * Real.sqrt p.1) = (p.1 : ℝ) ^ (3 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow p.1, ← Real.rpow_one_add' hk0.le (by norm_num),
              Real.sqrt_eq_rpow, ← Real.rpow_mul hk0.le]
            norm_num
          rw [hs]
          exact Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
        have hsl : 1 ≤ Real.sqrt p.2 := by rw [Real.one_le_sqrt]; exact hl1
        have hlog_nn : 0 ≤ 1 + Real.log (7 * p.1) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 7 * p.1 by linarith)
          linarith
        unfold crossBlockHarmonicFactor
        calc (1 + Real.log (7 * p.1)) ^ 2
            = (1 + Real.log (7 * p.1)) * (1 + Real.log (7 * p.1)) := sq _
          _ ≤ (15 * (p.1 : ℝ) ^ (1 / 8 : ℝ)) * (1 + Real.log (7 * p.1)) :=
              mul_le_mul_of_nonneg_right hlog15 hlog_nn
          _ ≤ (15 * Real.sqrt (p.1 * Real.sqrt p.1)) * (1 + Real.log (7 * p.1)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow (by norm_num)) hlog_nn
          _ ≤ (15 * Real.sqrt (p.1 * Real.sqrt p.1) * Real.sqrt p.2) *
                (1 + Real.log (7 * p.1)) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hsl) hlog_nn
          _ = 15 * (Real.sqrt (p.1 * Real.sqrt p.1) * Real.sqrt p.2 *
                (1 + Real.log (7 * p.1))) := by ring
      have hb' : 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (p.1 * M) / M')) ^ 2 * X * Y ≤
          5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2 * X * Y := by
        have h1 : 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (p.1 * M) / M')) ^ 2 ≤
            5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2 := by
          calc 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (p.1 * M) / M')) ^ 2
              ≤ 12 * (A + 16 * B) * ((1 + Real.log (7 * p.1)) ^ 2 * Lr ^ 2) :=
                mul_le_mul_of_nonneg_left hlog_sq (by positivity)
            _ ≤ 12 * (A + 16 * B) * ((15 * crossBlockHarmonicFactor p.1 p.2) * Lr ^ 2) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hfactor (sq_nonneg Lr)) (by positivity)
            _ = 180 * ((A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2) := by ring
            _ ≤ 195 * ((A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2) :=
                mul_le_mul_of_nonneg_right (by norm_num)
                  (mul_nonneg (mul_nonneg hW (crossBlockHarmonicFactor_nonneg hk p.2))
                    (sq_nonneg Lr))
            _ = 5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2 := by ring
        calc 12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (p.1 * M) / M')) ^ 2 * X * Y
            = (12 * (A + 16 * B) * (1 + Real.log (1 + 6 * (p.1 * M) / M')) ^ 2) * (X * Y) := by
              ring
          _ ≤ (5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2) * (X * Y) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2 * X * Y := by ring
      have e : 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
          (5 * 39 * (A + 16 * B) * crossBlockHarmonicFactor p.1 p.2 * Lr ^ 2 * X * Y) =
          C * (crossBlockHarmonicSeries p.1 * crossBlockDualSeries p.2) := by
        simp only [C, crossBlockHarmonicSeries, crossBlockDualSeries, crossBlockHarmonicFactor]
        ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left (hb.trans hb') (by positivity)
  refine h.trans (le_of_eq ?_)
  have hn1 : Summable fun k : ℕ => ‖crossBlockHarmonicSeries k‖ :=
    summable_crossBlockHarmonicSeries.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖crossBlockDualSeries l‖ :=
    summable_crossBlockDualSeries.abs.congr fun l => (Real.norm_eq_abs _).symm
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hn1 hn2]
  simp only [crossBlockConstant, crossBlockHarmonicMass, C]
  ring

/-- **Scale-free logarithmic cross-block bound for compact doubly collared sources.**
For any two dyadic blocks `S` (at `M`) and `S'` (at `M'`), `|truncatedBlockCoupling V S S' b|`
depends only on the ratio `M / M'`, eliminating the `M^{3/4}` growth on adjacent blocks `M' = 2M`. -/
theorem abs_truncatedBlockCoupling_le_logRatio {V : ℝ} (hV : 0 < V)
    {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b : ℕ → ℝ) :
    |truncatedBlockCoupling V S S' b| ≤
      5 * truncatedCrossBlockConstant * (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2 *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2) := by
  have hl (m : ℕ) : 0 ≤ (m : ℝ) / V := by positivity
  have hA := fun m f => (abs_weightCosineTransform_criticalTruncatedWeight_le (hl m)).1 f
  have hB := fun m f hf => (abs_weightCosineTransform_criticalTruncatedWeight_le (hl m)).2 f hf
  have hφ : ∀ r ∈ truncationDilations V,
      IntegrableOn (criticalTruncatedWeight ((r : ℝ) / V)) (Ioi 1) :=
    fun r _ => integrableOn_criticalTruncatedWeight _
  have hR := fun r hr => two_le_of_mem_truncationDilations (V := V) (r := r) hr
  exact abs_sum_integral_crossBlock_logRatio_le hφ hA hB criticalTruncatedCurvature_nonneg
    hR hM hM' hS hS' b b

/-- **Uniform `O(1)` upward cross-block bound for compact doubly collared sources.**
Whenever `1 ≤ M ≤ M'` (the larger block `S'` at `M'` is dilated by `r ≥ 2`), the cross-block
coupling `|truncatedBlockCoupling V S S' b|` is uniformly bounded by
`245 K_CB ‖b_S‖₂ ‖b_{S'}‖₂` for all `M ≤ M'` (including adjacent blocks `M' = 2M`). -/
theorem abs_truncatedBlockCoupling_up_uniform_le {V : ℝ} (hV : 0 < V)
    {S S' : Finset ℕ} {M M' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M')
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (b : ℕ → ℝ) :
    |truncatedBlockCoupling V S S' b| ≤
      245 * truncatedCrossBlockConstant *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2) := by
  have hM' : 1 ≤ M' := hM.trans hMM
  refine (abs_truncatedBlockCoupling_le_logRatio hV hM hM' hS hS' b).trans ?_
  have hMM' : (M : ℝ) ≤ M' := by exact_mod_cast hMM
  have hM'0 : (0 : ℝ) < M' := by exact_mod_cast hM'
  have hdiv : 6 * (M : ℝ) / M' ≤ 6 := by
    rw [div_le_iff₀ hM'0]; linarith
  have hlog7 : Real.log (1 + 6 * (M : ℝ) / M') ≤ 6 := by
    calc Real.log (1 + 6 * (M : ℝ) / M')
        ≤ Real.log 7 := Real.log_le_log (by positivity) (by linarith)
      _ ≤ 6 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)]
  have h0 : 0 ≤ 1 + Real.log (1 + 6 * (M : ℝ) / M') := by
    have := Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 6 * (M : ℝ) / M'))
    linarith
  have hsq : (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2 ≤ 49 := by
    calc (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2
        ≤ (1 + 6 : ℝ) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
      _ = 49 := by norm_num
  have hK := truncatedCrossBlockConstant_nonneg
  have hXY : 0 ≤ Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2) := by positivity
  calc 5 * truncatedCrossBlockConstant * (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2 *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2)
      = 5 * truncatedCrossBlockConstant * (1 + Real.log (1 + 6 * (M : ℝ) / M')) ^ 2 *
          (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2)) := by ring
    _ ≤ 5 * truncatedCrossBlockConstant * 49 *
          (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) hXY
    _ = 245 * truncatedCrossBlockConstant *
          Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n' ∈ S', b n' ^ 2) := by ring

/-! ## Section 3: Arithmetic Congruence Resonance Structure and the `√M` Collar-Drift Boundary -/

/-- **Harmonic affine-defect decomposition of the factorial cubic clock.**
For harmonic indices `k, l` and dilation `r`, the shifted-frequency difference splits into the
integer part `k(n+1) - lr(n'+1)`, the constant `1/12` offset `(k - lr)/12`, and the dilated
affine collar defects `lr · e_{n'+1} - k · e_{n+1}`. -/
theorem harmonic_factorialShiftedFreq_affine_gap (k l r n n' : ℕ) :
    (k : ℝ) * factorialShiftedFreq (n + 1) -
        ((l * r : ℕ) : ℝ) * factorialShiftedFreq (n' + 1) =
      ((k : ℝ) * (n + 1 : ℝ) - ((l * r : ℕ) : ℝ) * (n' + 1 : ℝ)) +
        ((k : ℝ) - ((l * r : ℕ) : ℝ)) / 12 +
        ((l * r : ℕ) : ℝ) * factorialAffineDefect (n' + 1) -
        (k : ℝ) * factorialAffineDefect (n + 1) := by
  unfold factorialAffineDefect
  push_cast
  ring

/-- **Modular progression spacing of resonant scales (`k(n+1) ≡ j (mod q)`).**
If two distinct scales `n₁ ≠ n₂` lie in the same harmonic congruence class modulo `q = l r ≥ 1`
(i.e. `(k * (n₁ + 1)) % q = (k * (n₂ + 1)) % q`), then their distance `|n₁ - n₂|` is at least
`q / gcd(k, q)`. In particular, when `Nat.Coprime k q`, resonant scales in a fixed congruence
class are separated by at least `q = l r`. -/
theorem resonant_scale_mod_eq_and_spacing {k q n₁ n₂ : ℕ} (hq : 1 ≤ q)
    (hmod : (k * (n₁ + 1)) % q = (k * (n₂ + 1)) % q) (hne : n₁ ≠ n₂) :
    q / Nat.gcd k q ≤ Nat.dist n₁ n₂ ∧
    (Nat.Coprime k q → q ≤ Nat.dist n₁ n₂) := by
  have hkey : ∀ a b : ℕ, b < a → (k * (a + 1)) % q = (k * (b + 1)) % q →
      q / Nat.gcd k q ≤ a - b := by
    intro a b hlt hm
    have hle : k * (b + 1) ≤ k * (a + 1) := Nat.mul_le_mul_left k (by omega)
    have hdvd : q ∣ k * (a - b) := by
      have hsub : k * (a + 1) - k * (b + 1) = k * (a - b) := by
        rw [← Nat.mul_sub_left_distrib]
        congr 1
        omega
      rw [← hsub]
      exact (Nat.modEq_iff_dvd' hle).mp hm.symm
    set g := Nat.gcd k q
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right k (by omega)
    have hq_eq : q = g * (q / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right k q)).symm
    have hk_eq : k = g * (k / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left k q)).symm
    have hdvd' : g * (q / g) ∣ g * ((k / g) * (a - b)) := by
      calc g * (q / g) = q := hq_eq.symm
        _ ∣ k * (a - b) := hdvd
        _ = (g * (k / g)) * (a - b) := by rw [← hk_eq]
        _ = g * ((k / g) * (a - b)) := by ring
    have hdvd_cop : q / g ∣ (k / g) * (a - b) :=
      Nat.dvd_of_mul_dvd_mul_left hg_pos hdvd'
    have hcop : Nat.Coprime (q / g) (k / g) :=
      (Nat.coprime_div_gcd_div_gcd hg_pos).symm
    have hdvd_diff : q / g ∣ a - b := hcop.dvd_of_dvd_mul_left hdvd_cop
    exact Nat.le_of_dvd (by omega) hdvd_diff
  have h1 : q / Nat.gcd k q ≤ Nat.dist n₁ n₂ := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Nat.dist_eq_sub_of_le hlt.le]
      exact hkey n₂ n₁ hlt hmod.symm
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hgt.le]
      exact hkey n₁ n₂ hgt hmod
  refine ⟨h1, fun hcop => ?_⟩
  rw [hcop.gcd_eq_one, Nat.div_one] at h1
  exact h1

/-- **Two-sided dilated affine defect bounds on a scale window `[M, LM]` and the `√M` boundary.**
For any `n' ∈ S` on a scale window `ScaleWindow S M L` (`M, L ≥ 1`) and any dilation `1 ≤ r ≤ L`:
1. `(r : ℝ) / (225 * L * M) ≤ r · factorialAffineDefect (n' + 1) ≤ (r : ℝ) / (140 * M) ≤ L / (140 * M)`.
2. Across any progression of `r`-step size `r ≤ L` inside the window, `r · factorialAffineDefect (n' + 1)`
   is bounded by `L² / (140 * M)`, which is at most `1 / 140` whenever `L² ≤ M` (the square-root
   window regime `L ≤ √M`). -/
theorem dilated_factorialAffineDefect_window_bounds {S : Finset ℕ} {M L r n' : ℕ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (hn' : n' ∈ S)
    (hr1 : 1 ≤ r) (hrL : r ≤ L) :
    (r : ℝ) / (225 * (L : ℝ) * (M : ℝ)) ≤ (r : ℝ) * factorialAffineDefect (n' + 1) ∧
    (r : ℝ) * factorialAffineDefect (n' + 1) ≤ (r : ℝ) / (140 * (M : ℝ)) ∧
    (r : ℝ) / (140 * (M : ℝ)) ≤ (L : ℝ) ^ 2 / (140 * (M : ℝ)) ∧
    (L ^ 2 ≤ M → (r : ℝ) * factorialAffineDefect (n' + 1) ≤ 1 / 140) := by
  obtain ⟨hlow_n, hhigh_n⟩ := hS n' hn'
  obtain ⟨hdef_low, hdef_high⟩ := factorialAffineDefect_bounds n'
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrL_real : (r : ℝ) ≤ L := by exact_mod_cast hrL
  have hL1_real : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn_low : (M : ℝ) ≤ (n' : ℝ) + 1 := by exact_mod_cast hlow_n
  have hn_high : (n' : ℝ) + 1 ≤ (L : ℝ) * (M : ℝ) := by exact_mod_cast hhigh_n
  have h1 : (r : ℝ) / (225 * (L : ℝ) * (M : ℝ)) ≤ (r : ℝ) * factorialAffineDefect (n' + 1) := by
    calc (r : ℝ) / (225 * (L : ℝ) * (M : ℝ))
        = (r : ℝ) * (1 / (225 * ((L : ℝ) * (M : ℝ)))) := by ring
      _ ≤ (r : ℝ) * (1 / (225 * ((n' : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity) (by nlinarith)) hr0.le
      _ ≤ (r : ℝ) * factorialAffineDefect (n' + 1) :=
          mul_le_mul_of_nonneg_left hdef_low hr0.le
  have h2 : (r : ℝ) * factorialAffineDefect (n' + 1) ≤ (r : ℝ) / (140 * (M : ℝ)) := by
    calc (r : ℝ) * factorialAffineDefect (n' + 1)
        ≤ (r : ℝ) * (1 / (140 * ((n' : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hdef_high hr0.le
      _ ≤ (r : ℝ) * (1 / (140 * (M : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity) (by nlinarith)) hr0.le
      _ = (r : ℝ) / (140 * (M : ℝ)) := by ring
  have h3 : (r : ℝ) / (140 * (M : ℝ)) ≤ (L : ℝ) ^ 2 / (140 * (M : ℝ)) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith
  refine ⟨h1, h2, h3, fun hsq => ?_⟩
  have hsq_real : (L : ℝ) ^ 2 ≤ M := by exact_mod_cast hsq
  calc (r : ℝ) * factorialAffineDefect (n' + 1)
      ≤ (L : ℝ) ^ 2 / (140 * (M : ℝ)) := h2.trans h3
    _ ≤ (M : ℝ) / (140 * (M : ℝ)) := div_le_div_of_nonneg_right hsq_real (by positivity)
    _ = 1 / 140 := by field_simp

/-! ## Section 4: Lacunary Families of Polynomial Scale Windows & Arbitrary-Width Dense Windows -/

/-- Dyadic slice exponents `k` covering a scale window `[M, LM]`, characterized by
`M < 2^(k + 1)` and `2^k ≤ L * M`. -/
def windowDyadicIndices (M L : ℕ) : Finset ℕ :=
  (Finset.range (L * M + 1)).filter (fun k => M < 2 ^ (k + 1) ∧ 2 ^ k ≤ L * M)

/-- Every scale window `ScaleWindow S M L` is the disjoint union of `dyadicSlice S k` over
`k ∈ windowDyadicIndices M L`. -/
theorem biUnion_dyadicSlice_windowDyadicIndices {S : Finset ℕ} {M L : ℕ}
    (hS : ScaleWindow S M L) :
    (windowDyadicIndices M L).biUnion (dyadicSlice S) = S := by
  ext n
  simp only [Finset.mem_biUnion, windowDyadicIndices, dyadicSlice, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨_, _, hn, _⟩
    exact hn
  · intro hn
    obtain ⟨h1, h2⟩ := hS n hn
    set k := Nat.log 2 (n + 1)
    have hk_le : 2 ^ k ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have hk_lt : n + 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have hk_self : k < 2 ^ k := Nat.lt_two_pow_self
    refine ⟨k, ⟨by omega, by omega, by omega⟩, hn, hk_le, hk_lt⟩

/-- For any finite set `K : Finset ℕ` of dyadic exponents, the squared lacunary weights
`(((2^k)^{1/16})⁻¹)² = (2^k)^{-1/8}` sum to at most `13`. -/
theorem sum_finset_dyadic_weight_sq_le (K : Finset ℕ) :
    ∑ k ∈ K, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 ≤ 13 := by
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
  set N := K.sup id + 1
  have hsub : K ⊆ Finset.range N := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  calc ∑ k ∈ K, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2
      ≤ ∑ k ∈ Finset.range N, ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ k ∈ Finset.range N, (12 / 13 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ((12 / 13 : ℝ) ^ N - 1) / (12 / 13 - 1) :=
        geom_sum_eq (by norm_num) N
    _ ≤ 13 := by
        have hpos : 0 ≤ (12 / 13 : ℝ) ^ N := by positivity
        have hsub' : ((12 / 13 : ℝ) ^ N - 1) / (12 / 13 - 1) =
            13 * (1 - (12 / 13 : ℝ) ^ N) := by ring
        linarith

/-- If `(L * M)^8 ≤ M'`, every dyadic slice exponent `k ∈ windowDyadicIndices M L` and
`k' ∈ windowDyadicIndices M' L'` satisfy `8 * k ≤ k'` and `(2^k)^8 ≤ 2^{k'}`. -/
theorem windowDyadicIndices_pow_le {M L M' L' k k' : ℕ} (hsep : (L * M) ^ 8 ≤ M')
    (hk : k ∈ windowDyadicIndices M L) (hk' : k' ∈ windowDyadicIndices M' L') :
    8 * k ≤ k' ∧ (2 ^ k) ^ 8 ≤ 2 ^ k' := by
  have hk_le : 2 ^ k ≤ L * M := (Finset.mem_filter.mp hk).2.2
  have hk'_lt : M' < 2 ^ (k' + 1) := (Finset.mem_filter.mp hk').2.1
  have hpow_lt : 2 ^ (8 * k) < 2 ^ (k' + 1) := by
    calc 2 ^ (8 * k) = (2 ^ k) ^ 8 := by rw [mul_comm, pow_mul]
      _ ≤ (L * M) ^ 8 := Nat.pow_le_pow_left hk_le 8
      _ ≤ M' := hsep
      _ < 2 ^ (k' + 1) := hk'_lt
  have hlt : 8 * k < k' + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
  have hle : 8 * k ≤ k' := by omega
  refine ⟨hle, ?_⟩
  rw [← pow_mul, mul_comm k 8]
  exact Nat.pow_le_pow_right (by norm_num) hle

/-- A **lacunary family of scale windows**: for `i < J`, `W_i` is a scale window `[M_i, L_i M_i]`
with `M_0 ≥ 3`, `L_i ≥ 1`, and `(L_i M_i)^8 ≤ M_{i+1}`. When `L_i = 2`, this recovers
`IsLacunaryBlockFamily`; when `L_i ≤ M_i^δ`, each `W_i` is a full polynomial scale window. -/
def IsLacunaryWindowFamily (J : ℕ) (M L : ℕ → ℕ) (W : ℕ → Finset ℕ) : Prop :=
  3 ≤ M 0 ∧
  (∀ i < J, 1 ≤ L i) ∧
  (∀ i, i + 1 < J → (L i * M i) ^ 8 ≤ M (i + 1)) ∧
  ∀ i < J, ScaleWindow (W i) (M i) (L i)

namespace IsLacunaryWindowFamily

variable {J : ℕ} {M L : ℕ → ℕ} {W : ℕ → Finset ℕ}

theorem three_le (h : IsLacunaryWindowFamily J M L W) : ∀ i < J, 3 ≤ M i := by
  intro i
  induction i with
  | zero => intro _; exact h.1
  | succ i ih =>
    intro hi
    have hM : 3 ≤ M i := ih (by omega)
    have hL : 1 ≤ L i := h.2.1 i (by omega)
    have hLM : M i ≤ L i * M i := Nat.le_mul_of_pos_left _ hL
    calc 3 ≤ M i := hM
      _ ≤ L i * M i := hLM
      _ ≤ (L i * M i) ^ 8 := Nat.le_self_pow (by norm_num) _
      _ ≤ M (i + 1) := h.2.2.1 i hi

theorem pow_le (h : IsLacunaryWindowFamily J M L W) {i i' : ℕ} (hii : i < i') (hi' : i' < J) :
    (L i * M i) ^ 8 ≤ M i' := by
  obtain ⟨d, rfl⟩ : ∃ d, i' = i + 1 + d := ⟨i' - (i + 1), by omega⟩
  induction d with
  | zero => exact h.2.2.1 i (by omega)
  | succ d ih =>
    have hL : 1 ≤ L (i + 1 + d) := h.2.1 (i + 1 + d) (by omega)
    calc (L i * M i) ^ 8 ≤ M (i + 1 + d) := ih (by omega) (by omega)
      _ ≤ L (i + 1 + d) * M (i + 1 + d) := Nat.le_mul_of_pos_left _ hL
      _ ≤ (L (i + 1 + d) * M (i + 1 + d)) ^ 8 := Nat.le_self_pow (by norm_num) _
      _ ≤ M (i + 1 + (d + 1)) := h.2.2.1 _ (by omega)

theorem le_of_lt (h : IsLacunaryWindowFamily J M L W) {i i' : ℕ} (hii : i < i') (hi' : i' < J) :
    M i ≤ M i' := by
  have hL : 1 ≤ L i := h.2.1 i (by omega)
  exact (Nat.le_mul_of_pos_left _ hL).trans
    ((Nat.le_self_pow (by norm_num) _).trans (h.pow_le hii hi'))

theorem pairwiseDisjoint (h : IsLacunaryWindowFamily J M L W) :
    ((Finset.range J : Finset ℕ) : Set ℕ).PairwiseDisjoint W := by
  intro i hi i' hi' hne
  simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
  have key : ∀ j j', j < j' → j' < J → Disjoint (W j) (W j') := by
    intro j j' hjj hj'
    rw [Finset.disjoint_left]
    intro n hn hn'
    have h1 := (h.2.2.2 j (by omega) n hn).2
    have h2 := (h.2.2.2 j' hj' n hn').1
    have h3 := h.three_le j (by omega)
    have hL := h.2.1 j (by omega)
    have h8 := h.pow_le hjj hj'
    have hLM : 3 ≤ L j * M j := by nlinarith
    have hlt : L j * M j < (L j * M j) ^ 8 := by
      calc L j * M j = (L j * M j) ^ 1 := (pow_one _).symm
        _ < (L j * M j) ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i i' hlt hi'
  · exact (key i' i hlt hi).symm

theorem lower (h : IsLacunaryWindowFamily J M L W) {n : ℕ}
    (hn : n ∈ (Finset.range J).biUnion W) :
    M 0 ≤ n + 1 := by
  obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
  have hi := Finset.mem_range.mp hi
  have hb := (h.2.2.2 i hi n hn).1
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hb
  · exact (h.le_of_lt hpos hi).trans hb

/-- The dyadic index sets `windowDyadicIndices (M i) (L i)` across distinct windows `i ≠ i'` are
disjoint. -/
theorem pairwiseDisjoint_windowDyadicIndices (h : IsLacunaryWindowFamily J M L W) :
    ((Finset.range J : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => windowDyadicIndices (M i) (L i)) := by
  intro i hi i' hi' hne
  simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
  have key : ∀ j j', j < j' → j' < J →
      Disjoint (windowDyadicIndices (M j) (L j)) (windowDyadicIndices (M j') (L j')) := by
    intro j j' hjj hj'
    rw [Finset.disjoint_left]
    intro k hk hk'
    have hsep := h.pow_le hjj hj'
    have h8 := (windowDyadicIndices_pow_le hsep hk hk').1
    have h3 := h.three_le j (by omega)
    have hk_lt : M j < 2 ^ (k + 1) := (Finset.mem_filter.mp hk).2.1
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0] at hk_lt
      omega
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i i' hlt hi'
  · exact (key i' i hlt hi).symm

end IsLacunaryWindowFamily

/-- **Prime channel bound on a lacunary family of scale windows.**
For every `IsLacunaryWindowFamily J M L W` and every `V > 0`:
1. The diagonal window couplings are bounded by the direct (`ε`-free) single-window law
   `directTruncatedWindowPrimeSlope * (log (L i) + windowRingMajorantUpperOffset) * E_i`.
2. The sum of all off-diagonal cross-window couplings (`i ≠ i'`) is bounded by
   `650 * truncatedCrossBlockConstant * ∑_i E_i`, completely independently of the window widths
   `L_i`, the number of windows `J`, and the truncation `V`. -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_lacunaryWindows {V : ℝ} (hV : 0 < V)
    {J : ℕ} {M L : ℕ → ℕ} {W : ℕ → Finset ℕ} (h : IsLacunaryWindowFamily J M L W) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V ((Finset.range J).biUnion W) b| ≤
      ∑ i ∈ Finset.range J,
        (directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset) +
          650 * truncatedCrossBlockConstant) * ∑ n ∈ W i, b n ^ 2 := by
  set I := Finset.range J
  set K_idx : ℕ → Finset ℕ := fun i => windowDyadicIndices (M i) (L i)
  set X_slice : ℕ → ℕ → ℝ := fun i k => ∑ n ∈ dyadicSlice (W i) k, b n ^ 2
  set s_slice : ℕ → ℕ → ℝ := fun i k => Real.sqrt (X_slice i k)
  set w : ℕ → ℝ := fun k => ((((2 ^ k : ℕ) : ℝ) ^ (1 / 16 : ℝ))⁻¹)
  set A_win : ℕ → ℝ := fun i => ∑ k ∈ K_idx i, w k * s_slice i k
  set X_win : ℕ → ℝ := fun i => ∑ n ∈ W i, b n ^ 2
  set K := truncatedCrossBlockConstant
  have hK : 0 ≤ K := truncatedCrossBlockConstant_nonneg
  have hX_slice (i k : ℕ) : 0 ≤ X_slice i k := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hX_win (i : ℕ) : 0 ≤ X_win i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw (k : ℕ) : 0 ≤ w k := by simp only [w]; positivity
  have hA_win (i : ℕ) : 0 ≤ A_win i := Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (Real.sqrt_nonneg _)
  have hd_W := h.pairwiseDisjoint
  have hd_K := h.pairwiseDisjoint_windowDyadicIndices
  have hX_eq : ∀ i ∈ I, X_win i = ∑ k ∈ K_idx i, X_slice i k := by
    intro i hi
    have hi_lt := Finset.mem_range.mp hi
    have hbi := biUnion_dyadicSlice_windowDyadicIndices (h.2.2.2 i hi_lt)
    calc X_win i = ∑ n ∈ (K_idx i).biUnion (dyadicSlice (W i)), b n ^ 2 := by
          dsimp only [X_win, K_idx]; rw [hbi]
      _ = ∑ k ∈ K_idx i, X_slice i k :=
          Finset.sum_biUnion (pairwiseDisjoint_dyadicSlice (W i) _)
  -- diagonal window bounds
  have hdiag : ∀ i ∈ I,
      |truncatedBlockCoupling V (W i) (W i) b| ≤
        directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset) *
          X_win i := by
    intro i hi
    have hi_lt := Finset.mem_range.mp hi
    rw [truncatedBlockCoupling_self hV]
    have hM1 : 1 ≤ M i := by have := h.three_le i hi_lt; omega
    exact (abs_criticalTruncatedPrimeEnergy_le_of_window_direct hV hM1
      (h.2.1 i hi_lt) (h.2.2.2 i hi_lt) b).2
  -- off-diagonal window couplings via dyadic slices
  have hoff : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' →
      |truncatedBlockCoupling V (W i) (W i') b| ≤ 50 * K * A_win i * A_win i' := by
    intro i hi i' hi' hne
    have hi_lt := Finset.mem_range.mp hi
    have hi'_lt := Finset.mem_range.mp hi'
    have hbi_i : (K_idx i).biUnion (dyadicSlice (W i)) = W i :=
      biUnion_dyadicSlice_windowDyadicIndices (h.2.2.2 i hi_lt)
    have hbi_i' : (K_idx i').biUnion (dyadicSlice (W i')) = W i' :=
      biUnion_dyadicSlice_windowDyadicIndices (h.2.2.2 i' hi'_lt)
    have hd_i := pairwiseDisjoint_dyadicSlice (W i) (K_idx i : Set ℕ)
    have hd_i' := pairwiseDisjoint_dyadicSlice (W i') (K_idx i' : Set ℕ)
    have hpair : ∀ k ∈ K_idx i, ∀ k' ∈ K_idx i',
        |truncatedBlockCoupling V (dyadicSlice (W i) k) (dyadicSlice (W i') k') b| ≤
          50 * K * (w k * s_slice i k) * (w k' * s_slice i' k') := by
      intro k hk k' hk'
      have hlac : (2 ^ k) ^ 8 ≤ 2 ^ k' ∨ (2 ^ k') ^ 8 ≤ 2 ^ k := by
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl (windowDyadicIndices_pow_le (h.pow_le hlt hi'_lt) hk hk').2
        · exact Or.inr (windowDyadicIndices_pow_le (h.pow_le hlt hi_lt) hk' hk).2
      have h1 := abs_truncatedBlockCoupling_le_of_pow_le hV
        (dyadicScaleBlock_dyadicSlice (W i) k) (dyadicScaleBlock_dyadicSlice (W i') k')
        Nat.one_le_two_pow Nat.one_le_two_pow hlac b
      exact h1.trans (le_of_eq (by dsimp only [w, s_slice, X_slice, K]; ring))
    conv_lhs => rw [← hbi_i, ← hbi_i']
    rw [truncatedBlockCoupling_biUnion_left V hd_i]
    have hinner (k : ℕ) :
        truncatedBlockCoupling V (dyadicSlice (W i) k)
          ((K_idx i').biUnion (dyadicSlice (W i'))) b =
        ∑ k' ∈ K_idx i',
          truncatedBlockCoupling V (dyadicSlice (W i) k) (dyadicSlice (W i') k') b :=
      truncatedBlockCoupling_biUnion_right V (dyadicSlice (W i) k) hd_i' b
    simp_rw [hinner]
    calc |∑ k ∈ K_idx i, ∑ k' ∈ K_idx i',
            truncatedBlockCoupling V (dyadicSlice (W i) k) (dyadicSlice (W i') k') b|
        ≤ ∑ k ∈ K_idx i, ∑ k' ∈ K_idx i',
            |truncatedBlockCoupling V (dyadicSlice (W i) k) (dyadicSlice (W i') k') b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ K_idx i, ∑ k' ∈ K_idx i',
            50 * K * (w k * s_slice i k) * (w k' * s_slice i' k') :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun k' hk' => hpair k hk k' hk'
      _ = 50 * K * A_win i * A_win i' := by
          dsimp only [A_win]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- global Cauchy-Schwarz across all disjoint dyadic indices `⋃_{i < J} K_idx i`
  have hA_sum_sq : (∑ i ∈ I, A_win i) ^ 2 ≤ 13 * ∑ i ∈ I, X_win i := by
    set S_global : ℕ → ℝ := fun k =>
      ∑ i ∈ I, if k ∈ K_idx i then s_slice i k else 0
    have hS_val : ∀ i ∈ I, ∀ k ∈ K_idx i, S_global k = s_slice i k := by
      intro i hi k hk
      dsimp only [S_global]
      rw [Finset.sum_eq_single i]
      · exact if_pos hk
      · intro j hj hne
        have hnot : k ∉ K_idx j :=
          Finset.disjoint_left.mp (hd_K hi hj hne.symm) hk
        exact if_neg hnot
      · intro hnot; exact absurd hi hnot
    have hsum_eq : ∑ i ∈ I, A_win i = ∑ k ∈ I.biUnion K_idx, w k * S_global k := by
      rw [Finset.sum_biUnion hd_K]
      refine Finset.sum_congr rfl fun i hi => ?_
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hS_val i hi k hk]
    have hS_sq : ∀ i ∈ I, ∀ k ∈ K_idx i, (S_global k) ^ 2 = X_slice i k := by
      intro i hi k hk
      rw [hS_val i hi k hk, Real.sq_sqrt (hX_slice i k)]
    have hsum_S_sq : ∑ k ∈ I.biUnion K_idx, (S_global k) ^ 2 = ∑ i ∈ I, X_win i := by
      rw [Finset.sum_biUnion hd_K]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hX_eq i hi]
      exact Finset.sum_congr rfl fun k hk => hS_sq i hi k hk
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (I.biUnion K_idx) w S_global
    rw [← hsum_eq, hsum_S_sq] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right
      (sum_finset_dyadic_weight_sq_le (I.biUnion K_idx))
      (Finset.sum_nonneg fun i _ => hX_win i))
  have hoff_sum : |∑ i ∈ I, ∑ i' ∈ I.erase i, truncatedBlockCoupling V (W i) (W i') b| ≤
      650 * K * ∑ i ∈ I, X_win i := by
    calc |∑ i ∈ I, ∑ i' ∈ I.erase i, truncatedBlockCoupling V (W i) (W i') b|
        ≤ ∑ i ∈ I, ∑ i' ∈ I.erase i, 50 * K * A_win i * A_win i' :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i' hi' =>
              hoff i hi i' (Finset.mem_of_mem_erase hi') (Finset.ne_of_mem_erase hi').symm))
      _ ≤ ∑ i ∈ I, ∑ i' ∈ I, 50 * K * A_win i * A_win i' :=
          Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun i' _ _ =>
              mul_nonneg (mul_nonneg (by positivity) (hA_win i)) (hA_win i')
      _ = 50 * K * (∑ i ∈ I, A_win i) ^ 2 := by
          symm
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
      _ ≤ 50 * K * (13 * ∑ i ∈ I, X_win i) :=
          mul_le_mul_of_nonneg_left hA_sum_sq (by positivity)
      _ = 650 * K * ∑ i ∈ I, X_win i := by ring
  have hsplit : ∑ i ∈ I, ∑ i' ∈ I, truncatedBlockCoupling V (W i) (W i') b =
      ∑ i ∈ I, truncatedBlockCoupling V (W i) (W i) b +
        ∑ i ∈ I, ∑ i' ∈ I.erase i, truncatedBlockCoupling V (W i) (W i') b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (Finset.add_sum_erase I _ hi).symm
  have hdiag_sum : |∑ i ∈ I, truncatedBlockCoupling V (W i) (W i) b| ≤
      ∑ i ∈ I, directTruncatedWindowPrimeSlope *
        (Real.log (L i) + windowRingMajorantUpperOffset) * X_win i :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hdiag)
  rw [criticalTruncatedPrimeEnergy_biUnion hV hd_W, hsplit]
  refine (abs_add_le _ _).trans ((add_le_add hdiag_sum hoff_sum).trans (le_of_eq ?_))
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by dsimp only [X_win, K]; ring

/-- **Complete energy lower bound across a lacunary family of scale windows.**
For every `IsLacunaryWindowFamily J M L W` and every truncation `V ≥ criticalTruncationThreshold`,
the complete energy on `⋃_{i < J} W_i` dominates
`∑_{i < J} (s_T (log (M 0) - c_T) - K_{T,0} - 1300 K_CB - 2 C_{TW,direct} (log (L i) + C_ring)) E_i`. -/
theorem criticalTruncatedCompleteEnergy_ge_of_lacunaryWindows {J : ℕ} {M L : ℕ → ℕ}
    {W : ℕ → Finset ℕ} (h : IsLacunaryWindowFamily J M L W) (b : ℕ → ℝ)
    {V : ℝ} (hV : criticalTruncationThreshold ≤ V) :
    (((∑ i ∈ Finset.range J,
        (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
          criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
          2 * directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset)) *
            ∑ n ∈ W i, b n ^ 2) : ℝ) : EReal) ≤
      criticalTruncatedCompleteEnergy V ((Finset.range J).biUnion W) b := by
  set I := Finset.range J
  set T := I.biUnion W
  set E := ∑ n ∈ T, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE_eq : E = ∑ i ∈ I, ∑ n ∈ W i, b n ^ 2 := Finset.sum_biUnion h.pairwiseDisjoint
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hV0 : 0 < V := by linarith
  have hM : 2 ≤ M 0 := by have := h.1; omega
  have hM0 : (2 : ℝ) ≤ M 0 := by exact_mod_cast hM
  set X := criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V T b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy T b hM (fun n hn => h.lower hn) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  set Tr := ∑ n ∈ T, |b n| / ((n + 1 : ℕ) : ℝ)
  set ac := sourceAutocorrelation (criticalTruncatedSource V T b) 0
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V T b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 := neg_abs_le (EF.gammaBracket 0 * ac)
    rw [abs_mul, abs_of_nonneg hac0] at h1
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le T b hM fun n hn => h.lower hn
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
  have hpol : |criticalTruncatedPolarReadout V T b * criticalTruncatedPolarEndpoint V T b| ≤
      144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalTruncatedPolarReadout_le hV0 T b
    have h2 := abs_criticalTruncatedPolarEndpoint_le hV1 T b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : Tr ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M 0 : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      dsimp only [E]
      nlinarith)
    calc _ ≤ a * (12 * Tr) * (c * (12 * Tr)) := h12
      _ = 144 * a * c * Tr ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := (abs_le.mp (abs_criticalTruncatedPrimeEnergy_le_of_lacunaryWindows hV0 h b)).2
  have hpol' := (abs_le.mp hpol).1
  set Z := ∑ i ∈ I,
    (criticalTruncatedWindowBaseConstant +
      2 * (directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset) +
        650 * truncatedCrossBlockConstant)) * ∑ n ∈ W i, b n ^ 2
  have hZ_eq : Z = criticalTruncatedWindowBaseConstant * E +
      2 * ∑ i ∈ I,
        (directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset) +
          650 * truncatedCrossBlockConstant) * ∑ n ∈ W i, b n ^ 2 := by
    unfold Z
    rw [hE_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hch : -Z ≤ EF.gammaBracket 0 * ac +
      2 * (criticalTruncatedPolarReadout V T b * criticalTruncatedPolarEndpoint V T b) -
      2 * criticalTruncatedPrimeEnergy V T b := by
    rw [hZ_eq]
    unfold criticalTruncatedWindowBaseConstant
    linarith
  have htot_eq : (∑ i ∈ I,
      (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
        2 * directTruncatedWindowPrimeSlope * (Real.log (L i) + windowRingMajorantUpperOffset)) *
          ∑ n ∈ W i, b n ^ 2) = X + -Z := by
    unfold X Z
    rw [hE_eq, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold criticalTruncatedCompleteEnergy
  rw [htot_eq, EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Unconditional Positivity Across Lacunary Families of Polynomial Scale Windows in All Five
Form Realizations (`compactFullWeilEnergy`, `fullZeroForm`, `weilFullFunctional`,
`zetaZeroConfig.W`, and `configurationSquareMass - configurationReflectionDefect`).**
For `δ = s_T / (4 (directTruncatedWindowPrimeSlope + 1)) > 0`, there exists `M₀` such that for
every `IsLacunaryWindowFamily J M L W` with `M₀ ≤ M 0` and `(L i : ℝ) ≤ (M 0 : ℝ)^δ` (`i < J`),
every truncation `V ≥ criticalTruncationThreshold`, and every nonzero `b` on `⋃_{i < J} W_i`,
all five form realizations and their single-scale `gridTentPattern` / `smoothGridTentDetector`
transfers are unconditionally strictly positive with explicit `(s_T / 4) log (M 0) ∑ b_n²` margin. -/
theorem exists_lacunaryPolynomialWindows_all_five_forms_pos :
    let δ : ℝ := criticalTruncatedArchLogSlope / (4 * (directTruncatedWindowPrimeSlope + 1))
    0 < δ ∧ ∃ M₀ : ℕ, ∀ (J : ℕ) (M L : ℕ → ℕ) (W : ℕ → Finset ℕ),
      IsLacunaryWindowFamily J M L W → M₀ ≤ M 0 →
      (∀ i < J, (L i : ℝ) ≤ (M 0 : ℝ) ^ δ) →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ b : ℕ → ℝ, (∃ n ∈ (Finset.range J).biUnion W, b n ≠ 0) →
          let T : Finset ℕ := (Finset.range J).biUnion W
          let R : ℝ := Real.log (2 * V)
          let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos T b x
          let μ : ℝ := criticalTruncatedArchLogSlope / 8 * Real.log (M 0) * ∑ n ∈ T, b n ^ 2
          0 < μ ∧
          2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
          compactFullWeilEnergy (criticalTruncatedTest hVpos T b) =
            fullZeroForm (criticalTruncatedTest hVpos T b) ∧
          ∀ᶠ n : ℕ in atTop,
            let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
            let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
            μ ≤ compactFullWeilEnergy P ∧
            μ ≤ fullZeroForm P ∧
            ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
              let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
              ContDiff ℝ 2 D ∧
              HasCompactSupport D ∧
              μ / 2 ≤ (weilFullFunctional (fun m => (Λ m : ℝ))
                (EF.weilTest D D)).re ∧
              μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
              configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
                configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set Wp := directTruncatedWindowPrimeSlope
  have hWp : 0 ≤ Wp := directTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (Wp + 1))
  have hδ : 0 < δ := by positivity
  set K := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant +
    1300 * truncatedCrossBlockConstant + 2 * Wp * windowRingMajorantUpperOffset
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (4 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨hδ, M₀, fun J M L W h hM hL_pow V hVpos hV b hb => ?_⟩
  obtain ⟨hlogM, _⟩ := hM₀ (M 0) hM
  set I := Finset.range J
  set T := I.biUnion W
  obtain ⟨j₀, hj₀, hbj₀⟩ := hb
  have hE : 0 < ∑ n ∈ T, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj₀)
  have hM3 : 3 ≤ M 0 := h.1
  have hMpos : (0 : ℝ) < M 0 := by exact_mod_cast (show 0 < M 0 by omega)
  have hlogM_pos : 0 < Real.log (M 0) := Real.log_pos (by exact_mod_cast (show 1 < M 0 by omega))
  have hgap_i : ∀ i ∈ I,
      s / 4 * Real.log (M 0) ≤
        s * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
          criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
          2 * Wp * (Real.log (L i) + windowRingMajorantUpperOffset) := by
    intro i hi
    have hi_lt := Finset.mem_range.mp hi
    have hLi0 : (0 : ℝ) < L i := by exact_mod_cast h.2.1 i hi_lt
    have hlogLi : Real.log (L i) ≤ δ * Real.log (M 0) := by
      have := Real.log_le_log hLi0 (hL_pow i hi_lt)
      rwa [Real.log_rpow hMpos] at this
    have h1 : 2 * Wp * Real.log (L i) ≤ s / 2 * Real.log (M 0) := by
      calc 2 * Wp * Real.log (L i) ≤ 2 * Wp * (δ * Real.log (M 0)) := by gcongr
        _ = s / 2 * Real.log (M 0) * (Wp / (Wp + 1)) := by unfold δ; field_simp; ring
        _ ≤ s / 2 * Real.log (M 0) * 1 := by
            gcongr
            rw [div_le_one (by linarith)]; linarith
        _ = s / 2 * Real.log (M 0) := by ring
    have h2 : K < s / 4 * Real.log (M 0) := by
      have := (div_lt_iff₀ hs).mp hlogM
      linarith
    unfold K at h2
    linarith
  have hcomp := criticalTruncatedCompleteEnergy_ge_of_lacunaryWindows h b hV
  rw [← compactFullWeilEnergy_criticalTruncatedTest hVpos] at hcomp
  have hsum_ge : s / 4 * Real.log (M 0) * ∑ n ∈ T, b n ^ 2 ≤
      ∑ i ∈ I,
        (s * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
          criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
          2 * Wp * (Real.log (L i) + windowRingMajorantUpperOffset)) * ∑ n ∈ W i, b n ^ 2 := by
    rw [Finset.sum_biUnion h.pairwiseDisjoint, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hgap_i i hi) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hweil : s / 4 * Real.log (M 0) * ∑ n ∈ T, b n ^ 2 ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos T b) :=
    hsum_ge.trans (EReal.coe_le_coe_iff.mp hcomp)
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set μ := s / 8 * Real.log (M 0) * ∑ n ∈ T, b n ^ 2
  have hμ : 0 < μ := by unfold μ; positivity
  have h2μ : 2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos T b) := by
    unfold μ; linarith
  exact ⟨hμ, h2μ, (fullZeroForm_eq_compactFullWeilEnergy _).symm,
    gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge hVpos hV1 T b hμ h2μ⟩

/-- **Two-Band Splitting of a Single Dense Window `[1, LM]` Without Any Lacunary Gap.**
For any disjoint decomposition `S = S_low ∪ S_high` of a dense support in `[1, LM]` where the
upper band `S_high` lies in a window `ScaleWindow S_high M L` (`M ≥ 2, L ≥ 1`) and `S_low` is an
arbitrary lower band in `[1, LM]` (with **no** lacunary separation between `S_low` and `S_high`),
whenever the upper band carries positive net margin
`0 < (s_T (log M - c_T) - K_{Γ,pol} - 2 C_TW (4 + log L)) E_high - (s_T (log M - c_T) ρ + K_{Γ,pol} + 4 C_TW (3 + log(LM))²) E_low`,
all five form realizations and their single-scale `gridTentPattern` / `smoothGridTentDetector`
transfers are unconditionally strictly positive. -/
theorem dense_window_two_band_all_five_forms_pos
    {S_low S_high : Finset ℕ} (hdisj : Disjoint S_low S_high) (b : ℕ → ℝ)
    {M L : ℕ} (hM : 2 ≤ M) (hM_log : criticalTruncatedArchLogOffset ≤ Real.log M)
    (hL : 1 ≤ L) (hS_low : ∀ n ∈ S_low, n + 1 ≤ L * M) (hS_high : ScaleWindow S_high M L)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalTwoBandTruncationThreshold ≤ V)
    {μ : ℝ} (hμ : 0 < μ)
    (hdom : 2 * μ ≤
      (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
          criticalAllScaleGammaPolarConstant -
          2 * criticalTruncatedWindowPrimeSlope * (4 + Real.log L)) *
        (∑ n ∈ S_high, b n ^ 2) -
      (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
          criticalLowModePenaltyRatio +
          criticalAllScaleGammaPolarConstant +
          4 * criticalTruncatedWindowPrimeSlope * (3 + Real.log ((L * M : ℕ) : ℝ)) ^ 2) *
        (∑ n ∈ S_low, b n ^ 2)) :
    let T : Finset ℕ := S_low ∪ S_high
    let R : ℝ := Real.log (2 * V)
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * criticalTruncatedTest hVpos T b x
    2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
    0 < compactFullWeilEnergy (criticalTruncatedTest hVpos T b) ∧
    0 < fullZeroForm (criticalTruncatedTest hVpos T b) ∧
    ∀ᶠ n : ℕ in atTop,
      let M_grid : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
      let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M_grid
      μ ≤ compactFullWeilEnergy P ∧
      μ ≤ fullZeroForm P ∧
      ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
        let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M_grid q
        ContDiff ℝ 2 D ∧
        HasCompactSupport D ∧
        μ / 2 ≤ (weilFullFunctional (fun m => (Λ m : ℝ))
          (EF.weilTest D D)).re ∧
        μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
        configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
          configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set T := S_low ∪ S_high
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have h2μ : 2 * μ ≤ compactFullWeilEnergy (criticalTruncatedTest hVpos T b) :=
    hdom.trans (compactFullWeilEnergy_criticalTruncatedTest_ge_of_low_and_window hdisj b
      hM hM_log hL hS_low hS_high hVpos hV)
  have hpos : 0 < compactFullWeilEnergy (criticalTruncatedTest hVpos T b) := by linarith
  have hzf : 0 < fullZeroForm (criticalTruncatedTest hVpos T b) := by
    rw [fullZeroForm_eq_compactFullWeilEnergy]
    exact hpos
  exact ⟨h2μ, hpos, hzf,
    gridTentPattern_and_smoothDetector_pos_of_compactFullWeilEnergy_ge hVpos hV1 T b hμ h2μ⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
