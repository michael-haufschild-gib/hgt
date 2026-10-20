import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormPolynomialWindows
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.RHTower.DeningerCausalVonMangoldtWall
import GaloisForLFunctions.RHTower.NonTemperedShiftedZetaPairCountermodel

/-!
# Compact Doubly Collared Sources on Polynomial Scale Windows and the Temperedness Gate

This module connects `ArithmeticPositivityTheory`, `ArithmeticCriticalityTheory`,
`SquareRootThreshold`, and `RHTower` to establish unconditional polynomial scale-window positivity
at arbitrarily large compact support `[-log(2V), 0]` while explicitly separating the tempered
prime channel of `ζ` from the non-tempered shifted-zeta countermodel `F_a(s) = ζ(s - a) ζ(s + a)`:

1. **Uniform-in-`V` Scale-Window Prime Decay for Compact Doubly Collared Sources
   (`abs_criticalTruncatedWindowCorrelation_le`, `abs_criticalTruncatedPrimeAtom_le_of_window`,
   `abs_criticalTruncatedPrimeEnergy_le_of_window`):**
   For every truncation `V > 0`, every scale window `ScaleWindow S M L` (`M, L ≥ 1`), and every
   `r ≥ 2`, the prime atom of `criticalTruncatedSource V S b` satisfies
   `|criticalTruncatedPrimeAtom V S b r| ≤ (Λ(r)/r) (4/π⁴) K_TW min(1, √(L/r)) ∑_{n ∈ S} b_n²`
   with `K_TW` independent of `V, M, L, S, b, r`. Evaluating `min(1, √(L/r)) ≤ (L/r)^ε` at
   `ε = 1/(2 + log L)` and applying the tempered critical-line Dirichlet bound
   `RHTower.tsum_vonMangoldt_div_rpow_le_six` yields
   `|criticalTruncatedPrimeEnergy V S b| ≤ C_TW (3 + log L) ∑_{n ∈ S} b_n²` uniformly in `V > 0`.

2. **Temperedness Gate Separation (`not_summable_shiftedPairVonMangoldt_div_rpow_of_le_abs`,
   `not_summable_shiftedPairVonMangoldt_window_majorant`):**
   While the critical-line raw weight `Λ(r)/r` is not summable (`deningerVonMangoldt_not_summable`,
   Wall 6), the `ε = 1/(2 + log L)` window decay makes `Λ(r) r^{-1-ε}` summable for every `L ≥ 1`
   with sum at most `6(3 + log L)`. By contrast, for the non-tempered countermodel
   `F_a(s) = ζ(s - a) ζ(s + a)` (`a ≠ 0`, Wall 9), the shifted von Mangoldt series
   `shiftedPairVonMangoldt a r / r^{1+ε} = Λ(r)(r^a + r^{-a}) / r^{1+ε}` fails summability
   whenever `ε ≤ |a|` (and in particular on every scale window with `1/|a| - 2 ≤ log L`).

3. **Unconditional Polynomial Scale-Window Coercivity at Arbitrarily Large Compact Support Across
   All Five Form Realizations (`criticalTruncatedCompleteEnergy_ge_of_window`,
   `compactFullWeilEnergy_criticalTruncatedTest_ge_of_window`,
   `fullZeroForm_criticalTruncatedTest_ge_of_window`,
   `exists_polynomial_window_compact_weil_and_fullZeroForm_pos`,
   `exists_smooth_actual_zeta_reflection_coercivity_of_compact_window`):**
   On every polynomial scale window `[M, LM]` with `L ≤ M^δ` (`M ≥ M₀`) and every truncation
   `V ≥ criticalTruncationThreshold` (support `[-log(2V), 0]` covering all prime powers `r ≤ ⌈2V⌉`),
   `criticalTruncatedCompleteEnergy`, `compactFullWeilEnergy` (`APT`), `fullZeroForm` (`ACT`),
   `(weilFullFunctional Λ ...).re` (`RHTower`), and their smooth `C_c²(ℝ, ℝ)` mollifications mapping
   to actual-zeta zero-side reflection dominance
   `configurationReflectionDefect zetaZeroConfig F < configurationSquareMass zetaZeroConfig F` (`SRT`)
   are unconditionally strictly positive with explicit `Ω(log M)` margin.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported ENNReal
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Uniform-in-`V` Scale-Window Prime Decay for Compact Doubly Collared Sources -/

/-- Uniform harmonic constant of the truncated collar weight `criticalTruncatedWeight (r / V)`,
independent of `r` and `V`. -/
def windowTruncatedUniform : ℝ :=
  4 * crossSpacedBound criticalCollarMass criticalTruncatedCurvature

/-- Far harmonic constant of the truncated collar weight `criticalTruncatedWeight (r / V)`,
independent of `r` and `V`. -/
def windowTruncatedFarConstant : ℝ :=
  16 * criticalTruncatedCurvature

/-- Window correlation constant `K_TW` of compact doubly collared sources, independent of `V`. -/
def criticalTruncatedWindowConstant : ℝ :=
  windowTruncatedUniform * (Real.pi ^ 2 / 6) ^ 2 +
    (Real.sqrt 8 * windowTruncatedUniform *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
      windowTruncatedFarConstant * (Real.pi ^ 2 / 6) ^ 2)

/-- Logarithmic prime-window slope `C_TW = (4/π⁴) K_TW · 6e` of compact doubly collared sources,
independent of `V`. -/
def criticalTruncatedWindowPrimeSlope : ℝ :=
  4 / Real.pi ^ 4 * criticalTruncatedWindowConstant * (6 * Real.exp 1)

theorem windowTruncatedUniform_nonneg : 0 ≤ windowTruncatedUniform := by
  unfold windowTruncatedUniform crossSpacedBound
  have hA : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
  have hB : 0 ≤ criticalTruncatedCurvature := criticalTruncatedCurvature_nonneg
  positivity

theorem windowTruncatedFarConstant_nonneg : 0 ≤ windowTruncatedFarConstant := by
  unfold windowTruncatedFarConstant
  have hB : 0 ≤ criticalTruncatedCurvature := criticalTruncatedCurvature_nonneg
  positivity

theorem criticalTruncatedWindowConstant_nonneg : 0 ≤ criticalTruncatedWindowConstant := by
  unfold criticalTruncatedWindowConstant
  have hU := windowTruncatedUniform_nonneg
  have hF := windowTruncatedFarConstant_nonneg
  have h1 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have h2 : 0 ≤ ∑' l : ℕ, 1 / (l : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  positivity

theorem criticalTruncatedWindowPrimeSlope_nonneg : 0 ≤ criticalTruncatedWindowPrimeSlope := by
  unfold criticalTruncatedWindowPrimeSlope
  have := criticalTruncatedWindowConstant_nonneg
  positivity

private theorem truncated_collar_uniform {lam : ℝ} (hl : 0 ≤ lam) (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℕ} (hr : 1 ≤ r) (k l : ℕ) (hk : 1 ≤ k) (hl1 : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
      dyadicCrossKernel (weightCosineTransform (criticalTruncatedWeight lam)) k
        ((l * r : ℕ) : ℝ) n n'| ≤ windowTruncatedUniform * ∑ n ∈ S, b n ^ 2 := by
  obtain ⟨hA, hB⟩ := abs_weightCosineTransform_criticalTruncatedWeight_le hl
  exact abs_bilinear_dyadicCrossKernel_le_uniform hA hB
    criticalTruncatedCurvature_nonneg S (by exact_mod_cast hk)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)) b

private theorem truncated_collar_far {lam : ℝ} (hl : 0 ≤ lam) {S : Finset ℕ} {M L : ℕ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) {r : ℕ} (k l : ℕ)
    (hk : 1 ≤ k) (hfar : 8 * (L : ℝ) * k ≤ ((l * r : ℕ) : ℝ)) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
      dyadicCrossKernel (weightCosineTransform (criticalTruncatedWeight lam)) k
        ((l * r : ℕ) : ℝ) n n'| ≤
      windowTruncatedFarConstant * (L / ((l * r : ℕ) : ℝ)) * ∑ n ∈ S, b n ^ 2 := by
  obtain ⟨_, hB⟩ := abs_weightCosineTransform_criticalTruncatedWeight_le hl
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq1 : (1 : ℝ) ≤ ((l * r : ℕ) : ℝ) := by nlinarith
  have h := abs_bilinear_dyadicCrossKernel_le_far hB
    criticalTruncatedCurvature_nonneg hM hL hS hk1 hfar b
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  unfold windowTruncatedFarConstant
  have hB0 := criticalTruncatedCurvature_nonneg
  rw [show 16 * (L : ℝ) * criticalTruncatedCurvature / ((l * r : ℕ) : ℝ) ^ 2 =
    16 * criticalTruncatedCurvature * (L / ((l * r : ℕ) : ℝ)) * (1 / ((l * r : ℕ) : ℝ)) by field_simp]
  have : 1 / ((l * r : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
  have h0 : 0 ≤ 16 * criticalTruncatedCurvature * (L / ((l * r : ℕ) : ℝ)) := by positivity
  nlinarith

/-- **Uniform-in-`V` dilation correlation bound on scale windows.** For every `lam ≥ 0`
(in particular `lam = r / V`), every scale window `ScaleWindow S M L` (`M, L ≥ 1`), and every
`r ≥ 1`, the correlation against `criticalTruncatedWeight lam` decays like `min(1, √(L/r))`
uniformly in `lam`. -/
theorem abs_criticalTruncatedWindowCorrelation_le {lam : ℝ} (hl : 0 ≤ lam) {S : Finset ℕ}
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) {r : ℕ}
    (hr : 1 ≤ r) :
    |∫ v in Ioi 1, criticalTruncatedWeight lam v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r))) *
        ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU := windowTruncatedUniform_nonneg
  have hF := windowTruncatedFarConstant_nonneg
  have hZ1 : 0 ≤ (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2 :=
    mul_nonneg (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rcases le_or_gt L r with hLr | hLr
  · have hc := abs_integral_weight_dilate_le_of_window (integrableOn_criticalTruncatedWeight lam)
      S b hL hLr hU hF
      (fun k l hk hl1 => truncated_collar_uniform hl S b hr k l hk hl1)
      (fun k l hk _ hfar => truncated_collar_far hl hM hL hS b k l hk hfar)
    have hmin : min 1 (Real.sqrt (L / r)) = Real.sqrt (L / r) := by
      refine min_eq_right ?_
      rw [Real.sqrt_le_one, div_le_one hrpos]
      exact_mod_cast hLr
    rw [hmin]
    refine hc.trans ?_
    unfold criticalTruncatedWindowConstant
    have hρ : 0 ≤ Real.sqrt (L / r) := Real.sqrt_nonneg _
    have hpi : 0 < 4 / Real.pi ^ 4 := by positivity
    have hU2 : 0 ≤ windowTruncatedUniform * (Real.pi ^ 2 / 6) ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hpi.le hρ) hU2) hE]
  · have hc := abs_integral_weight_dilate_le_of_uniform (integrableOn_criticalTruncatedWeight lam)
      S b r hU (fun k l hk hl1 => truncated_collar_uniform hl S b hr k l hk hl1)
    have hmin : min 1 (Real.sqrt (L / r)) = 1 := by
      refine min_eq_left ?_
      rw [Real.one_le_sqrt, one_le_div hrpos]
      exact_mod_cast hLr.le
    rw [hmin, mul_one]
    refine hc.trans ?_
    unfold criticalTruncatedWindowConstant
    have hpi : 0 < 4 / Real.pi ^ 4 := by positivity
    have hrest : 0 ≤ Real.sqrt 8 * windowTruncatedUniform *
        ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
        windowTruncatedFarConstant * (Real.pi ^ 2 / 6) ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg hpi.le hrest) hE]

/-- **Window-decaying prime-atom bound for compact doubly collared sources.** For every `V > 0`,
every scale window `ScaleWindow S M L` (`M, L ≥ 1`), and every `r ≥ 2`, the prime atom is bounded
by `(Λ(r)/r) (4/π⁴) K_TW min(1, √(L/r)) ∑ b_n²` uniformly in `V`. -/
theorem abs_criticalTruncatedPrimeAtom_le_of_window {V : ℝ} (hV : 0 < V) {S : Finset ℕ}
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) (r : ℕ) :
    |criticalTruncatedPrimeAtom V S b r| ≤
      (if 2 ≤ r then
        (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r)))) *
          ∑ n ∈ S, b n ^ 2
      else 0) := by
  unfold criticalTruncatedPrimeAtom
  split_ifs with hr
  · have hr0 : (0 : ℝ) < r := by positivity
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    have hl : 0 ≤ (r : ℝ) / V := by positivity
    have hw : (∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))) =
        ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [criticalTruncatedWeight]
      rw [show (r : ℝ) / V * v = r * v / V by ring]
    have hcorr := abs_criticalTruncatedWindowCorrelation_le hl hM hL hS b (r := r) (by omega)
    rw [integral_criticalTruncatedSource_mul_dilate hV S b hr, hw, abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsr.le),
      abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
    have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_|)
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
          (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r))) *
            ∑ n ∈ S, b n ^ 2)) := by gcongr
      _ = (ArithmeticFunction.vonMangoldt r : ℝ) / (Real.sqrt r * Real.sqrt r) *
          (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r)))) *
          ∑ n ∈ S, b n ^ 2 := by ring
      _ = _ := by rw [hrr]
  · simp

private theorem min_sqrt_le_rpow' {L r ε : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    min 1 (Real.sqrt (L / r)) ≤ (L / r) ^ ε := by
  rcases le_or_gt r L with h | h
  · exact (min_le_left _ _).trans (Real.one_le_rpow (by rw [le_div_iff₀ hr]; linarith) hε0)
  · refine (min_le_right _ _).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hr]; linarith) hε

/-- **Uniform-in-`V` logarithmic prime-window law for compact doubly collared sources.**
For every truncation `V > 0`, every scale window `ScaleWindow S M L` (`M, L ≥ 1`), and every
real coefficient vector `b`,
`|criticalTruncatedPrimeEnergy V S b| ≤ C_TW (3 + log L) ∑_{n ∈ S} b_n²`
with `C_TW` independent of `V`. -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_window {V : ℝ} (hV : 0 < V) {S : Finset ℕ}
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V S b| ≤
      criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  set ε := 1 / (2 + Real.log L)
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  set C := 4 / Real.pi ^ 4 * criticalTruncatedWindowConstant * E
  have hC : 0 ≤ C := by have := criticalTruncatedWindowConstant_nonneg; positivity
  have hs : (1 : ℝ) < 1 + ε := by linarith
  have hsum := RHTower.summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs
  have hbd (r : ℕ) : |criticalTruncatedPrimeAtom V S b r| ≤
      C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) := by
    have hatom := abs_criticalTruncatedPrimeAtom_le_of_window hV hM hL hS b r
    refine hatom.trans ?_
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      have hmin := min_sqrt_le_rpow' hL0 hr0 hε0.le hε
      have hpow : (r : ℝ) ^ (1 + ε) = r * r ^ ε := by rw [Real.rpow_add hr0, Real.rpow_one]
      rw [hpow, Real.div_rpow hL0.le hr0.le] at *
      have hrε : 0 < (r : ℝ) ^ ε := Real.rpow_pos_of_pos hr0 _
      have hK0 := criticalTruncatedWindowConstant_nonneg
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r)))) * E
          ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * ((L : ℝ) ^ ε / (r : ℝ) ^ ε))) * E := by
            gcongr
        _ = C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r * r ^ ε)) := by
            unfold C; field_simp
    · have := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      positivity
  have hmaj : Summable fun r : ℕ =>
      C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) :=
    hsum.mul_left _
  have habs : Summable fun r => ‖criticalTruncatedPrimeAtom V S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj
  unfold criticalTruncatedPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ((habs.tsum_le_tsum (fun r => by
    rw [Real.norm_eq_abs]; exact hbd r) hmaj).trans ?_)
  rw [tsum_mul_left]
  have hsix := RHTower.tsum_vonMangoldt_div_rpow_le_six hs
  have hLε : (L : ℝ) ^ ε ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    unfold ε
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hfrac : 6 * (1 + ε) / (1 + ε - 1) = 6 * (3 + Real.log L) := by
    unfold ε; field_simp; ring
  rw [hfrac] at hsix
  have hLε0 : 0 ≤ (L : ℝ) ^ ε := (Real.rpow_pos_of_pos hL0 _).le
  calc C * (L : ℝ) ^ ε * ∑' r : ℕ, (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε) ≤
        C * Real.exp 1 * (6 * (3 + Real.log L)) := by gcongr
    _ = criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * E := by
        unfold C criticalTruncatedWindowPrimeSlope; ring

/-! ## Section 2: Temperedness Gate Separation (`Wall 6` vs. `Wall 9`) -/

/-- The scale-window dilation exponent `ε(L) = 1 / (2 + log L)`. -/
def windowDilationExponent (L : ℕ) : ℝ := 1 / (2 + Real.log L)

theorem windowDilationExponent_pos {L : ℕ} (hL : 1 ≤ L) : 0 < windowDilationExponent L := by
  unfold windowDilationExponent
  have : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  positivity

/-- **Tempered Window Summability (`ζ` passes Wall 6 & Wall 9).** While the raw critical-line
von Mangoldt series `Λ(r)/r` diverges (`RHTower.deningerVonMangoldt_not_summable`), the
scale-window dilation exponent `ε(L) = 1/(2 + log L)` makes `Λ(r) / r^{1 + ε(L)}` unconditionally
summable for every `L ≥ 1`, with sum bounded by `6(3 + log L)`. -/
theorem summable_vonMangoldt_windowDilationExponent {L : ℕ} (hL : 1 ≤ L) :
    Summable (fun r : ℕ => (ArithmeticFunction.vonMangoldt r : ℝ) /
      (r : ℝ) ^ (1 + windowDilationExponent L)) ∧
    (∑' r : ℕ, (ArithmeticFunction.vonMangoldt r : ℝ) /
      (r : ℝ) ^ (1 + windowDilationExponent L)) ≤ 6 * (3 + Real.log L) := by
  have hε := windowDilationExponent_pos hL
  have hs : (1 : ℝ) < 1 + windowDilationExponent L := by linarith
  refine ⟨RHTower.summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs, ?_⟩
  have hsix := RHTower.tsum_vonMangoldt_div_rpow_le_six hs
  have hfrac : 6 * (1 + windowDilationExponent L) / (1 + windowDilationExponent L - 1) =
      6 * (3 + Real.log L) := by
    unfold windowDilationExponent; field_simp; ring
  rwa [hfrac] at hsix

/-- Pointwise dominance of the shifted-pair von Mangoldt weight over `Λ(r) r^{|a|}` for `r ≥ 1`. -/
theorem vonMangoldt_mul_rpow_abs_le_shiftedPairVonMangoldt (a : ℝ) {r : ℕ} (_ : 1 ≤ r) :
    (ArithmeticFunction.vonMangoldt r : ℝ) * (r : ℝ) ^ |a| ≤ shiftedPairVonMangoldt a r := by
  unfold shiftedPairVonMangoldt
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    have : 0 ≤ (r : ℝ) ^ (-a) := Real.rpow_nonneg hr0 _
    nlinarith
  · rw [abs_of_neg ha]
    have : 0 ≤ (r : ℝ) ^ a := Real.rpow_nonneg hr0 _
    nlinarith

/-- **Non-Tempered Divergence (`ζ(s - a) ζ(s + a)` fails the Temperedness Gate, Wall 9).**
For every shift `a` and every exponent `ε ≤ |a|`, the shifted-pair prime series
`r ↦ shiftedPairVonMangoldt a r / r^{1 + ε}` is not summable. -/
theorem not_summable_shiftedPairVonMangoldt_div_rpow_of_le_abs {a ε : ℝ} (hε : ε ≤ |a|) :
    ¬ Summable (fun r : ℕ => shiftedPairVonMangoldt a r / (r : ℝ) ^ (1 + ε)) := by
  intro hsum
  apply RHTower.deningerVonMangoldt_not_summable
  refine Summable.of_nonneg_of_le
    (fun r => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg r))
    (fun r => ?_) hsum
  rcases eq_or_ne r 0 with rfl | hr0
  · simp [shiftedPairVonMangoldt]
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hdom := vonMangoldt_mul_rpow_abs_le_shiftedPairVonMangoldt a hr1
    have hexp : (r : ℝ) ^ (1 + ε) ≤ (r : ℝ) * (r : ℝ) ^ |a| := by
      rw [Real.rpow_add hr_pos, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr_ge1 hε) hr_pos.le
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ)
        = ((ArithmeticFunction.vonMangoldt r : ℝ) * (r : ℝ) ^ |a|) /
            ((r : ℝ) * (r : ℝ) ^ |a|) := by
          rw [mul_div_mul_right _ _ (Real.rpow_pos_of_pos hr_pos |a|).ne']
      _ ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) * (r : ℝ) ^ |a|) / (r : ℝ) ^ (1 + ε) :=
          div_le_div_of_nonneg_left
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hr_pos.le _))
            (Real.rpow_pos_of_pos hr_pos _) hexp
      _ ≤ shiftedPairVonMangoldt a r / (r : ℝ) ^ (1 + ε) :=
          div_le_div_of_nonneg_right hdom (Real.rpow_nonneg hr_pos.le _)

/-- **Scale-Window Temperedness Gate Theorem.** For any non-tempered shift `a ≠ 0` and any window
ratio `L ≥ 1` with `1 / |a| - 2 ≤ log L`, the scale-window prime majorant converges for `ζ`
(`Λ`) with sum `≤ 6(3 + log L)` while diverging for `ζ(s - a) ζ(s + a)` (`shiftedPairVonMangoldt a`). -/
theorem not_summable_shiftedPairVonMangoldt_windowDilationExponent {a : ℝ} (ha : a ≠ 0)
    {L : ℕ} (hL : 1 ≤ L) (hLa : 1 / |a| - 2 ≤ Real.log L) :
    ¬ Summable (fun r : ℕ =>
      shiftedPairVonMangoldt a r / (r : ℝ) ^ (1 + windowDilationExponent L)) := by
  have ha_pos : 0 < |a| := abs_pos.mpr ha
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hε : windowDilationExponent L ≤ |a| := by
    unfold windowDilationExponent
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ ha_pos).mp (show 1 / |a| ≤ 2 + Real.log L by linarith)
    linarith
  exact not_summable_shiftedPairVonMangoldt_div_rpow_of_le_abs hε

/-! ## Section 3: Unconditional Polynomial Scale-Window Positivity at Arbitrarily Large Compact Support -/

/-- Gamma-plus-polar base constant `|Ω(0)| U + 288 a_R a_E` of compact doubly collared sources,
independent of `V, M, L`. -/
def criticalTruncatedWindowBaseConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    288 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant

theorem criticalTruncatedWindowBaseConstant_nonneg : 0 ≤ criticalTruncatedWindowBaseConstant := by
  unfold criticalTruncatedWindowBaseConstant
  have hU : 0 ≤ criticalCollarMassUpper := by
    unfold criticalCollarMassUpper
    have := factorialUnitIntervalUpper_pos
    positivity
  have ha : 0 ≤ criticalTruncatedReadoutConstant := by
    unfold criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ criticalTruncatedEndpointConstant := by
    unfold criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  positivity

/-- **Uniform-in-`V` channel bound on scale windows `[M, LM]`.** For every scale window
`ScaleWindow S M L` (`M ≥ 2, L ≥ 1`) and every truncation `V ≥ 1`, the Gamma, polar, and prime
channels of `criticalTruncatedSource V S b` cost at most
`(K_{T,0} + 2 C_TW (3 + log L)) ∑_{n ∈ S} b_n²` uniformly in `V`. -/
theorem neg_le_criticalTruncatedChannels_of_window (S : Finset ℕ) (b : ℕ → ℝ) {M L : ℕ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) {V : ℝ} (hV : 1 ≤ V) :
    -((criticalTruncatedWindowBaseConstant +
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * ∑ n ∈ S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
        2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
        2 * criticalTruncatedPrimeEnergy V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hV0 : 0 < V := by linarith
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
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
    have h2 := abs_criticalTruncatedPolarEndpoint_le hV S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * T) * (c * (12 * T)) := h12
      _ = 144 * a * c * T ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := abs_criticalTruncatedPrimeEnergy_le_of_window hV0 (by omega) hL hS b
  have hP' := (abs_le.mp hP).2
  have hpol' := (abs_le.mp hpol).1
  unfold criticalTruncatedWindowBaseConstant
  nlinarith

/-- **Complete energy of compact doubly collared sources on scale windows `[M, LM]`.**
For every scale window `ScaleWindow S M L` (`M ≥ 2, L ≥ 1`) and every truncation
`V ≥ criticalTruncationThreshold`,
`E(g^V) ≥ (s_T (log M - c_T) - K_{T,0} - 2 C_TW (3 + log L)) ∑_{n ∈ S} b_n²`
uniformly in `V`. -/
theorem criticalTruncatedCompleteEnergy_ge_of_window (S : Finset ℕ) (b : ℕ → ℝ) {M L : ℕ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) {V : ℝ}
    (hV : criticalTruncationThreshold ≤ V) :
    (((criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
        criticalTruncatedWindowBaseConstant -
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) *
          ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalTruncatedCompleteEnergy V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set X := criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy S b hM (fun n hn => (hS n hn).1) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalTruncatedChannels_of_window S b hM hL hS hV1
  unfold criticalTruncatedCompleteEnergy
  rw [show (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant -
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E =
      X + -((criticalTruncatedWindowBaseConstant +
        2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Real Weil energy lower bound on scale windows `[M, LM]` at arbitrarily large compact support.** -/
theorem compactFullWeilEnergy_criticalTruncatedTest_ge_of_window (S : Finset ℕ) (b : ℕ → ℝ)
    {M L : ℕ} (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) {V : ℝ} (hVpos : 0 < V)
    (hV : criticalTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant -
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * ∑ n ∈ S, b n ^ 2 ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S b) := by
  have h := criticalTruncatedCompleteEnergy_ge_of_window S b hM hL hS hV
  rw [← compactFullWeilEnergy_criticalTruncatedTest hVpos] at h
  exact EReal.coe_le_coe_iff.mp h

/-- **ACT `fullZeroForm` lower bound on scale windows `[M, LM]` at arbitrarily large compact support.** -/
theorem fullZeroForm_criticalTruncatedTest_ge_of_window (S : Finset ℕ) (b : ℕ → ℝ)
    {M L : ℕ} (hM : 2 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) {V : ℝ} (hVpos : 0 < V)
    (hV : criticalTruncationThreshold ≤ V) :
    (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant -
      2 * criticalTruncatedWindowPrimeSlope * (3 + Real.log L)) * ∑ n ∈ S, b n ^ 2 ≤
      fullZeroForm (criticalTruncatedTest hVpos S b) := by
  rw [fullZeroForm_eq_compactFullWeilEnergy]
  exact compactFullWeilEnergy_criticalTruncatedTest_ge_of_window S b hM hL hS hVpos hV

/-- **Unconditional Polynomial Scale-Window Positivity of `compactFullWeilEnergy`, `fullZeroForm`,
and `weilFullFunctional` at Arbitrarily Large Compact Support.**
There exist `δ > 0` and `M₀` such that for every `M ≥ M₀`, every window `[M, LM]` with `L ≤ M^δ`,
every truncation `V ≥ criticalTruncationThreshold` (support `[-log(2V), 0]` of arbitrarily large
length covering all prime powers `r ≤ ⌈2V⌉`), every `ScaleWindow S M L`, and every nonzero `b`,
the compact test `g^V = criticalTruncatedTest hVpos S b` satisfies
`0 < (s_T / 4) log M ∑_{n ∈ S} b_n² ≤ compactFullWeilEnergy g^V = fullZeroForm g^V = Re W_Λ(g^V)`. -/
theorem exists_polynomial_window_compact_weil_and_fullZeroForm_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          0 < criticalTruncatedArchLogSlope / 4 * Real.log M * ∑ n ∈ S, b n ^ 2 ∧
          criticalTruncatedArchLogSlope / 4 * Real.log M * ∑ n ∈ S, b n ^ 2 ≤
            compactFullWeilEnergy (criticalTruncatedTest hVpos S b) ∧
          compactFullWeilEnergy (criticalTruncatedTest hVpos S b) =
            fullZeroForm (criticalTruncatedTest hVpos S b) ∧
          fullZeroForm (criticalTruncatedTest hVpos S b) =
            (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
                (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set W := criticalTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := criticalTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set K := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant + 6 * W
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (4 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM V hVpos hV S hS b hb => ?_⟩
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
        2 * W * (3 + Real.log L) := by
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
  have hweil := compactFullWeilEnergy_criticalTruncatedTest_ge_of_window S b hM2 hL hS hVpos hV
  refine ⟨by positivity, (mul_le_mul_of_nonneg_right hgap hE.le).trans hweil,
    (fullZeroForm_eq_compactFullWeilEnergy _).symm,
    fullZeroForm_eq_re_weilFullFunctional (criticalTruncatedTest hVpos S b).continuous
      (criticalTruncatedTest hVpos S b).hasCompactSupport⟩

/-- **Smooth `C_c²(ℝ, ℝ)` Transfer to Actual-Zeta Zero-Side Reflection Dominance.**
For every compact doubly collared source `g^V = criticalTruncatedTest hVpos S b` (`V ≥ 1/2`),
its mollification `F_k = smoothCompactSource g^V k ∈ C_c²(ℝ, ℝ)` converges in `fullZeroForm` and
`compactFullWeilEnergy` at rate `O(1/(k+1))`; consequently, on every polynomial scale window
`[M, LM]` with `L ≤ M^δ` (`M ≥ M₀`) and every `V ≥ criticalTruncationThreshold`, all sufficiently
large mollification indices `k` satisfy the actual-zeta zero-side reflection dominance
`configurationReflectionDefect zetaZeroConfig F_k + (s_T / 8) log M ∑_{n ∈ S} b_n² ≤ configurationSquareMass zetaZeroConfig F_k`. -/
theorem exists_smooth_actual_zeta_reflection_coercivity_of_compact_window :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          ∃ K₀ : ℕ, ∀ k ≥ K₀,
            configurationReflectionDefect zetaZeroConfig
              (fun x => (smoothCompactSource (criticalTruncatedTest hVpos S b) k x : ℂ)) +
              criticalTruncatedArchLogSlope / 8 * Real.log M * ∑ n ∈ S, b n ^ 2 ≤
            configurationSquareMass zetaZeroConfig
              (fun x => (smoothCompactSource (criticalTruncatedTest hVpos S b) k x : ℂ)) := by
  obtain ⟨δ, hδ, M₀, hwin⟩ := exists_polynomial_window_compact_weil_and_fullZeroForm_pos
  refine ⟨δ, hδ, M₀, fun M hM L hL hLM V hVpos hV S hS b hb => ?_⟩
  obtain ⟨hpos, hge, _, _⟩ := hwin M hM L hL hLM V hVpos hV S hS b hb
  set g := criticalTruncatedTest hVpos S b
  set μ := criticalTruncatedArchLogSlope / 8 * Real.log M * ∑ n ∈ S, b n ^ 2
  have hμ : 0 < μ := by unfold μ; linarith
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set R := Real.log (2 * V)
  have hR0 : 0 ≤ R := Real.log_nonneg (by linarith)
  have hR : ∀ x, R < |x| → g x = 0 := by
    intro x hx
    apply criticalTruncatedSource_eq_zero hVpos S b
    intro hmem
    have : |x| ≤ R := abs_le.mpr ⟨hmem.1, hmem.2.trans hR0⟩
    linarith
  set Mval := 2 * ∑ n ∈ S, |b n|
  have hMval : ∀ x, |g x| ≤ Mval := by
    intro x
    change |criticalTruncatedSource V S b x| ≤ _
    rw [criticalTruncatedSource_eq, abs_mul, abs_mul, abs_mul]
    have h1 : |criticalUpperCutoff (Real.exp (-x) / V)| ≤ 1 := by
      rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
    have h2 : |Real.smoothTransition (Real.exp (-x) - 1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
    have h3 : |Real.smoothTransition (Real.exp (-x) - 1)| *
        (|Real.exp (x / 2)| * |realPhaseCombination S b (Real.exp (-x))|) ≤ Mval := by
      by_cases hx : x ≤ 0
      · have hexp : |Real.exp (x / 2)| ≤ 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (by linarith)
        have hph := abs_realPhaseCombination_le_two_mul S b (Real.exp (-x))
        calc _ ≤ 1 * (1 * Mval) := mul_le_mul h2 (mul_le_mul hexp hph (abs_nonneg _) zero_le_one)
              (by positivity) zero_le_one
          _ = Mval := by ring
      · rw [Real.smoothTransition.zero_of_nonpos (by
          have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
          rw [Real.exp_zero] at this; linarith), abs_zero, zero_mul]
        have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n)
        unfold Mval; positivity
    calc |criticalUpperCutoff (Real.exp (-x) / V)| *
          (|Real.smoothTransition (Real.exp (-x) - 1)| *
            (|Real.exp (x / 2)| * |realPhaseCombination S b (Real.exp (-x))|))
        ≤ 1 * Mval := mul_le_mul h1 h3 (by positivity) zero_le_one
      _ = Mval := one_mul _
  obtain ⟨Klip, hKlip⟩ := exists_lipschitz_criticalTruncatedSource hVpos S b
  set C := compactFullWeilApproximationCost R Mval Klip
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (C / μ)
  refine ⟨K₀, fun k hk => ?_⟩
  have herr := compactFullWeilEnergy_smoothing_error g hMval hKlip hR0 hR k
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have herr_le : C / ((k : ℝ) + 1) ≤ μ := by
    rcases le_or_gt C 0 with hC0 | hC0
    · exact (div_nonpos_of_nonpos_of_nonneg hC0 hk_pos.le).trans hμ.le
    · rw [div_le_iff₀ hk_pos]
      have hK_lt : C / μ < (k : ℝ) + 1 := by
        calc C / μ < (K₀ : ℝ) := hK₀
          _ ≤ (k : ℝ) := by exact_mod_cast hk
          _ < (k : ℝ) + 1 := by linarith
      have := (div_lt_iff₀ hμ).mp hK_lt
      linarith
  have hsm_ge : μ ≤ compactFullWeilEnergy (smoothCompactSource g k) := by
    have h1 := (abs_le.mp herr).1
    have h2 : 2 * μ ≤ compactFullWeilEnergy g := by
      unfold μ; linarith
    linarith
  have hF_diff : ContDiff ℝ 2 (smoothCompactSource g k : ℝ → ℝ) :=
    RHTower.CHMDDoobGraph.smooth_contDiff
      (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport) k
  have hF_supp : HasCompactSupport (smoothCompactSource g k : ℝ → ℝ) :=
    (smoothCompactSource g k).hasCompactSupport
  have hbridge := fullZeroForm_eq_zeta_squareMass_sub_reflectionDefect hF_diff hF_supp
  rw [fullZeroForm_eq_compactFullWeilEnergy] at hbridge
  linarith

end GaloisForLFunctions.ArithmeticPositivityTheory
