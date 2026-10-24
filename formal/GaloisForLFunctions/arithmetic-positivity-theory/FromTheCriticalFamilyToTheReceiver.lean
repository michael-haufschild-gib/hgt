import GaloisForLFunctions.«arithmetic-positivity-theory».MultiScaleLowModeAndGridTentSchurBridge
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity
import GaloisForLFunctions.SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor

/-!
# From the Critical Family to the Receiver: Quantitative Grid-Tent Transfer, Channel-by-Channel Parity Split, and the Graded Receiver Ledger

Every positivity theorem on the doubly collared critical family (`criticalTruncatedSource V S b`)
and its single-scale grid tent patterns (`gridTentPattern`) is driven by the logarithmic
archimedean Lévy gain `s_T (log M - c_T) ∑_{n ∈ S} b_n²` at scale `M`. On the receiver tests
`F ∈ C_c²(ℝ, ℝ)` where the Riemann Hypothesis and the zero width `zetaZeroWidth` are decided, there
is no scale parameter `M → ∞`: the passage from the critical family to the receiver is governed by
quantitative finite-scale approximation, parity projection onto the odd reflection sector, and the
graded reflected-prime/polar ledger.

This module establishes five unconditional pillars completing the bridge from the critical family
to the receiver (§7.5 and §7.8.1):

1. **Quantitative Finite-Scale Grid-Tent and Smooth-Detector Approximation Across All Five Form
   Realizations** (`gridTentApproximationConstant`, `gridTentMassApproximationConstant`,
   `abs_compactFullWeilEnergy_gridTentPattern_sub_le`,
   `abs_compactFullWeilEnergy_gridTentPattern_sub_le_inv_scale`,
   `abs_fullZeroForm_gridTentPattern_sub_le`,
   `abs_integral_sq_gridTentPattern_sub_le`,
   `abs_smoothGridTentDetector_sub_compactFullWeilEnergy_le`):
   Exposes the explicit finite-scale error bound for `gridTentPattern` and `smoothGridTentDetector`
   in both `compactFullWeilEnergy` (and `fullZeroForm`, `weilFullFunctional`, `zetaZeroConfig.W`,
   `configurationSquareMass - configurationReflectionDefect`) and `L²` mass `∫ g²`, with explicit
   `O(d_{n+1}) ≤ O(1/(12(n+1)))` decay in the arithmetic scale `n` and `1/(q+1)` in the smoothing
   index `q`, retaining the prime cutoff beyond the observation horizon.

2. **Exact Channel-by-Channel Parity Split on `C_c(ℝ, ℝ)` and Odd/Even Projections of Compact
   Critical Sources** (`evenCompactSource`, `oddCompactSource`,
   `autocorr_evenCompactSource_add_oddCompactSource`,
   `integral_sq_evenCompactSource_add_oddCompactSource`,
   `biScaleLevyEnergy_evenCompactSource_add_oddCompactSource`,
   `fullPairing_autocorr_evenCompactSource_add_oddCompactSource`,
   `compactFullWeilEnergy_eq_evenCompactSource_add_oddCompactSource`,
   `integral_sq_oddCompactSource_criticalTruncatedTest`,
   `ofReal_le_oddPartReal_criticalTruncatedLevyEnergy`,
   `ofReal_le_evenPartReal_criticalTruncatedLevyEnergy`):
   For every `f ∈ C_c(ℝ, ℝ)` and every shift `t ∈ ℝ`, the autocorrelation splits identically into
   even and odd parts: `autocorr (evenCompactSource f) t + autocorr (oddCompactSource f) t = autocorr f t`.
   Consequently, `∫ f²`, `biScaleLevyEnergy f`, `fullPairing (autocorr f)`, `compactFullWeilEnergy f`,
   and `fullZeroForm f` split additively channel by channel. Because `criticalTruncatedSource V S b`
   is supported on `(-∞, 0]` and vanishes at `0`, its odd and even projections each carry exact half
   of its `L²` mass and individually satisfy logarithmic archimedean Lévy coercivity
   `≥ (s_T / 2) (log M - c_{T,odd}) ∑_{n ∈ S} b_n²`.

3. **Norm-Controlled Subfamily Transfer and Graded Grid-Tent Receiver Laws**
   (`HasNormControlledReceiverTransfer`, `zetaZeroWidth_le_of_normControlled_subfamily_transfer`,
   `riemannHypothesis_iff_subexponential_normControlled_transfer`,
   `riemannHypothesis_iff_bdd_normControlled_transfer`,
   `zetaZeroWidth_le_of_eventually_gridTentPattern_odd_floor`,
   `riemannHypothesis_iff_subexponential_gridTentPattern_odd_floor`,
   `riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor`):
   Proves that any subfamily `ℱ r ⊆ C_c(ℝ, ℝ)` that approximates odd receiver tests `F` at aperture
   `r` in `compactFullWeilEnergy` with `L²`-norm control `∫ g² ≤ α e^{2β r} ∫ F²` transfers a
   graded floor `-C e^{2σ r} ∫ g²` to `zetaZeroWidth ≤ σ + β`. In particular, for `β = 0` (as
   satisfied by `gridTentPattern` and `oddCompactSource (gridTentPattern ...)`), a graded floor at
   rate `σ` forces `zetaZeroWidth ≤ σ`, and any subexponential or uniform constant floor (`σ = 0`)
   forces `zetaZeroWidth = 0`, `RiemannHypothesis`, and self-improves to exact positivity `≥ 0` across
   all apertures.

4. **All-Aperture Reflected-Prime/Polar Receiver Ledger, Rate-`1/2` and Sharp PNT Floors, De la
   Vallée Poussin Sobolev Bounds, and the Converse Width-to-Floor Bridge**
   (`compactFullWeilEnergy_eq_reflectedPrimePolarLedger`,
   `compactFullWeilEnergy_eq_chebyshevTwoPoleDefect_ledger`,
   `compactFullWeilEnergy_eq_criticalScalePrefix_ledger`,
   `compactFullWeilEnergy_ge_neg_seventy_five_mul_exp`,
   `exists_compactFullWeilEnergy_ge_neg_three_add_eps_mul_exp`,
   `exists_compactFullWeilEnergy_ge_neg_deLaValleePoussin_sobolev`,
   `exists_compactFullWeilEnergy_ge_neg_poleTilted_deLaValleePoussin_sobolev`,
   `exists_compactFullWeilEnergy_ge_neg_of_zetaZeroWidth_lt`,
   `exists_gridTentPattern_ge_neg_of_zetaZeroWidth_lt`):
   Transports the exact reflected-prime/polar, two-pole Chebyshev-defect (`E(s) = e^s + s - 1 - ψ(e^s)`),
   and second-order critical-scale prefix ledgers, together with the unconditional `-75 e^r`,
   `-((3 + ε) e^r + C)`, and de la Vallée Poussin Sobolev floors and the converse width-to-floor
   implication `zetaZeroWidth < β ⟹ Floor(2β)`, directly to `compactFullWeilEnergy` and finite-scale
   `gridTentPattern`.

5. **Unconditional Small-Aperture Receiver Coercivity (`r ≤ 3/10` for All Profiles, `r ≤ 181/500`
   Past the First Prime for Odd Profiles) and Finite-Scale Grid-Tent Transfer**
   (`compactFullWeilEnergy_ge_of_support_le_threeTenths`,
   `gridTentPattern_and_smoothDetector_pos_of_support_le_threeTenths`,
   `compactFullWeilEnergy_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`,
   `gridTentPattern_and_smoothDetector_pos_of_odd_support_le_threeHundredSixtyTwoThousandths`):
   Establishes unconditional coercivity `(1/5000) ∫ F² ≤ compactFullWeilEnergy F` on `[-3/10, 3/10]`
   for all profiles and `(1/1000) ∫ F² ≤ compactFullWeilEnergy F` on `[-181/500, 181/500]` (strictly
   past `(log 2)/2`) for odd profiles, and transfers both with explicit finite-scale thresholds to
   `gridTentPattern` and `smoothGridTentDetector` across all five form realizations.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators ENNReal CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Quantitative Finite-Scale Grid-Tent and Smooth-Detector Approximation -/

/-- Explicit complete-form approximation constant for `gridTentPattern` on `[-R, R]`, retaining the
prime cutoff `compactFullWeilPrimeCutoff (R + 2)` beyond the observation horizon `2(R + 1)`. -/
def gridTentApproximationConstant (R Mg Kg L : ℝ) : ℝ :=
  let B := R + 2
  let MG := Real.exp (3 * B / 2) * Mg
  let Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  let Kf := Real.exp (3 * B / 2) * (L + 3 / 2 * (MG + 2 * L))
  let N := compactFullWeilPrimeCutoff B
  let Const := (Mf + Mg) * (|EF.gammaBracket 0| + 2 * mass N) + (Kf + Kg) * archWeightFirstMoment
  2 * B * (Real.exp (3 * B / 2) * (2 * L)) * Const

/-- Explicit `L²`-mass approximation constant for `gridTentPattern` on `[-R, R]`. -/
def gridTentMassApproximationConstant (R Mg L : ℝ) : ℝ :=
  let B := R + 2
  let MG := Real.exp (3 * B / 2) * Mg
  let Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  2 * B * (Real.exp (3 * B / 2) * (2 * L)) * (Mf + Mg)

theorem gridTentApproximationConstant_nonneg {R Mg Kg L : ℝ}
    (hR : 0 ≤ R) (hMg : 0 ≤ Mg) (hKg : 0 ≤ Kg) (hL : 0 ≤ L) :
    0 ≤ gridTentApproximationConstant R Mg Kg L := by
  unfold gridTentApproximationConstant
  dsimp only
  have hB : 0 ≤ R + 2 := by linarith
  have hN := mass_nonneg (compactFullWeilPrimeCutoff (R + 2))
  have hA := archWeightFirstMoment_nonneg
  positivity

theorem gridTentMassApproximationConstant_nonneg {R Mg L : ℝ}
    (hR : 0 ≤ R) (hMg : 0 ≤ Mg) (hL : 0 ≤ L) :
    0 ≤ gridTentMassApproximationConstant R Mg L := by
  unfold gridTentMassApproximationConstant
  dsimp only
  have hB : 0 ≤ R + 2 := by linarith
  positivity

private theorem primeCutoff_large_of_radius (R : ℝ) :
    2 * (R + 1) < cutoff (compactFullWeilPrimeCutoff R) := by
  have he : Real.exp (2 * (R + 1) + 1) ≤ (compactFullWeilPrimeCutoff R : ℝ) := Nat.le_ceil _
  have he' : Real.exp (2 * (R + 1) + 1) ≤ ((compactFullWeilPrimeCutoff R + 2 : ℕ) : ℝ) := by
    push_cast; linarith
  have h := Real.log_le_log (Real.exp_pos _) he'
  rw [Real.log_exp] at h
  exact lt_of_lt_of_le (by linarith) h

/-- **Quantitative Finite-Scale `L¹` Source Gap and Envelope Bounds for `gridTentPattern`.** -/
theorem compactSourceL1Gap_gridTentPattern_le (g : C_c(ℝ, ℝ)) {R Mg L : ℝ} (hR : 0 ≤ R)
    (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
    let B : ℝ := R + 2
    let MG : ℝ := Real.exp (3 * B / 2) * Mg
    let Mf : ℝ := Real.exp (3 * B / 2) * (MG + 2 * L)
    let Kf : ℝ := Real.exp (3 * B / 2) * (L + 3 / 2 * (MG + 2 * L))
    let d : ℝ := sourceFactorialWidth (n + 1)
    let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / d⌉₊
    (∀ x, |P x| ≤ Mf) ∧
    (∀ x y, |P x - P y| ≤ Kf * |x - y|) ∧
    (∀ x, B < |x| → P x = 0) ∧
    compactSourceL1Gap P g ≤ 2 * B * (Real.exp (3 * B / 2) * (2 * L)) * d := by
  dsimp only
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
  set B := R + 2
  have hB : 0 ≤ B := by linarith
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  set MG := Real.exp (3 * B / 2) * Mg
  have hMG (x : ℝ) : |G x| ≤ MG := by
    by_cases hx : R < |x|
    · simp only [G, hgR x hx, mul_zero, abs_zero]; positivity
    · have hx' := abs_le.mp (le_of_not_gt hx)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hMg x) (abs_nonneg _) (Real.exp_pos _).le
  set Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  set Kf := Real.exp (3 * B / 2) * (L + 3 / 2 * (MG + 2 * L))
  set d := sourceFactorialWidth (n + 1)
  have hd : 0 < d := sourceFactorialWidth_pos (by omega)
  have hd1 : d ≤ 1 := sourceFactorialWidth_le_one (by omega)
  set M := ⌈2 * (R + 1) / d⌉₊
  have hM1 : 2 * (R + 1) ≤ M * d := by
    have := Nat.le_ceil (2 * (R + 1) / d)
    rw [div_le_iff₀ hd] at this; exact this
  have hM2 : M * d ≤ 2 * (R + 1) + d := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * (R + 1) / d by positivity)
    have h2 := mul_lt_mul_of_pos_right this hd
    rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h2
    exact h2.le
  set a := -(R + 1)
  have hgz {x : ℝ} (hx : R < |x|) : G x = 0 := by simp only [G, hgR x hx, mul_zero]
  have hGa : G a = 0 := hgz (by rw [abs_of_neg (by linarith : a < 0)]; simp only [a]; linarith)
  have hGM : G (a + M * d) = 0 := hgz (by rw [abs_of_pos (by simp only [a]; linarith)]; simp only [a]; linarith)
  have hout : ∀ x, x ≤ a ∨ a + M * d ≤ x → G x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact hgz (by rw [abs_of_neg (by simp only [a] at hx; linarith)]; simp only [a] at hx; linarith)
    · exact hgz (by rw [abs_of_pos (by simp only [a] at hx; linarith)]; simp only [a] at hx; linarith)
  set F := gridInterpolant G a d M
  have hrep (x : ℝ) : gridTentPattern G n a M x = Real.exp (3 * x / 2) * F x :=
    gridTentPattern_apply n hGa hGM x
  have hFG (x : ℝ) : |F x - G x| ≤ 2 * L * d := abs_gridInterpolant_sub_le hGL hd hGa hout x
  have hFL : ∀ x y, |F x - F y| ≤ L * |x - y| := gridInterpolant_lipschitz hGL hd M
  have hF0 : ∀ x, B < |x| → F x = 0 := by
    intro x hx
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hx; linarith) with hneg | hpos
    · rw [abs_of_neg hneg] at hx
      exact gridInterpolant_of_le G a hd M (by simp only [a]; linarith)
    · rw [abs_of_pos hpos] at hx
      show gridInterpolant G a d M x = 0
      rw [gridInterpolant_of_ge G a hd M (by simp only [a]; linarith), hGM, hGa, sub_zero]
  have hFM (x : ℝ) : |F x| ≤ MG + 2 * L := by
    have h1 := hFG x
    have h2 := hMG x
    have h3 : 2 * L * d ≤ 2 * L := by nlinarith
    calc |F x| ≤ |F x - G x| + |G x| := by
          have := abs_sub_abs_le_abs_sub (F x) (G x); linarith
      _ ≤ _ := by linarith
  have hfM (x : ℝ) : |gridTentPattern G n a M x| ≤ Mf := by
    rw [hrep]
    by_cases hx : B < |x|
    · rw [hF0 x hx, mul_zero, abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hx' := abs_le.mp (le_of_not_gt hx)
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hFM x) (abs_nonneg _) (Real.exp_pos _).le
  have hfL : ∀ x y, |gridTentPattern G n a M x - gridTentPattern G n a M y| ≤ Kf * |x - y| := by
    intro x y; rw [hrep, hrep]; exact expWeight_mul_lipschitz hB hFL hFM hF0 x y
  have hf0 : ∀ x, B < |x| → gridTentPattern G n a M x = 0 := by
    intro x hx; rw [hrep, hF0 x hx, mul_zero]
  have hg0 : ∀ x, B < |x| → g x = 0 := fun x hx => hgR x (by linarith)
  refine ⟨hfM, hfL, hf0, ?_⟩
  have hpt (x : ℝ) : |gridTentPattern G n a M x - g x| ≤
      (Icc (-B) B).indicator (fun _ => Real.exp (3 * B / 2) * (2 * L * d)) x := by
    by_cases hx : B < |x|
    · rw [hf0 x hx, hg0 x hx, sub_zero, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) x
    · have hx' := abs_le.mp (le_of_not_gt hx)
      rw [Set.indicator_of_mem (by exact ⟨hx'.1, hx'.2⟩), hrep]
      have hgG : g x = Real.exp (3 * x / 2) * G x := by
        simp only [G, ← mul_assoc, ← Real.exp_add]; ring_nf; simp
      rw [hgG, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hFG x) (abs_nonneg _) (Real.exp_pos _).le
  have hint : Integrable fun x => |gridTentPattern G n a M x - g x| :=
    ((gridTentPattern G n a M - g).continuous.integrable_of_hasCompactSupport
      (gridTentPattern G n a M - g).hasCompactSupport).abs
  unfold compactSourceL1Gap
  calc (∫ x, |gridTentPattern G n a M x - g x|) ≤
      ∫ x, (Icc (-B) B).indicator (fun _ => Real.exp (3 * B / 2) * (2 * L * d)) x :=
        integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const measure_Icc_lt_top.ne)) hpt
    _ = 2 * B * (Real.exp (3 * B / 2) * (2 * L)) * d := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring

/-- **Quantitative Finite-Scale Complete-Form Approximation for `gridTentPattern`.**
At every arithmetic scale `n : ℕ`, the single-scale grid tent pattern of `G(x) = e^{-3x/2} g(x)`
approximates `compactFullWeilEnergy g` within `gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)`. -/
theorem abs_compactFullWeilEnergy_gridTentPattern_sub_le (g : C_c(ℝ, ℝ)) {R Mg Kg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    |compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) -
      compactFullWeilEnergy g| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hKg0 : 0 ≤ Kg := by have := (abs_nonneg _).trans (hKg 1 0); norm_num at this; exact this
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  obtain ⟨hfM, hfL, hf0, hgap⟩ := compactSourceL1Gap_gridTentPattern_le g hR hgR hMg hGL n
  set B := R + 2
  set MG := Real.exp (3 * B / 2) * Mg
  set Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  set Kf := Real.exp (3 * B / 2) * (L + 3 / 2 * (MG + 2 * L))
  set N := compactFullWeilPrimeCutoff B
  set Const := (Mf + Mg) * (|EF.gammaBracket 0| + 2 * mass N) + (Kf + Kg) * archWeightFirstMoment
  have hConst : 0 ≤ Const := add_nonneg (mul_nonneg (by positivity)
    (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (mass_nonneg N))))
    (mul_nonneg (by positivity) archWeightFirstMoment_nonneg)
  have hcut := primeCutoff_large_of_radius B
  set P := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x) n (-(R + 1))
    ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  have hg0 : ∀ x, B < |x| → g x = 0 := fun x hx => hgR x (by linarith)
  have hft : ∀ x, cutoff N ≤ x → autocorr P x = 0 := fun x hx =>
    autocorr_eq_zero_of_far hf0 (by rw [abs_of_pos (by linarith)]; linarith)
  have hgt : ∀ x, cutoff N ≤ x → autocorr g x = 0 := fun x hx =>
    autocorr_eq_zero_of_far hg0 (by rw [abs_of_pos (by linarith)]; linarith)
  have hQ := compactFullWeilEnergy_sub_le_L1 P g hfM hMg hfL hKg N hft hgt
  calc |compactFullWeilEnergy P - compactFullWeilEnergy g|
      ≤ compactSourceL1Gap P g * Const := hQ
    _ ≤ (2 * B * (Real.exp (3 * B / 2) * (2 * L)) * sourceFactorialWidth (n + 1)) * Const :=
        mul_le_mul_of_nonneg_right hgap hConst
    _ = gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
        unfold gridTentApproximationConstant; ring

/-- **Explicit `1 / (12 (n + 1))` Complete-Form Approximation Bound for `gridTentPattern`.** -/
theorem abs_compactFullWeilEnergy_gridTentPattern_sub_le_inv_scale (g : C_c(ℝ, ℝ)) {R Mg Kg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    |compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) -
      compactFullWeilEnergy g| ≤
      gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hKg0 : 0 ≤ Kg := by have := (abs_nonneg _).trans (hKg 1 0); norm_num at this; exact this
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  have hC := gridTentApproximationConstant_nonneg hR hMg0 hKg0 hL0
  have hd : sourceFactorialWidth (n + 1) ≤ 1 / (12 * ((n : ℝ) + 1)) := by
    have := (sourceFactorialWidth_bounds (N := n + 1) (by omega)).2
    push_cast at this; exact this
  refine (abs_compactFullWeilEnergy_gridTentPattern_sub_le g hR hgR hMg hKg hGL n).trans ?_
  calc gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1)
      ≤ gridTentApproximationConstant R Mg Kg L * (1 / (12 * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hd hC
    _ = gridTentApproximationConstant R Mg Kg L / (12 * ((n : ℝ) + 1)) := by ring

/-- **Quantitative Finite-Scale `fullZeroForm` Approximation for `gridTentPattern`.** -/
theorem abs_fullZeroForm_gridTentPattern_sub_le (g : C_c(ℝ, ℝ)) {R Mg Kg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    |fullZeroForm (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) -
      fullZeroForm g| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
  rw [fullZeroForm_eq_compactFullWeilEnergy, fullZeroForm_eq_compactFullWeilEnergy]
  exact abs_compactFullWeilEnergy_gridTentPattern_sub_le g hR hgR hMg hKg hGL n

/-- **Quantitative Finite-Scale `L²`-Mass Approximation for `gridTentPattern`.** -/
theorem abs_integral_sq_gridTentPattern_sub_le (g : C_c(ℝ, ℝ)) {R Mg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n : ℕ) :
    |(∫ x, (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊ x) ^ 2) -
      ∫ x, g x ^ 2| ≤
      gridTentMassApproximationConstant R Mg L * sourceFactorialWidth (n + 1) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hL0 : 0 ≤ L := by have := (abs_nonneg _).trans (hGL 1 0); norm_num at this; exact this
  obtain ⟨hfM, -, -, hgap⟩ := compactSourceL1Gap_gridTentPattern_le g hR hgR hMg hGL n
  set P := gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x) n (-(R + 1))
    ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  have hac := autocorr_sub_le_L1 P g hfM hMg 0
  rw [RHTower.AutocorrelationKrein.autocorr_zero_eq P,
    RHTower.AutocorrelationKrein.autocorr_zero_eq g] at hac
  set B := R + 2
  set MG := Real.exp (3 * B / 2) * Mg
  set Mf := Real.exp (3 * B / 2) * (MG + 2 * L)
  have hB : 0 ≤ B := by linarith
  have hMM : 0 ≤ Mf + Mg := by positivity
  calc |(∫ x, P x ^ 2) - ∫ x, g x ^ 2|
      ≤ (Mf + Mg) * compactSourceL1Gap P g := hac
    _ ≤ (Mf + Mg) * (2 * B * (Real.exp (3 * B / 2) * (2 * L)) * sourceFactorialWidth (n + 1)) :=
        mul_le_mul_of_nonneg_left hgap hMM
    _ = gridTentMassApproximationConstant R Mg L * sourceFactorialWidth (n + 1) := by
        unfold gridTentMassApproximationConstant; ring

/-- **`L²`-Mass Convergence of `gridTentPattern`.** -/
theorem tendsto_integral_sq_gridTentPattern (g : C_c(ℝ, ℝ)) {R Mg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|) :
    Tendsto (fun n : ℕ => ∫ x, (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * g x)
        n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊ x) ^ 2)
      atTop (𝓝 (∫ x, g x ^ 2)) := by
  have hdn : Tendsto (fun n : ℕ => sourceFactorialWidth (n + 1)) atTop (𝓝 0) := by
    have hub : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 12 : ℝ)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    refine squeeze_zero (fun n => (sourceFactorialWidth_pos (by omega)).le) (fun n => ?_) hub
    have := (sourceFactorialWidth_bounds (N := n + 1) (by omega)).2
    push_cast at this; exact this
  have hlim := hdn.const_mul (gridTentMassApproximationConstant R Mg L)
  rw [mul_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs]
  exact abs_integral_sq_gridTentPattern_sub_le g hR hgR hMg hGL n

/-- **Quantitative Joint Approximation for `smoothGridTentDetector` Across All Five Realizations.** -/
theorem abs_smoothGridTentDetector_sub_compactFullWeilEnergy_le (g : C_c(ℝ, ℝ)) {R Mg Kg L : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (n q : ℕ) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
    let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
    let err : ℝ := gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) +
      1 / ((q : ℝ) + 1)
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest D D)).re - compactFullWeilEnergy g| ≤ err ∧
    |(zetaZeroConfig.W D D).re - fullZeroForm g| ≤ err ∧
    |(configurationSquareMass zetaZeroConfig D -
        configurationReflectionDefect zetaZeroConfig D) - fullZeroForm g| ≤ err := by
  dsimp only
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
  set M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
  set D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
  have h1 := abs_compactFullWeilEnergy_gridTentPattern_sub_le g hR hgR hMg hKg hGL n
  obtain ⟨hD1, hD2, hD3⟩ := smoothGridTentDetector_fullWeil_approximation G n (-(R + 1)) M q
  have hW : |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
      (EF.weilTest D D)).re - compactFullWeilEnergy g| ≤
      gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) +
        1 / ((q : ℝ) + 1) := by
    calc |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re - compactFullWeilEnergy g|
        ≤ |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re - compactFullWeilEnergy P| +
          |compactFullWeilEnergy P - compactFullWeilEnergy g| := abs_sub_le _ _ _
      _ ≤ 1 / ((q : ℝ) + 1) +
          gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) :=
          add_le_add hD1 h1
      _ = _ := by ring
  refine ⟨hW, ?_, ?_⟩
  · rw [hD2, fullZeroForm_eq_compactFullWeilEnergy g]
    exact hW
  · have hsub : configurationSquareMass zetaZeroConfig D -
        configurationReflectionDefect zetaZeroConfig D = (zetaZeroConfig.W D D).re := by
      linarith [hD3]
    rw [hsub, hD2, fullZeroForm_eq_compactFullWeilEnergy g]
    exact hW

/-! ## Section 2: Channel-by-Channel Parity Split on `C_c(ℝ, ℝ)` and Odd/Even Critical Projections -/

/-- The even part `x ↦ (f(x) + f(-x)) / 2` of a compactly supported continuous real source `f ∈ C_c(ℝ, ℝ)`. -/
def evenCompactSource (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨RHTower.evenPartReal f, (f.continuous.add (f.continuous.comp continuous_neg)).div_const 2⟩,
    RHTower.hasCompactSupport_evenPartReal f.hasCompactSupport⟩

/-- The odd part `x ↦ (f(x) - f(-x)) / 2` of a compactly supported continuous real source `f ∈ C_c(ℝ, ℝ)`. -/
def oddCompactSource (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨RHTower.oddPartReal f, (f.continuous.sub (f.continuous.comp continuous_neg)).div_const 2⟩,
    RHTower.hasCompactSupport_oddPartReal f.hasCompactSupport⟩

@[simp] theorem evenCompactSource_apply (f : C_c(ℝ, ℝ)) (x : ℝ) :
    evenCompactSource f x = RHTower.evenPartReal f x := rfl

@[simp] theorem oddCompactSource_apply (f : C_c(ℝ, ℝ)) (x : ℝ) :
    oddCompactSource f x = RHTower.oddPartReal f x := rfl

theorem evenCompactSource_neg (f : C_c(ℝ, ℝ)) (x : ℝ) :
    evenCompactSource f (-x) = evenCompactSource f x :=
  RHTower.evenPartReal_neg f x

theorem oddCompactSource_neg (f : C_c(ℝ, ℝ)) (x : ℝ) :
    oddCompactSource f (-x) = -oddCompactSource f x :=
  RHTower.oddPartReal_neg f x

theorem evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) (x : ℝ) :
    evenCompactSource f x + oddCompactSource f x = f x :=
  RHTower.evenPartReal_add_oddPartReal f x

/-- **Exact Pointwise Autocorrelation Parity Split on `C_c(ℝ, ℝ)`.**
For every compactly supported continuous real source `f ∈ C_c(ℝ, ℝ)` and every shift `t ∈ ℝ`,
the cross autocorrelations between the even and odd parts cancel identically upon integration,
giving `autocorr (evenCompactSource f) t + autocorr (oddCompactSource f) t = autocorr f t`. -/
theorem autocorr_evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) (t : ℝ) :
    autocorr (evenCompactSource f) t + autocorr (oddCompactSource f) t = autocorr f t := by
  have hi_e : Integrable fun x => evenCompactSource f x * evenCompactSource f (x + t) :=
    ((evenCompactSource f).continuous.mul
      ((evenCompactSource f).continuous.comp (continuous_id.add_const t))).integrable_of_hasCompactSupport
      (evenCompactSource f).hasCompactSupport.mul_right
  have hi_o : Integrable fun x => oddCompactSource f x * oddCompactSource f (x + t) :=
    ((oddCompactSource f).continuous.mul
      ((oddCompactSource f).continuous.comp (continuous_id.add_const t))).integrable_of_hasCompactSupport
      (oddCompactSource f).hasCompactSupport.mul_right
  have hi_f1 : Integrable fun x => f x * f (x + t) :=
    (f.continuous.mul (f.continuous.comp (continuous_id.add_const t))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hi_f2 : Integrable fun x => f (-x) * f (-x - t) := by
    have h := (f.continuous.mul
      (f.continuous.comp (continuous_id.sub (continuous_const : Continuous fun _ : ℝ => t)))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
    exact h.comp_neg
  unfold autocorr
  rw [← integral_add hi_e hi_o]
  have hpt : (fun x => evenCompactSource f x * evenCompactSource f (x + t) +
      oddCompactSource f x * oddCompactSource f (x + t)) =
      fun x => (f x * f (x + t) + f (-x) * f (-x - t)) / 2 := by
    funext x
    simp only [evenCompactSource_apply, oddCompactSource_apply, RHTower.evenPartReal,
      RHTower.oddPartReal]
    rw [show -(x + t) = -x - t by ring]
    ring
  rw [hpt, integral_div, integral_add hi_f1 hi_f2]
  have hneg : (∫ x, f (-x) * f (-x - t)) = ∫ x, f x * f (x - t) :=
    integral_neg_eq_self (fun x => f x * f (x - t)) volume
  have hshift : (∫ x, f x * f (x - t)) = ∫ x, f x * f (x + t) := by
    have h1 := integral_add_right_eq_self (fun x => f (x - t) * f x) t
    simp only [add_sub_cancel_right] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hneg, hshift]
  ring

/-- **Exact `L²`-Mass Orthogonality on `C_c(ℝ, ℝ)`.** -/
theorem integral_sq_evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) :
    (∫ x, (evenCompactSource f x) ^ 2) + (∫ x, (oddCompactSource f x) ^ 2) = ∫ x, (f x) ^ 2 := by
  rw [← RHTower.AutocorrelationKrein.autocorr_zero_eq (evenCompactSource f),
    ← RHTower.AutocorrelationKrein.autocorr_zero_eq (oddCompactSource f),
    ← RHTower.AutocorrelationKrein.autocorr_zero_eq f]
  exact autocorr_evenCompactSource_add_oddCompactSource f 0

/-- **Exact Parity Split of the Signed Prime–Polar Pairing on `C_c(ℝ, ℝ)`.** -/
theorem fullPairing_autocorr_evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) :
    fullPairing (autocorr (evenCompactSource f)) + fullPairing (autocorr (oddCompactSource f)) =
      fullPairing (autocorr f) := by
  obtain ⟨R, hR1, hfR'⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_support_radius f.hasCompactSupport
  have hR0 : 0 ≤ R := by linarith
  have heR : ∀ x, R < |x| → evenCompactSource f x = 0 := fun x hx => by
    simp only [evenCompactSource_apply, RHTower.evenPartReal]
    rw [hfR' x hx, hfR' (-x) (by rwa [abs_neg])]; ring
  have hoR : ∀ x, R < |x| → oddCompactSource f x = 0 := fun x hx => by
    simp only [oddCompactSource_apply, RHTower.oddPartReal]
    rw [hfR' x hx, hfR' (-x) (by rwa [abs_neg])]; ring
  set N := compactFullWeilPrimeCutoff R
  have hcut : 2 * (R + 1) < cutoff N := primeCutoff_large_of_radius R
  have hft : ∀ x, cutoff N ≤ x → autocorr f x = 0 := fun x hx =>
    autocorr_eq_zero_of_far hfR' (by rw [abs_of_pos (by linarith)]; linarith)
  have het : ∀ x, cutoff N ≤ x → autocorr (evenCompactSource f) x = 0 := fun x hx =>
    autocorr_eq_zero_of_far heR (by rw [abs_of_pos (by linarith)]; linarith)
  have hot : ∀ x, cutoff N ≤ x → autocorr (oddCompactSource f) x = 0 := fun x hx =>
    autocorr_eq_zero_of_far hoR (by rw [abs_of_pos (by linarith)]; linarith)
  rw [fullPairing_eq_pairing_of_tail _ N het, fullPairing_eq_pairing_of_tail _ N hot,
    fullPairing_eq_pairing_of_tail _ N hft]
  have hei : IntegrableOn (fun x => polarDensity x * autocorr (evenCompactSource f) x) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul (continuous_autocorr_compact (evenCompactSource f))).integrableOn_Icc
  have hoi : IntegrableOn (fun x => polarDensity x * autocorr (oddCompactSource f) x) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul (continuous_autocorr_compact (oddCompactSource f))).integrableOn_Icc
  unfold pairing
  have hsum : (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * autocorr (evenCompactSource f) (Real.log (n : ℝ))) +
      (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * autocorr (oddCompactSource f) (Real.log (n : ℝ))) =
      ∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * autocorr f (Real.log (n : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← mul_add, autocorr_evenCompactSource_add_oddCompactSource]
  have hint : (∫ x in Icc 0 (cutoff N), polarDensity x * autocorr (evenCompactSource f) x) +
      (∫ x in Icc 0 (cutoff N), polarDensity x * autocorr (oddCompactSource f) x) =
      ∫ x in Icc 0 (cutoff N), polarDensity x * autocorr f x := by
    rw [← integral_add hei hoi]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    rw [← mul_add, autocorr_evenCompactSource_add_oddCompactSource]
  linarith

/-- If `f ∈ C_c(ℝ, ℝ)` is Lipschitz with constant `K`, then `evenCompactSource f` and
`oddCompactSource f` are also Lipschitz with constant `K`. -/
theorem lipschitz_evenCompactSource_and_oddCompactSource (f : C_c(ℝ, ℝ)) {K : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    (∀ x y, |evenCompactSource f x - evenCompactSource f y| ≤ K * |x - y|) ∧
    (∀ x y, |oddCompactSource f x - oddCompactSource f y| ≤ K * |x - y|) := by
  constructor <;> intro x y
  · simp only [evenCompactSource_apply, RHTower.evenPartReal]
    rw [show (f x + f (-x)) / 2 - (f y + f (-y)) / 2 = ((f x - f y) + (f (-x) - f (-y))) / 2 by ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 := hf x y
    have h2 : |f (-x) - f (-y)| ≤ K * |x - y| := by
      simpa only [show -x - -y = -(x - y) by ring, abs_neg] using hf (-x) (-y)
    have h3 := abs_add_le (f x - f y) (f (-x) - f (-y))
    linarith
  · simp only [oddCompactSource_apply, RHTower.oddPartReal]
    rw [show (f x - f (-x)) / 2 - (f y - f (-y)) / 2 = ((f x - f y) - (f (-x) - f (-y))) / 2 by ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 := hf x y
    have h2 : |f (-x) - f (-y)| ≤ K * |x - y| := by
      simpa only [show -x - -y = -(x - y) by ring, abs_neg] using hf (-x) (-y)
    have h3 := abs_sub (f x - f y) (f (-x) - f (-y))
    linarith

/-- **Exact Parity Split of `biScaleLevyEnergy` on Lipschitz Sources in `C_c(ℝ, ℝ)`.** -/
theorem biScaleLevyEnergy_evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) {K : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    biScaleLevyEnergy (evenCompactSource f) + biScaleLevyEnergy (oddCompactSource f) =
      biScaleLevyEnergy f := by
  obtain ⟨heL, hoL⟩ := lipschitz_evenCompactSource_and_oddCompactSource f hf
  have hei := integrableOn_levy_of_lipschitz (evenCompactSource f) heL
  have hoi := integrableOn_levy_of_lipschitz (oddCompactSource f) hoL
  unfold biScaleLevyEnergy
  rw [← integral_add hei hoi]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have h0 := autocorr_evenCompactSource_add_oddCompactSource f 0
  have ht := autocorr_evenCompactSource_add_oddCompactSource f t
  rw [← add_mul, ← h0, ← ht]
  ring

/-- **Exact Parity Split of `compactFullWeilEnergy` and `fullZeroForm` on Lipschitz Sources in `C_c(ℝ, ℝ)`.** -/
theorem compactFullWeilEnergy_eq_evenCompactSource_add_oddCompactSource (f : C_c(ℝ, ℝ)) {K : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    compactFullWeilEnergy f =
      compactFullWeilEnergy (evenCompactSource f) + compactFullWeilEnergy (oddCompactSource f) ∧
    fullZeroForm f =
      fullZeroForm (evenCompactSource f) + fullZeroForm (oddCompactSource f) := by
  obtain ⟨heL, hoL⟩ := lipschitz_evenCompactSource_and_oddCompactSource f hf
  have h1 : compactFullWeilEnergy f =
      compactFullWeilEnergy (evenCompactSource f) + compactFullWeilEnergy (oddCompactSource f) := by
    unfold compactFullWeilEnergy
    rw [re_weilFullFunctional_eq_of_compact_finite_jump f (integrableOn_levy_of_lipschitz f hf),
      re_weilFullFunctional_eq_of_compact_finite_jump (evenCompactSource f)
        (integrableOn_levy_of_lipschitz (evenCompactSource f) heL),
      re_weilFullFunctional_eq_of_compact_finite_jump (oddCompactSource f)
        (integrableOn_levy_of_lipschitz (oddCompactSource f) hoL)]
    have h0 := autocorr_evenCompactSource_add_oddCompactSource f 0
    have hJ := biScaleLevyEnergy_evenCompactSource_add_oddCompactSource f hf
    have hP := fullPairing_autocorr_evenCompactSource_add_oddCompactSource f
    rw [← h0, ← hJ, ← hP]
    ring
  refine ⟨h1, ?_⟩
  rw [fullZeroForm_eq_compactFullWeilEnergy, fullZeroForm_eq_compactFullWeilEnergy,
    fullZeroForm_eq_compactFullWeilEnergy, h1]

/-- Because `criticalTruncatedSource V S b` vanishes on `[0, ∞)`, `g^V(x)` and `g^V(-x)` have
disjoint supports for every `x ∈ ℝ`. -/
theorem criticalTruncatedSource_mul_neg_eq_zero (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedSource V S b x * criticalTruncatedSource V S b (-x) = 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := by linarith
    have hz : criticalTruncatedSource V S b (-x) = 0 := by
      simp only [criticalTruncatedSource, criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show -x ∉ Iic 0 from not_le.mpr hpos), mul_zero]
    rw [hz, mul_zero]
  · have hz : criticalTruncatedSource V S b 0 = 0 := by
      simp only [criticalTruncatedSource, criticalCollaredSource, neg_zero, Real.exp_zero, sub_self,
        Real.smoothTransition.zero_of_nonpos le_rfl, zero_mul, mul_zero]
    rw [neg_zero, hz, mul_zero]
  · have hz : criticalTruncatedSource V S b x = 0 := by
      simp only [criticalTruncatedSource, criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show x ∉ Iic 0 from not_le.mpr hx), mul_zero]
    rw [hz, zero_mul]

/-- **Exact Half-Mass Law for the Odd and Even Projections of `criticalTruncatedTest`.**
Because `criticalTruncatedSource V S b` is supported on `(-∞, 0]` and vanishes at `0`, its odd
and even projections each carry exact half of the `L²` mass of `criticalTruncatedSource V S b`. -/
theorem integral_sq_oddCompactSource_criticalTruncatedTest {V : ℝ} (hVpos : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ x, (oddCompactSource (criticalTruncatedTest hVpos S b) x) ^ 2) =
      (1 / 2) * ∫ x, criticalTruncatedSource V S b x ^ 2 ∧
    (∫ x, (evenCompactSource (criticalTruncatedTest hVpos S b) x) ^ 2) =
      (1 / 2) * ∫ x, criticalTruncatedSource V S b x ^ 2 := by
  set g := criticalTruncatedTest hVpos S b
  have hg_sq : Integrable fun x => g x ^ 2 :=
    (g.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq g.hasCompactSupport)
  have hg_neg_sq : Integrable fun x => g (-x) ^ 2 := hg_sq.comp_neg
  have hneg_eq : (∫ x, g (-x) ^ 2) = ∫ x, g x ^ 2 :=
    integral_neg_eq_self (fun x => g x ^ 2) volume
  have hpt_odd : (fun x => (oddCompactSource g x) ^ 2) =
      fun x => (g x ^ 2 + g (-x) ^ 2) / 4 := by
    funext x
    simp only [oddCompactSource_apply, RHTower.oddPartReal]
    have h0 : g x * g (-x) = 0 := criticalTruncatedSource_mul_neg_eq_zero V S b x
    nlinarith
  have hpt_even : (fun x => (evenCompactSource g x) ^ 2) =
      fun x => (g x ^ 2 + g (-x) ^ 2) / 4 := by
    funext x
    simp only [evenCompactSource_apply, RHTower.evenPartReal]
    have h0 : g x * g (-x) = 0 := criticalTruncatedSource_mul_neg_eq_zero V S b x
    nlinarith
  have hod : (∫ x, (oddCompactSource g x) ^ 2) = (1 / 2) * ∫ x, g x ^ 2 := by
    rw [hpt_odd, integral_div, integral_add hg_sq hg_neg_sq, hneg_eq]
    ring
  have hev : (∫ x, (evenCompactSource g x) ^ 2) = (1 / 2) * ∫ x, g x ^ 2 := by
    rw [hpt_even, integral_div, integral_add hg_sq hg_neg_sq, hneg_eq]
    ring
  exact ⟨hod, hev⟩

/-- **`ℓ²` Mass Sandwich for the Odd and Even Projections of `criticalTruncatedTest`.** -/
theorem oddCompactSource_criticalTruncatedTest_mass_bounds {V : ℝ} (hVpos : 0 < V)
    (hV : 2 + factorialWindowLength ≤ V) (S : Finset ℕ) (b : ℕ → ℝ) :
    (criticalCollarMassLower / 2) * (∑ n ∈ S, b n ^ 2) ≤
      ∫ x, (oddCompactSource (criticalTruncatedTest hVpos S b) x) ^ 2 ∧
    (∫ x, (oddCompactSource (criticalTruncatedTest hVpos S b) x) ^ 2) ≤
      (criticalCollarMassUpper / 2) * (∑ n ∈ S, b n ^ 2) := by
  have hhalf := (integral_sq_oddCompactSource_criticalTruncatedTest hVpos S b).1
  have hlo := integral_criticalTruncatedSource_sq_ge hV S b
  have hhi := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
  have hsq : sourceAutocorrelation (criticalTruncatedSource V S b) 0 =
      ∫ x, criticalTruncatedSource V S b x ^ 2 := by
    unfold sourceAutocorrelation; simp only [sub_zero, sq]
  rw [hsq] at hhi
  rw [hhalf]
  exact ⟨by linarith, by linarith⟩

/-- Truncation threshold `V_{0,odd} = max(2 + L, 16 U / A_c)` for the odd and even projections of
a doubly collared critical source. -/
def criticalOddTruncationThreshold : ℝ :=
  max (2 + factorialWindowLength) (16 * criticalCollarMassUpper / criticalCollarMassLower)

/-- Logarithmic offset `3 + log(1 / η(A_c / 4, D_c))` for the odd and even projections of a doubly
collared critical source. -/
def criticalOddTruncatedArchLogOffset : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff (criticalCollarMassLower / 4) criticalCollarLowFreqConstant)

theorem admissibleSource_of_compactlySupported (f : C_c(ℝ, ℝ)) :
    AdmissibleSource f := by
  have hc : Continuous fun x => (f x : ℂ) := Complex.continuous_ofReal.comp f.continuous
  have hcs : HasCompactSupport fun x => (f x : ℂ) := f.hasCompactSupport.comp_left Complex.ofReal_zero
  exact ⟨hc.integrable_of_hasCompactSupport hcs, hc.memLp_of_hasCompactSupport hcs⟩

/-- **Logarithmic Archimedean Lévy Coercivity for Both the Odd and Even Projections of
`criticalTruncatedTest`.**
For every scale family `S` with `n + 1 ≥ M ≥ 2`, every `V ≥ criticalOddTruncationThreshold`, and
every `b : ℕ → ℝ`, both `oddCompactSource (criticalTruncatedTest hVpos S b)` and
`evenCompactSource (criticalTruncatedTest hVpos S b)` individually satisfy logarithmic archimedean
Lévy coercivity with slope `criticalTruncatedArchLogSlope / 2`. -/
theorem ofReal_le_oddPartReal_and_evenPartReal_criticalTruncatedLevyEnergy
    (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1)
    {V : ℝ} (hVpos : 0 < V) (hV : criticalOddTruncationThreshold ≤ V) :
    ENNReal.ofReal ((criticalTruncatedArchLogSlope / 2) *
        (Real.log M - criticalOddTruncatedArchLogOffset) * ∑ n ∈ S, b n ^ 2) ≤
      sourceLevyEnergy (oddCompactSource (criticalTruncatedTest hVpos S b)) ∧
    ENNReal.ofReal ((criticalTruncatedArchLogSlope / 2) *
        (Real.log M - criticalOddTruncatedArchLogOffset) * ∑ n ∈ S, b n ^ 2) ≤
      sourceLevyEnergy (evenCompactSource (criticalTruncatedTest hVpos S b)) := by
  set A := criticalCollarMassLower
  set D := criticalCollarLowFreqConstant
  set U := criticalCollarMassUpper
  set η := lowFreqRelativeCutoff (A / 4) D
  set E := ∑ n ∈ S, b n ^ 2
  set g := criticalTruncatedSource V S b
  set g_odd := oddCompactSource (criticalTruncatedTest hVpos S b)
  set g_even := evenCompactSource (criticalTruncatedTest hVpos S b)
  have hA : 0 < A := criticalCollarMassLower_pos
  have hD : 0 < D := criticalCollarLowFreqConstant_pos
  have hη : 0 < η := lowFreqRelativeCutoff_pos (by positivity) hD
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hV1 : 2 + factorialWindowLength ≤ V := (le_max_left _ _).trans hV
  have hV2 : 16 * U / A ≤ V := (le_max_right _ _).trans hV
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - criticalOddTruncatedArchLogOffset = Real.log R - 3 := by
    unfold criticalOddTruncatedArchLogOffset
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]; ring
  rw [hlogR]
  have hs : 0 < criticalTruncatedArchLogSlope := criticalTruncatedArchLogSlope_pos
  rcases le_or_gt (Real.log R - 3) 0 with hneg | hpos
  · have hnp : (criticalTruncatedArchLogSlope / 2) * (Real.log R - 3) * E ≤ 0 := by
      have : (criticalTruncatedArchLogSlope / 2) * (Real.log R - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
      nlinarith
    rw [ENNReal.ofReal_of_nonpos hnp]
    exact ⟨zero_le, zero_le⟩
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  have hg := admissibleSource_criticalTruncatedSource V S b
  have hgo := admissibleSource_of_compactlySupported g_odd
  have hge := admissibleSource_of_compactlySupported g_even
  have hgc := admissibleSource_criticalCollaredSource S b
  have hh := admissibleSource_criticalTruncationTail V S b
  have hmi := integrable_levySourceSpectralDensity hg
  have hmoi := integrable_levySourceSpectralDensity hgo
  have hmei := integrable_levySourceSpectralDensity hge
  have hhi := integrable_levySourceSpectralDensity hh
  have hsplit : ∀ t, levySourceSpectralDensity g t ≤
      2 * levySourceSpectralDensity (criticalCollaredSource S b) t +
        2 * levySourceSpectralDensity (criticalTruncationTail V S b) t := by
    intro t
    have hfun : (fun x => (g x : ℂ)) = (fun x => (criticalCollaredSource S b x : ℂ)) +
        (-1 : ℂ) • fun x => (criticalTruncationTail V S b x : ℂ) := by
      funext x
      have := criticalTruncatedSource_add_tail V S b x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g]
      rw [← this]; push_cast; ring
    unfold levySourceSpectralDensity
    rw [hfun, RHTower.WeilSpectral.paperFT_add_smul_real hgc.1 hh.1, neg_one_mul, ← sub_eq_add_neg]
    have := norm_sub_le (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t)
      (paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t)
    nlinarith [norm_nonneg (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t -
      paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t),
      sq_nonneg (‖paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t‖ -
        ‖paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t‖),
      norm_nonneg (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t),
      norm_nonneg (paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t)]
  have hlowc : ∀ t ∈ Icc (-R) R, levySourceSpectralDensity (criticalCollaredSource S b) t ≤
      2 * D ^ 2 / M * E := by
    intro t ht
    refine norm_sq_paperFT_criticalCollaredSource_le S b hM hS ?_
    have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
    calc |t| ≤ R := abs_le.mpr ht
      _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
  have htail := integral_criticalTruncationTail_sq_le (V := V) (by linarith [factorialWindowLength_pos]) S b
  have hhtot := integral_levySourceSpectralDensity hh
  have hhnn : ∀ t, 0 ≤ levySourceSpectralDensity (criticalTruncationTail V S b) t := fun t => sq_nonneg _
  have hlow : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
      A / 4 * E + 2 * (U / V * E) := by
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
        ∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
          2 * levySourceSpectralDensity (criticalTruncationTail V S b) t) :=
      setIntegral_mono_on hmi.integrableOn ((integrableOn_const (by simp)).add
        (hhi.integrableOn.const_mul 2)) measurableSet_Icc fun t ht => (hsplit t).trans
          (by gcongr; exact hlowc t ht)
    have h2 : (∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
        2 * levySourceSpectralDensity (criticalTruncationTail V S b) t)) ≤
        (2 * R) * (2 * (2 * D ^ 2 / M * E)) +
          2 * (2 * Real.pi * ∫ x, criticalTruncationTail V S b x ^ 2) := by
      have hc : IntegrableOn (fun _ : ℝ => 2 * (2 * D ^ 2 / M * E)) (Icc (-R) R) :=
        integrableOn_const (by simp)
      rw [integral_add hc (hhi.integrableOn.const_mul 2), setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, integral_const_mul, ← hhtot]
      rw [show R - -R = 2 * R by ring]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hhi (Eventually.of_forall hhnn)) (by norm_num))
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) ≤ (A / 4) / 2 * E := by
      have := low_band_plancherel_energy_le_half_arch (A := A / 4) hD hE hM
      calc 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) =
            (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E / (M : ℝ)) := by ring
        _ ≤ _ := this
    calc 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * (2 * D ^ 2 / M * E)) +
            2 * (2 * Real.pi * ∫ x, criticalTruncationTail V S b x ^ 2)) := by
          gcongr; exact h1.trans h2
      _ = 2 * (1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E))) +
            2 * ∫ x, criticalTruncationTail V S b x ^ 2 := by field_simp
      _ ≤ 2 * ((A / 4) / 2 * E) + 2 * (U / V * E) := by gcongr
      _ = A / 4 * E + 2 * (U / V * E) := by ring
  have hUV : 2 * (U / V * E) ≤ A / 8 * E := by
    have : U / V ≤ A / 16 := by
      rw [div_le_iff₀ hVpos]
      have := (div_le_iff₀ hA).mp hV2
      linarith
    nlinarith
  have hspec_split : ∀ t, levySourceSpectralDensity g t =
      levySourceSpectralDensity g_even t + levySourceSpectralDensity g_odd t := by
    intro t
    unfold levySourceSpectralDensity
    exact RHTower.norm_sq_paperFT_ofReal_eq_even_add_odd
      (criticalTruncatedTest hVpos S b).continuous
      (criticalTruncatedTest hVpos S b).hasCompactSupport t
  have hle_odd : ∀ t, levySourceSpectralDensity g_odd t ≤ levySourceSpectralDensity g t := fun t => by
    rw [hspec_split t]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hle_even : ∀ t, levySourceSpectralDensity g_even t ≤ levySourceSpectralDensity g t := fun t => by
    rw [hspec_split t]; exact le_add_of_nonneg_right (sq_nonneg _)
  have hlow_odd : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g_odd t ≤
      3 * A / 8 * E := by
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g_odd t) ≤
        ∫ t in Icc (-R) R, levySourceSpectralDensity g t :=
      setIntegral_mono_on hmoi.integrableOn hmi.integrableOn measurableSet_Icc fun t _ => hle_odd t
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hpi.le
    linarith [hlow, hUV]
  have hlow_even : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g_even t ≤
      3 * A / 8 * E := by
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g_even t) ≤
        ∫ t in Icc (-R) R, levySourceSpectralDensity g t :=
      setIntegral_mono_on hmei.integrableOn hmi.integrableOn measurableSet_Icc fun t _ => hle_even t
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hpi.le
    linarith [hlow, hUV]
  obtain ⟨hmass_odd, hmass_even⟩ := integral_sq_oddCompactSource_criticalTruncatedTest hVpos S b
  have hmass_g := integral_criticalTruncatedSource_sq_ge hV1 S b
  have htot_odd := integral_levySourceSpectralDensity hgo
  have htot_even := integral_levySourceSpectralDensity hge
  have hsplit_odd := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmoi
  have hsplit_even := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmei
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhigh_odd : A / 8 * E ≤
      1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g_odd t := by
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g_odd t = ∫ y, g_odd y ^ 2 := by
      rw [htot_odd]; field_simp
    rw [← hsplit_odd, mul_add] at h1
    linarith [hmass_odd, hmass_g, hlow_odd]
  have hhigh_even : A / 8 * E ≤
      1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g_even t := by
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g_even t = ∫ y, g_even y ^ 2 := by
      rw [htot_even]; field_simp
    rw [← hsplit_even, mul_add] at h1
    linarith [hmass_even, hmass_g, hlow_even]
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  have hfac : (criticalTruncatedArchLogSlope / 2) * (Real.log R - 3) * E =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) * (A / 8 * E) := by
    unfold criticalTruncatedArchLogSlope; ring
  rw [hfac, ENNReal.ofReal_mul hc0]
  exact ⟨(mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hhigh_odd) zero_le).trans
      (sourceLevyEnergy_ge_highBand hgo hR1),
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hhigh_even) zero_le).trans
      (sourceLevyEnergy_ge_highBand hge hR1)⟩

/-! ## Section 3: Norm-Controlled Subfamily Transfer and Graded Grid-Tent Receiver Laws -/

/-- A family of compact sources `ℱ : ℝ → Set C_c(ℝ, ℝ)` indexed by aperture `r > 0` has
**`(α, β)`-norm-controlled receiver transfer** if every odd `F ∈ C_c²(ℝ, ℝ)` supported in `[-r, r]`
can be approximated in `compactFullWeilEnergy` to within any `δ > 0` by a source `g ∈ ℱ r` whose
`L²` mass satisfies `∫ g² ≤ α e^{2β r} ∫ F² + δ`. -/
def HasNormControlledReceiverTransfer (ℱ : ℝ → Set C_c(ℝ, ℝ)) (α β : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
    (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
    ∀ δ : ℝ, 0 < δ → ∃ g ∈ ℱ r,
      |compactFullWeilEnergy g - fullZeroForm F| ≤ δ ∧
      (∫ x, g x ^ 2) ≤ α * Real.exp (2 * β * r) * (∫ x, F x ^ 2) + δ

/-- **Graded Norm-Controlled Subfamily Transfer Theorem.**
If `ℱ` has `(α, β)`-norm-controlled receiver transfer (`α, β ≥ 0`) and satisfies a graded floor
`compactFullWeilEnergy g ≥ -C e^{2σ r} ∫ g²` (`C, σ ≥ 0`) on `g ∈ ℱ r`, then the zero width of
`ζ` satisfies `zetaZeroWidth ≤ σ + β`. -/
theorem zetaZeroWidth_le_of_normControlled_subfamily_transfer
    {ℱ : ℝ → Set C_c(ℝ, ℝ)} {α β σ C : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (htransfer : HasNormControlledReceiverTransfer ℱ α β)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ g ∈ ℱ r,
      -(C * Real.exp (2 * σ * r) * ∫ x, g x ^ 2) ≤ compactFullWeilEnergy g) :
    zetaZeroWidth ≤ σ + β := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C * α) (by linarith) ?_
  intro r hr F hF hFc hodd hsupp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set K := C * Real.exp (2 * σ * r) + 1
  have hK : 0 < K := by positivity
  set δ := ε / K
  have hδ : 0 < δ := div_pos hε hK
  obtain ⟨g, hg, happrox, hmass⟩ := htransfer r hr F hF hFc hodd hsupp δ hδ
  have hfg := hfloor r hr g hg
  have h1 := (abs_le.mp happrox).2
  have h2 : C * Real.exp (2 * σ * r) * ∫ x, g x ^ 2 ≤
      C * Real.exp (2 * σ * r) * (α * Real.exp (2 * β * r) * (∫ x, F x ^ 2) + δ) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  have hexp : C * Real.exp (2 * σ * r) * (α * Real.exp (2 * β * r) * (∫ x, F x ^ 2)) =
      C * α * Real.exp (2 * (σ + β) * r) * ∫ x, F x ^ 2 := by
    rw [show 2 * (σ + β) * r = 2 * σ * r + 2 * β * r by ring, Real.exp_add]
    ring
  rw [mul_add, hexp] at h2
  have hδK : (C * Real.exp (2 * σ * r) + 1) * δ = ε := mul_div_cancel₀ ε hK.ne'
  have hδK' : C * Real.exp (2 * σ * r) * δ + δ = ε := by linarith
  linarith

/-- **Subexponential Norm-Controlled Transfer Equivalence (`β = 0`).**
For any family `ℱ` with `(α, 0)`-norm-controlled receiver transfer (`α ≥ 0`) contained in the odd
sector (or on which `compactFullWeilEnergy ≥ 0` holds under `RiemannHypothesis`), `RiemannHypothesis`
is equivalent to a subexponential floor on `ℱ r`. -/
theorem riemannHypothesis_of_subexponential_normControlled_transfer
    {ℱ : ℝ → Set C_c(ℝ, ℝ)} {α : ℝ} (hα : 0 ≤ α)
    (htransfer : HasNormControlledReceiverTransfer ℱ α 0)
    (hfloor : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ g ∈ ℱ r,
      -(C * Real.exp (2 * σ * r) * ∫ x, g x ^ 2) ≤ compactFullWeilEnergy g) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ zetaZeroWidth_nonneg
  refine le_of_forall_pos_le_add fun σ hσ => ?_
  rw [zero_add]
  obtain ⟨C, hC0, hC⟩ := hfloor σ hσ
  have h := zetaZeroWidth_le_of_normControlled_subfamily_transfer hα le_rfl hσ.le hC0 htransfer hC
  rwa [add_zero] at h

/-- **Unconditional `(1, 0)`-Norm-Controlled Receiver Transfer for the Single-Scale Grid Tent Family.**
For every aperture `r > 0`, the single-scale grid tent family `gridTentPattern` on `[-(r+1), r+1]`
approximates every odd receiver test `F ∈ C_c²` supported in `[-r, r]` simultaneously in
`compactFullWeilEnergy` and `L²` mass with `(α, β) = (1, 0)`. -/
theorem hasNormControlledReceiverTransfer_gridTentFamily :
    HasNormControlledReceiverTransfer
      (fun r => {P | ∃ (F : ℝ → ℝ) (n : ℕ), ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
        (∀ x, F (-x) = -F x) ∧ (∀ x, r < |x| → F x = 0) ∧
        P = gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
          n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊})
      1 0 := by
  intro r hr F hF hFc hodd hsupp δ hδ
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  obtain ⟨Mg, hMg⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨Kg, hKg⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
  have hGc : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
  obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport hFc.mul_left (by norm_num)
  have hMg' : ∀ x, |Fc x| ≤ Mg := fun x => by rw [← Real.norm_eq_abs]; exact hMg x
  have hKg' : ∀ x y, |Fc x - Fc y| ≤ Kg * |x - y| := fun x y => by
    have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this
  have hGL' : ∀ x y, |Real.exp (-(3 * x / 2)) * Fc x - Real.exp (-(3 * y / 2)) * Fc y| ≤
      L * |x - y| := fun x y => by
    have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this
  have hlim1 := tendsto_compactFullWeilEnergy_gridTentPattern Fc hr.le hsupp hMg' hKg' hGL'
  have hlim2 := tendsto_integral_sq_gridTentPattern Fc hr.le hsupp hMg' hGL'
  rw [← fullZeroForm_eq_compactFullWeilEnergy Fc] at hlim1
  have hev1 := (tendsto_iff_norm_sub_tendsto_zero.mp hlim1).eventually (eventually_lt_nhds hδ)
  have hev2 := (tendsto_iff_norm_sub_tendsto_zero.mp hlim2).eventually (eventually_lt_nhds hδ)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set P := gridTentPattern G n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊
  refine ⟨P, ⟨F, n, hF, hFc, hodd, hsupp, rfl⟩, ?_, ?_⟩
  · rw [Real.norm_eq_abs] at hn1
    exact hn1.le
  · rw [Real.norm_eq_abs] at hn2
    have h2 : (∫ x, P x ^ 2) - ∫ x, F x ^ 2 ≤ δ := (abs_le.mp hn2.le).2
    rw [mul_zero, zero_mul, Real.exp_zero, one_mul, one_mul]
    linarith

/-- **Graded Grid-Tent Receiver Law.**
If for every aperture `r > 0` and every odd `F ∈ C_c²` supported in `[-r, r]`, the single-scale
grid tent pattern `gridTentPattern` eventually satisfies a floor `-C e^{2σ r} ∫ F²` (`σ ≥ 0`),
then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_eventually_gridTentPattern_odd_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      ∀ᶠ n : ℕ in atTop,
        -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤
          compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
            n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊)) :
    zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  obtain ⟨Mg, hMg⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨Kg, hKg⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
  have hGc : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
  obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport hFc.mul_left (by norm_num)
  have hlim := tendsto_compactFullWeilEnergy_gridTentPattern Fc hr.le hsupp
    (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
    (fun x y => by have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
    (fun x y => by have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
  rw [← fullZeroForm_eq_compactFullWeilEnergy Fc] at hlim
  exact ge_of_tendsto hlim (hfloor r hr F hF hFc hodd hsupp)

/-- **Self-Improving Subexponential Grid-Tent Receiver Bootstrap.**
`RiemannHypothesis` holds if and only if for every `σ > 0` there exists `C : ℝ` such that for
every aperture `r > 0` and every odd `F ∈ C_c²` supported in `[-r, r]`, the single-scale grid
tent pattern eventually satisfies `compactFullWeilEnergy ≥ -C e^{2σ r} ∫ F²`. -/
theorem riemannHypothesis_iff_subexponential_gridTentPattern_odd_floor :
    RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  constructor
  · intro hRH σ _
    have hnonneg := riemannHypothesis_iff_eventually_gridTentPattern_nonneg.mp hRH
    refine ⟨0, fun r hr F _ _ _ _ => ?_⟩
    set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    filter_upwards [hnonneg G r hr.le] with n hn
    rw [zero_mul, zero_mul, neg_zero]
    exact hn
  · intro hsub
    refine riemannHypothesis_of_subexponential_odd_floor fun σ hσ => ?_
    obtain ⟨C, hC⟩ := hsub σ hσ
    refine ⟨C, fun r hr F hF hFc hodd hsupp => ?_⟩
    set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
    obtain ⟨Mg, hMg⟩ := hF.continuous.bounded_above_of_compact_support hFc
    obtain ⟨Kg, hKg⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
    set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    have hGc : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
    obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport hFc.mul_left (by norm_num)
    have hlim := tendsto_compactFullWeilEnergy_gridTentPattern Fc hr.le hsupp
      (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
      (fun x y => by have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
      (fun x y => by have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
    rw [← fullZeroForm_eq_compactFullWeilEnergy Fc] at hlim
    exact ge_of_tendsto hlim (hC r hr F hF hFc hodd hsupp)

/-- **Constant-Floor Grid-Tent Receiver Bootstrap (`σ = 0`).**
`RiemannHypothesis` holds if and only if there exists `C : ℝ` such that for every aperture `r > 0`
and every odd `F ∈ C_c²` supported in `[-r, r]`, the single-scale grid tent pattern eventually
satisfies `compactFullWeilEnergy ≥ -C ∫ F²`. -/
theorem riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  constructor
  · intro hRH
    have hnonneg := riemannHypothesis_iff_eventually_gridTentPattern_nonneg.mp hRH
    refine ⟨0, fun r hr F _ _ _ _ => ?_⟩
    set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
    filter_upwards [hnonneg G r hr.le] with n hn
    rw [zero_mul, neg_zero]
    exact hn
  · rintro ⟨C, hC⟩
    rw [riemannHypothesis_iff_subexponential_gridTentPattern_odd_floor]
    intro σ hσ
    refine ⟨|C|, fun r hr F hF hFc hodd hsupp => ?_⟩
    filter_upwards [hC r hr F hF hFc hodd hsupp] with n hn
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hexp1 : 1 ≤ Real.exp (2 * σ * r) := Real.one_le_exp (by positivity)
    have hle : C * ∫ x, F x ^ 2 ≤ |C| * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
      calc C * ∫ x, F x ^ 2 ≤ |C| * 1 * ∫ x, F x ^ 2 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hI0
        _ ≤ |C| * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 (abs_nonneg C)) hI0
    linarith

/-! ## Section 4: The Reflected-Prime/Polar Receiver Ledger, Unconditional Floors, and the Width-to-Floor Bridge -/

/-- **All-Aperture Reflected-Prime/Polar Ledger for `compactFullWeilEnergy`.**
For every aperture `r > 0`, every plateau radius `R > r`, and every odd `F ∈ C_c²(ℝ, ℝ)` supported
in `[-r, r]`, `compactFullWeilEnergy` decomposes into the archimedean gauge budget minus
`reflectedPrimePolarCost F r`, and simultaneously equals the horizon-localized two-pole
Chebyshev-defect ledger on `(0, 2r]` and the second-order critical-scale prefix ledger on `(0, ∞)`. -/
theorem compactFullWeilEnergy_eq_reflectedPrimePolar_and_chebyshev_ledgers
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0) :
    let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
    let budget : ℝ := surplusPool (aperturePlateau r R) F +
      crossingPotentialTerm (aperturePlateau r R) F +
      gaugeRemainder (aperturePlateau r R) F
    compactFullWeilEnergy Fc = budget - reflectedPrimePolarCost F r ∧
    compactFullWeilEnergy Fc = budget -
      ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) ∧
    compactFullWeilEnergy Fc = budget -
      ∫ s in Ioi (0 : ℝ), (criticalScalePrefix s + s ^ 2 / 2 - s) *
        (2 * Real.exp (-s / 2) *
          (autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4)) := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  let f := mkOddRealTestsAt F hF hFc hodd hsupp
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  have hdef : (scalingSubsurface (oddRealTestsAt r)).defect (0, 0, f) (0, 0, f) =
      compactFullWeilEnergy Fc := by
    rw [scalingSubsurface_defect_self,
      show (f.1 : ℝ → ℝ) = F from rfl,
      weilPair_self_eq_fullZeroForm hF hFc, hF_eq]
  have h1 := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hrR (0, 0, f)
  have h2 := scalingSubsurface_odd_defect_eq_chebyshevDefectLedger hr hrR (0, 0, f)
  have h3 := scalingSubsurface_odd_defect_eq_criticalScalePrefixLedger hr hrR (0, 0, f)
  rw [hdef] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Unconditional All-Aperture Rate-`1/2` Floor `-78 e^r ∫ F²` on `compactFullWeilEnergy` and
`gridTentPattern`.** -/
theorem compactFullWeilEnergy_and_gridTent_ge_neg_seventy_eight_mul_exp
    {r : ℝ} (hr : 0 < r) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0) :
    let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩;
    -(78 * Real.exp r * ∫ u, F u ^ 2) ≤ compactFullWeilEnergy Fc ∧
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ᶠ n : ℕ in atTop,
      -(78 * Real.exp r * ∫ u, F u ^ 2) - ε₀ ≤
        compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
          n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  let f := mkOddRealTestsAt F hF hFc hodd hsupp
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  have hdef := scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr (0, 0, f)
  rw [scalingSubsurface_defect_self, show (f.1 : ℝ → ℝ) = F from rfl,
    weilPair_self_eq_fullZeroForm hF hFc, hF_eq] at hdef
  refine ⟨hdef, fun ε₀ hε₀ => ?_⟩
  obtain ⟨Mg, hMg⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨Kg, hKg⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
  have hGc : ContDiff ℝ 2 G := by dsimp [G]; fun_prop
  obtain ⟨L, hL⟩ := hGc.lipschitzWith_of_hasCompactSupport hFc.mul_left (by norm_num)
  have hlim := tendsto_compactFullWeilEnergy_gridTentPattern Fc hr.le hsupp
    (fun x => by rw [← Real.norm_eq_abs]; exact hMg x)
    (fun x y => by have := hKg.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
    (fun x y => by have := hL.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this)
  have hlt : -(78 * Real.exp r * ∫ u, F u ^ 2) - ε₀ < compactFullWeilEnergy Fc := by linarith
  filter_upwards [hlim.eventually (eventually_gt_nhds hlt)] with n hn
  exact hn.le

/-- **Sharp PNT `-((8 + ε) e^r + C) ∫ F²` Floor on `compactFullWeilEnergy`.** -/
theorem exists_compactFullWeilEnergy_ge_neg_eight_add_eps_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
      ∀ (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F),
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(((8 + ε) * Real.exp r + C) * ∫ u, F u ^ 2) ≤
        compactFullWeilEnergy ⟨⟨F, hF.continuous⟩, hFc⟩ := by
  obtain ⟨C, hC0, hC⟩ := exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp hε
  refine ⟨C, hC0, fun r hr F hF hFc hodd hsupp => ?_⟩
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  let f := mkOddRealTestsAt F hF hFc hodd hsupp
  have hdef := hC r hr (0, 0, f)
  rwa [scalingSubsurface_defect_self, show (f.1 : ℝ → ℝ) = F from rfl,
    weilPair_self_eq_fullZeroForm hF hFc, hF_eq] at hdef

/-- **De la Vallée Poussin Sobolev Floor on `compactFullWeilEnergy`.** -/
theorem exists_compactFullWeilEnergy_ge_neg_deLaValleePoussin_sobolev :
    ∃ c > 0, ∃ K > 0, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
      ∀ (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F),
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(K * Real.exp r * Real.exp (-c * Real.sqrt r) *
          ((∫ u, F u ^ 2) + (1 / 2) * ∫ u, deriv F u ^ 2)) ≤
        compactFullWeilEnergy ⟨⟨F, hF.continuous⟩, hFc⟩ := by
  obtain ⟨c, hc, K, hK, halloc⟩ := exists_globalIncidenceAllocation_with_deLaValleePoussin_deficit
  refine ⟨c, hc, K, hK, fun r hr F hF hFc hodd hsupp => ?_⟩
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  let f := mkOddRealTestsAt F hF hFc hodd hsupp
  have hled := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr (by linarith : r < r + 1) (0, 0, f)
  have ha := halloc r (r + 1) F hr (by linarith) hF hFc hodd hsupp
  rw [scalingSubsurface_defect_self, show (f.1 : ℝ → ℝ) = F from rfl,
    weilPair_self_eq_fullZeroForm hF hFc, hF_eq] at hled
  unfold reflectedPrimePolarCost at hled
  linarith

/-- **Converse Width-to-Floor Bridge for `compactFullWeilEnergy` and `gridTentPattern`.**
For every `β > zetaZeroWidth`, there exists `C ≥ 0` such that for every aperture `A ≥ 0`, every
`F ∈ C_c²(ℝ, ℝ)` supported in `[-A, A]` with `|gaugeDerivative (autocorr F) t| ≤ D`, and every
arithmetic scale `n : ℕ`, `compactFullWeilEnergy` satisfies the rate-`2β` floor and `gridTentPattern`
inherits this floor up to the explicit finite-scale error `gridTentApproximationConstant * d_{n+1}`. -/
theorem exists_compactFullWeilEnergy_and_gridTent_ge_neg_of_zetaZeroWidth_lt
    {β : ℝ} (hβ : zetaZeroWidth < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : ℝ → ℝ,
      ∀ (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F),
      (∀ x : ℝ, A < |x| → F x = 0) → ∀ D : ℝ,
      (∀ t : ℝ, |ChebyshevGauge.gaugeDerivative (autocorr F) t| ≤ D) →
      let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩;
      -(C * (1 + A) * Real.exp (2 * β * A) * ((∫ x, F x ^ 2) + D)) ≤
        compactFullWeilEnergy Fc ∧
      ∀ {Mg Kg L : ℝ}, (∀ x, |F x| ≤ Mg) → (∀ x y, |F x - F y| ≤ Kg * |x - y|) →
        (∀ x y, |Real.exp (-(3 * x / 2)) * F x - Real.exp (-(3 * y / 2)) * F y| ≤ L * |x - y|) →
        ∀ n : ℕ,
          -(C * (1 + A) * Real.exp (2 * β * A) * ((∫ x, F x ^ 2) + D)) -
            gridTentApproximationConstant A Mg Kg L * sourceFactorialWidth (n + 1) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(A + 1)) ⌈2 * (A + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
  obtain ⟨C, hC0, hfloor⟩ := exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt hβ
  refine ⟨C, hC0, fun A hA F hF hFc hsupp D hD => ?_⟩
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  have h1 := hfloor A hA F hF hFc hsupp D hD
  rw [hF_eq] at h1
  refine ⟨h1, fun {Mg Kg L} hMg hKg hGL n => ?_⟩
  have happrox := (abs_le.mp (abs_compactFullWeilEnergy_gridTentPattern_sub_le Fc hA hsupp
    hMg hKg hGL n)).1
  linarith

/-! ## Section 5: Unconditional Small-Aperture Coercivity (`3/10` All-Profile, `181/500` Odd-Profile) and Finite-Scale Grid-Tent Transfer -/

/-- **Explicit Finite-Scale Grid-Tent and Smooth-Detector Positivity Transfer for Any `g ∈ C_c(ℝ, ℝ)`.**
If `compactFullWeilEnergy g ≥ 2 * μ > 0`, then at every arithmetic scale `n` satisfying
`gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤ μ`, the single-scale
grid tent pattern `P_n` and its smoothed detector `D_{n,q}` (`1/(q+1) ≤ μ/2`) achieve strict
positivity across all five form realizations. -/
theorem gridTentPattern_and_smoothDetector_pos_of_explicit_scale (g : C_c(ℝ, ℝ)) {R Mg Kg L μ : ℝ}
    (hR : 0 ≤ R) (hgR : ∀ x, R < |x| → g x = 0) (hMg : ∀ x, |g x| ≤ Mg)
    (hKg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hGL : ∀ x y, |Real.exp (-(3 * x / 2)) * g x - Real.exp (-(3 * y / 2)) * g y| ≤ L * |x - y|)
    (hge : 2 * μ ≤ compactFullWeilEnergy g)
    {n : ℕ} (hn : gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) ≤ μ) :
    let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
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
  set G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * g x
  set M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
  set P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
  have h1 := (abs_le.mp (abs_compactFullWeilEnergy_gridTentPattern_sub_le g hR hgR hMg hKg hGL n)).1
  have hP_ge : μ ≤ compactFullWeilEnergy P := by linarith
  have hP_zf : μ ≤ fullZeroForm P := by
    rw [fullZeroForm_eq_compactFullWeilEnergy P]
    exact hP_ge
  refine ⟨hP_ge, hP_zf, fun q hq => ?_⟩
  set D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
  obtain ⟨hD_diff, hD_cpt⟩ := smoothGridTentDetector_admissible G n (-(R + 1)) M q
  obtain ⟨hD_approx, hD_W, hD_refl⟩ := smoothGridTentDetector_fullWeil_approximation G n (-(R + 1)) M q
  have hD_weil_ge : μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
      (EF.weilTest D D)).re := by
    have h2 := (abs_le.mp hD_approx).1
    linarith
  have hD_zeta_ge : μ / 2 ≤ (zetaZeroConfig.W D D).re := by
    rw [hD_W]; exact hD_weil_ge
  have hD_gap : configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
      configurationSquareMass zetaZeroConfig D := by
    linarith [hD_refl, hD_zeta_ge]
  exact ⟨hD_diff, hD_cpt, hD_weil_ge, hD_zeta_ge, hD_gap⟩

/-- **Unconditional All-Profile Receiver Coercivity on `[-3/10, 3/10]` and Explicit Finite-Scale
Grid-Tent Transfer.**
Every `F ∈ C_c²(ℝ, ℝ)` supported in `[-3/10, 3/10]` satisfies
`(1 / 5000) * ∫ x, F x ^ 2 ≤ compactFullWeilEnergy F`, and at every scale `n` where
`gridTentApproximationConstant (3/10) Mg Kg L * d_{n+1} ≤ (1 / 10000) * ∫ F²`, `gridTentPattern`
and `smoothGridTentDetector` inherit this coercivity across all five form realizations. -/
theorem compactFullWeilEnergy_and_gridTent_ge_of_support_le_threeTenths
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, 3 / 10 < |x| → F x = 0) :
    let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
    let μ : ℝ := (1 / 10000) * ∫ x, F x ^ 2
    2 * μ ≤ compactFullWeilEnergy Fc ∧
    ∀ {Mg Kg L : ℝ}, (∀ x, |F x| ≤ Mg) → (∀ x y, |F x - F y| ≤ Kg * |x - y|) →
      (∀ x y, |Real.exp (-(3 * x / 2)) * F x - Real.exp (-(3 * y / 2)) * F y| ≤ L * |x - y|) →
      ∀ {n : ℕ}, gridTentApproximationConstant (3 / 10) Mg Kg L * sourceFactorialWidth (n + 1) ≤ μ →
        let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
        let M : ℕ := ⌈2 * (3 / 10 + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(3 / 10 + 1)) M
        μ ≤ compactFullWeilEnergy P ∧
        μ ≤ fullZeroForm P ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(3 / 10 + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re ∧
          μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
          configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
            configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  have h1 := fullZeroForm_ge_of_support_le_threeTenths hF hFc hsupp
  rw [hF_eq] at h1
  have hge : 2 * ((1 / 10000) * ∫ x, F x ^ 2) ≤ compactFullWeilEnergy Fc := by linarith
  refine ⟨hge, fun {Mg Kg L} hMg hKg hGL {n} hn => ?_⟩
  exact gridTentPattern_and_smoothDetector_pos_of_explicit_scale Fc (by norm_num) hsupp
    hMg hKg hGL hge hn

/-- **Unconditional Odd-Sector Receiver Coercivity Past the First Prime (`[-181/500, 181/500]`) and
Explicit Finite-Scale Grid-Tent Transfer.**
Because `(1 / 2) * Real.log 2 < 181 / 500`, the prime `2` actively enters the correlation support on
`[-181/500, 181/500]`. Every odd `F ∈ C_c²(ℝ, ℝ)` supported in `[-181/500, 181/500]` satisfies
`(1 / 1000) * ∫ x, F x ^ 2 ≤ compactFullWeilEnergy F`, and at every scale `n` where
`gridTentApproximationConstant (181/500) Mg Kg L * d_{n+1} ≤ (1 / 2000) * ∫ F²`, `gridTentPattern`
and `smoothGridTentDetector` inherit this coercivity across all five form realizations. -/
theorem compactFullWeilEnergy_and_gridTent_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    let Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
    let μ : ℝ := (1 / 2000) * ∫ x, F x ^ 2
    Real.log 2 / 2 < 181 / 500 ∧
    2 * μ ≤ compactFullWeilEnergy Fc ∧
    ∀ {Mg Kg L : ℝ}, (∀ x, |F x| ≤ Mg) → (∀ x y, |F x - F y| ≤ Kg * |x - y|) →
      (∀ x y, |Real.exp (-(3 * x / 2)) * F x - Real.exp (-(3 * y / 2)) * F y| ≤ L * |x - y|) →
      ∀ {n : ℕ}, gridTentApproximationConstant (181 / 500) Mg Kg L * sourceFactorialWidth (n + 1) ≤ μ →
        let G : ℝ → ℝ := fun x => Real.exp (-(3 * x / 2)) * F x
        let M : ℕ := ⌈2 * (181 / 500 + 1) / sourceFactorialWidth (n + 1)⌉₊
        let P : C_c(ℝ, ℝ) := gridTentPattern G n (-(181 / 500 + 1)) M
        μ ≤ compactFullWeilEnergy P ∧
        μ ≤ fullZeroForm P ∧
        ∀ q : ℕ, 1 / ((q : ℝ) + 1) ≤ μ / 2 →
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(181 / 500 + 1)) M q
          ContDiff ℝ 2 D ∧
          HasCompactSupport D ∧
          μ / 2 ≤ (weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
            (EF.weilTest D D)).re ∧
          μ / 2 ≤ (zetaZeroConfig.W D D).re ∧
          configurationReflectionDefect zetaZeroConfig D + μ / 2 ≤
            configurationSquareMass zetaZeroConfig D := by
  dsimp only
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hF_eq : fullZeroForm F = compactFullWeilEnergy Fc :=
    fullZeroForm_eq_compactFullWeilEnergy Fc
  have h1 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hF hFc hodd hsupp
  rw [hF_eq] at h1
  have hge : 2 * ((1 / 2000) * ∫ x, F x ^ 2) ≤ compactFullWeilEnergy Fc := by linarith
  refine ⟨half_log_two_lt_threeHundredSixtyTwoThousandths, hge,
    fun {Mg Kg L} hMg hKg hGL {n} hn => ?_⟩
  exact gridTentPattern_and_smoothDetector_pos_of_explicit_scale Fc (by norm_num) hsupp
    hMg hKg hGL hge hn

end GaloisForLFunctions.ArithmeticPositivityTheory
end
