import GaloisForLFunctions.«arithmetic-positivity-theory».QuantitativeGridTentDetection
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerNodeDeletionPrice

/-!
# Source Selection in the Full Weil Cone: Single-Index Exposure, One-Sided Selection, and Additional Sign Estimates

By `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`, the full Weil cone
`{lam : ℕ → ℝ | WeilPositiveFull lam}` is empty if the Riemann Hypothesis fails and equals the
singleton `{Λ}` (on the visible indices `n ≥ 2`) if RH holds. Consequently, full-cone membership
splits into two distinct problems (§7.9):

1. **Source selection (distinguishing single-index perturbations and identifying `lam = Λ` on
   `n ≥ 2`):** Which admissible sources expose enough data to distinguish every single-index
   perturbation `w + δ · 1_{n = m}` (`m ≥ 2`, `δ ≠ 0`), and how do the one-sided cones select `Λ`?
2. **Additional sign estimates for the identified source:** Identifying the coefficients `lam(n) = Λ(n)`
   for `n ≥ 2` is unconditional for `lam = Λ` and does not by itself prove `WeilPositiveFull lam`.
   Which additional estimates on `lam` (or on the receiver / critical-family / node-deletion cones)
   are necessary and sufficient to certify the sign of the full Weil functional for the identified
   source, or to certify a graded strip / finite-aperture zero-free region?

This module resolves both parts unconditionally:

1. **Exact Single-Index Coordinate Extraction by Narrow Pair Tests (`pairTest`, `realPairTest`, and
   `gridTentPattern`) (`re_weilFullFunctional_pairTest_eq`, `re_weilFullFunctional_sub_pairTest_eq`,
   `re_weilFullFunctional_singleIndexPerturbation_pairTest`,
   `exists_pairTest_strict_drop_of_singleIndexPerturbation`,
   `forall_two_le_eq_iff_forall_re_weilFullFunctional_pairTest_eq`,
   `realPairTest_weilFullFunctional_and_gridTent_approximation`):**
   - For every `m ≥ 2` and `σ : ℝ`, the narrow pair test `pairTest m σ(u) = h_m(u) + σ h_m(u - log m)`
     (with `h_m = narrowBump m` supported in `[-1/(4(m+1)), 1/(4(m+1))]`) has `ℓ`-vector supported
     exclusively at index `m`, where `logValue (pairTest m σ) m = 2 σ (∫ h_m²) / √m ≠ 0`.
   - Perturbing any weight `w : ℕ → ℝ` at a single index `m ≥ 2` by `δ` shifts
     `(weilFullFunctional w (EF.weilTest (pairTest k σ) (pairTest k σ))).re` by
     `-δ * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m)` at `k = m` (or `-δ * σ / Real.sqrt m`
     after normalizing by `massOf (Finsupp.single (pairTestFn m σ) 1) = 2 ∫ h_m²`) and by `0` at every
     `k ≠ m`.
   - For every `δ ≠ 0`, choosing `σ = if 0 < δ then 1 else -1` strictly decreases the Weil functional
     on `pairTest m σ` by `|δ| * (2 * (∫ h_m²) / √m) > 0`.
   - Two weights `w₁, w₂ : ℕ → ℝ` agree on all `n ≥ 2` if and only if their full Weil functionals
     agree on `pairTest m 1` for all `m ≥ 2`, with explicit inversion formula recovering `w(m)`.
   - The real-valued pair seed `realPairTest m σ` vanishes outside `[-(log m + 1), log m + 1]` and
     transfers to single-scale factorial grid tent patterns `gridTentPattern` within
     `gridTentApproximationConstant (Real.log m + 1) Mg Kg L * sourceFactorialWidth (n + 1)`.

2. **Truncated Riemann-Kernel Exposure and Unconditional Refutation of Every Single-Index
   Perturbation of `Λ` (`atomPairing_singleIndexDelta`,
   `atomPairing_singleIndexDelta_riemannKernelAutocorr_sign`,
   `exists_truncatedRiemannKernelReal_weilFullFunctional_singleIndexPerturbation_neg`,
   `weilPositiveFull_vonMangoldtSingleIndexPerturbation_iff`,
   `not_weilPositiveFull_vonMangoldtSingleIndexPerturbation_of_ne_zero`):**
   - For `singleIndexDelta m δ = δ · 1_{n = m}` (`m ≥ 2`), the exposing functional
     `ℓ(v) = atomPairing v riemannKernelAutocorr` evaluates to
     `(δ / √m) (riemannKernelAutocorr (log m) + riemannKernelAutocorr (-log m))`, which has the
     exact sign of `δ` because `riemannKernelAutocorr y > 0` everywhere.
   - For every `m ≥ 2` and every `δ > 0`, **unconditionally** (without RH!), there exists `L₀ : ℝ`
     such that for all `L ≥ L₀`, the truncated Riemann kernel `truncatedRiemannKernelReal L` satisfies
     `(weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ) (EF.weilTest (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))).re < 0`.
   - For every `m ≥ 2` and every `δ ≠ 0` (both `δ > 0` and `δ < 0`, whether `m` is a prime power or
     composite), `¬ WeilPositiveFull (vonMangoldtSingleIndexPerturbation m δ)` holds unconditionally,
     and `WeilPositiveFull (vonMangoldtSingleIndexPerturbation m δ) ↔ RiemannHypothesis ∧ δ = 0`.

3. **Unconditional One-Sided Cone Selection Without Summability Premises
   (`positiveOnNonposCone_iff_riemannHypothesis_and_vonMangoldt_le`,
   `positiveOnNonnegCone_iff_riemannHypothesis_and_le_vonMangoldt`,
   `weilPositiveFull_iff_positiveOnNonposCone_and_positiveOnNonnegCone`):**
   - Combining M. Riesz one-sided cone feasibility with unconditional full-cone uniqueness
     (`eq_vonMangoldt_of_weilPositiveFull`) removes the summability premises from the one-sided
     criteria: for *every* `U, L : ℕ → ℝ`,
     `PositiveOnNonposCone U ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → Λ(n) ≤ U(n)` and
     `PositiveOnNonnegCone L ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → L(n) ≤ Λ(n)`.
   - Full-cone membership is the exact intersection of the two one-sided cones:
     `WeilPositiveFull lam ↔ PositiveOnNonposCone lam ∧ PositiveOnNonnegCone lam`.

4. **Source Identification vs. Cone Membership, and the Additional Estimates Proving the Sign
   (`SourceIdentifiedWithVonMangoldt`, `sourceIdentifiedWithVonMangoldt_iff_forall_two_le_eq`,
   `weilPositiveFull_of_sourceIdentified_iff_additional_estimates`,
   `graded_and_finite_aperture_sign_of_sourceIdentified`):**
   - For a weight `lam : ℕ → ℝ` identified with `Λ` on the pair-test family `{pairTest m 1 : m ≥ 2}`,
     full-cone positivity `WeilPositiveFull lam` is unconditionally equivalent to each of:
     (i) one-sided positivity `PositiveOnNonposCone lam` (where the prime sum is already nonnegative),
     (ii) one-sided positivity `PositiveOnNonnegCone lam`,
     (iii) the prime-power node-deletion symbol slack bound
           `∀ m, IsPrimePow m → ZeroPoleBlindSymbolSlackOn (primePowerNodes \ {m}) (lam m / √m)`,
     (iv) a constant-in-aperture floor `-(C * ∫ F²)` on odd `gridTentPattern`s,
     (v) a subexponential-in-aperture floor `-(C_σ e^{2σ r} ∫ F²)` (`∀ σ > 0`) on odd `gridTentPattern`s,
     (vi) a subexponential-in-aperture floor on `fullZeroForm F` for all odd `F ∈ C_c²([-r, r])`, and
     (vii) `RiemannHypothesis`.
   - At a graded level, an `(α, β)`-norm-controlled subfamily transfer with rate-`2σ` floor for an
     identified source certifies `zetaZeroWidth ≤ σ + β`, and eventual nonnegativity on smoothed
     grid-tent detectors at a single fixed aperture `R ≥ e⁶` certifies `ZetaWindowPositive R` and
     excludes all zeros of depth `≥ 1/R` below `zetaClusterHorizonHeight A₀ R`.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real BigOperators ENNReal CompactlySupported ComplexConjugate ContDiff
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Single-Index Perturbations and Exact Coordinate Extraction by Narrow Pair Tests -/

/-- A single-index perturbation `δ · 1_{n = m}` supported at the arithmetic index `m : ℕ`. -/
def singleIndexDelta (m : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  if n = m then δ else 0

/-- Perturbation `w + δ · 1_{n = m}` of an arithmetic weight `w : ℕ → ℝ` at a single index `m`. -/
def singleIndexPerturbation (w : ℕ → ℝ) (m : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  w n + singleIndexDelta m δ n

/-- Single-index perturbation `Λ + δ · 1_{n = m}` of the von Mangoldt weight at index `m`. -/
def vonMangoldtSingleIndexPerturbation (m : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  singleIndexPerturbation (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) m δ n

@[simp]
theorem singleIndexDelta_self (m : ℕ) (δ : ℝ) :
    singleIndexDelta m δ m = δ := by
  simp [singleIndexDelta]

theorem singleIndexDelta_of_ne {m n : ℕ} (δ : ℝ) (h : n ≠ m) :
    singleIndexDelta m δ n = 0 := by
  simp [singleIndexDelta, h]

@[simp]
theorem singleIndexPerturbation_self (w : ℕ → ℝ) (m : ℕ) (δ : ℝ) :
    singleIndexPerturbation w m δ m = w m + δ := by
  simp [singleIndexPerturbation]

theorem singleIndexPerturbation_of_ne (w : ℕ → ℝ) {m n : ℕ} (δ : ℝ) (h : n ≠ m) :
    singleIndexPerturbation w m δ n = w n := by
  simp [singleIndexPerturbation, singleIndexDelta, h]

@[simp]
theorem singleIndexPerturbation_zero (w : ℕ → ℝ) (m : ℕ) :
    singleIndexPerturbation w m 0 = w := by
  funext n
  simp [singleIndexPerturbation, singleIndexDelta]

/-- **Exact Single-Index Evaluation of `weilFullFunctional` on a Narrow Pair Test `pairTest m σ`.**
For every weight `w : ℕ → ℝ`, every index `m ≥ 2`, and every `σ : ℝ`, the narrow pair test
`pairTest m σ` isolates the single coefficient `w m` with weight
`2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m`. -/
theorem re_weilFullFunctional_pairTest_eq (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (σ : ℝ) :
    (weilFullFunctional w (EF.weilTest (pairTest m σ) (pairTest m σ))).re =
      weilArchRe (EF.weilTest (pairTest m σ) (pairTest m σ)) -
        w m * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) := by
  have h := re_weilFullFunctional_eq w (pairTestFn m σ)
  change (weilFullFunctional w (EF.weilTest (pairTest m σ) (pairTest m σ))).re =
    weilArchRe (EF.weilTest (pairTest m σ) (pairTest m σ)) -
      linearCombination ℝ (fun j : LogIndex => w j) (logVector (pairTestFn (⟨m, hm⟩ : LogIndex) σ)) at h
  rw [logVector_pairTestFn ⟨m, hm⟩ σ, linearCombination_single, smul_eq_mul] at h
  linarith

/-- **Exact Coordinate Difference Formula on `pairTest m σ`.**
For any two arithmetic weights `w₁, w₂ : ℕ → ℝ` and any `m ≥ 2`, the difference of their full Weil
functionals on `pairTest m σ` depends only on `w₁ m - w₂ m`. -/
theorem re_weilFullFunctional_sub_pairTest_eq (w₁ w₂ : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (σ : ℝ) :
    (weilFullFunctional w₁ (EF.weilTest (pairTest m σ) (pairTest m σ))).re -
      (weilFullFunctional w₂ (EF.weilTest (pairTest m σ) (pairTest m σ))).re =
      -(w₁ m - w₂ m) * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) := by
  rw [re_weilFullFunctional_pairTest_eq w₁ hm σ, re_weilFullFunctional_pairTest_eq w₂ hm σ]
  ring

/-- **Exact Kronecker-Delta Response of `singleIndexPerturbation` on Narrow Pair Tests.**
For `m ≥ 2` and `k ≥ 2`, perturbing `w` by `δ` at index `m` shifts `weilFullFunctional` on
`pairTest k σ` by `-δ * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m)` when `k = m`, and by
`0` when `k ≠ m`. When `σ ^ 2 = 1`, normalizing by the pair-test mass `2 ∫ (narrowBump m t)^2`
yields `-δ * σ / Real.sqrt m` at `k = m`. -/
theorem re_weilFullFunctional_singleIndexPerturbation_pairTest (w : ℕ → ℝ) {m k : ℕ}
    (hm : 2 ≤ m) (hk : 2 ≤ k) (δ σ : ℝ) :
    (weilFullFunctional (singleIndexPerturbation w m δ)
        (EF.weilTest (pairTest k σ) (pairTest k σ))).re -
      (weilFullFunctional w (EF.weilTest (pairTest k σ) (pairTest k σ))).re =
      (if k = m then -δ * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) else 0) ∧
    (σ ^ 2 = 1 →
      ((weilFullFunctional (singleIndexPerturbation w m δ)
          (EF.weilTest (pairTest m σ) (pairTest m σ))).re -
        (weilFullFunctional w (EF.weilTest (pairTest m σ) (pairTest m σ))).re) /
        massOf (Finsupp.single (pairTestFn m σ) 1) =
      -(δ * σ / Real.sqrt m)) := by
  constructor
  · rw [re_weilFullFunctional_sub_pairTest_eq (singleIndexPerturbation w m δ) w hk σ]
    by_cases hkm : k = m
    · subst hkm
      rw [if_pos rfl, singleIndexPerturbation_self]
      ring
    · rw [if_neg hkm, singleIndexPerturbation_of_ne w δ hkm, sub_self, neg_zero, zero_mul]
  · intro hσ
    rw [re_weilFullFunctional_sub_pairTest_eq (singleIndexPerturbation w m δ) w hm σ,
      singleIndexPerturbation_self, massOf_single_pairTestFn hm hσ]
    have hI : ∫ t, (narrowBump m t) ^ 2 ≠ 0 := (integral_narrowBump_sq_pos m).ne'
    have h2I : 2 * ∫ t, (narrowBump m t) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero hI
    calc -(w m + δ - w m) * (2 * σ * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) /
          (2 * ∫ t, (narrowBump m t) ^ 2)
        = (-(δ * σ / Real.sqrt m)) * (2 * ∫ t, (narrowBump m t) ^ 2) /
          (2 * ∫ t, (narrowBump m t) ^ 2) := by ring
      _ = -(δ * σ / Real.sqrt m) := mul_div_cancel_right₀ _ h2I

/-- **Two-Sign Strict Lowering of the Weil Functional by Narrow Pair Tests.**
For every weight `w : ℕ → ℝ`, every index `m ≥ 2`, and every nonzero single-index perturbation
`δ ≠ 0`, one of the two narrow pair tests `pairTest m 1` or `pairTest m (-1)` strictly lowers the
real Weil functional by `|δ| * (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) > 0`. -/
theorem exists_pairTest_strict_drop_of_singleIndexPerturbation (w : ℕ → ℝ) {m : ℕ}
    (hm : 2 ≤ m) {δ : ℝ} (hδ : δ ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (weilFullFunctional (singleIndexPerturbation w m δ)
          (EF.weilTest (pairTest m σ) (pairTest m σ))).re -
        (weilFullFunctional w (EF.weilTest (pairTest m σ) (pairTest m σ))).re =
        -|δ| * (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) ∧
      (weilFullFunctional (singleIndexPerturbation w m δ)
          (EF.weilTest (pairTest m σ) (pairTest m σ))).re <
        (weilFullFunctional w (EF.weilTest (pairTest m σ) (pairTest m σ))).re := by
  have hw_pos : 0 < 2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m := pairTest_weight_pos ⟨m, hm⟩
  have habs_pos : 0 < |δ| * (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) :=
    mul_pos (abs_pos.mpr hδ) hw_pos
  rcases lt_trichotomy δ 0 with hneg | rfl | hpos
  · have h := (re_weilFullFunctional_singleIndexPerturbation_pairTest w hm hm δ (-1)).1
    rw [if_pos rfl] at h
    have hval :
        (weilFullFunctional (singleIndexPerturbation w m δ)
            (EF.weilTest (pairTest m (-1)) (pairTest m (-1)))).re -
          (weilFullFunctional w (EF.weilTest (pairTest m (-1)) (pairTest m (-1)))).re =
        -|δ| * (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) := by
      rw [h, abs_of_neg hneg]
      ring
    exact ⟨-1, Or.inr rfl, hval, by linarith⟩
  · exact (hδ rfl).elim
  · have h := (re_weilFullFunctional_singleIndexPerturbation_pairTest w hm hm δ 1).1
    rw [if_pos rfl] at h
    have hval :
        (weilFullFunctional (singleIndexPerturbation w m δ)
            (EF.weilTest (pairTest m 1) (pairTest m 1))).re -
          (weilFullFunctional w (EF.weilTest (pairTest m 1) (pairTest m 1))).re =
        -|δ| * (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m) := by
      rw [h, abs_of_pos hpos]
      ring
    exact ⟨1, Or.inl rfl, hval, by linarith⟩

/-- **Complete Coordinate Identification by `pairTest m 1` (`m ≥ 2`) and Explicit Inversion.**
Two arithmetic weights `w₁, w₂ : ℕ → ℝ` agree on all visible indices `n ≥ 2` if and only if their
full Weil functionals agree on `pairTest m 1` for every `m ≥ 2`. Moreover, each coefficient `w₁ m`
(`m ≥ 2`) is explicitly recovered from `weilArchRe` and `weilFullFunctional w₁` on `pairTest m 1`. -/
theorem forall_two_le_eq_iff_forall_re_weilFullFunctional_pairTest_eq (w₁ w₂ : ℕ → ℝ) :
    ((∀ n : ℕ, 2 ≤ n → w₁ n = w₂ n) ↔
      ∀ m : ℕ, 2 ≤ m →
        (weilFullFunctional w₁ (EF.weilTest (pairTest m 1) (pairTest m 1))).re =
          (weilFullFunctional w₂ (EF.weilTest (pairTest m 1) (pairTest m 1))).re) ∧
    (∀ m : ℕ, 2 ≤ m →
      w₁ m =
        (weilArchRe (EF.weilTest (pairTest m 1) (pairTest m 1)) -
          (weilFullFunctional w₁ (EF.weilTest (pairTest m 1) (pairTest m 1))).re) /
          (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m)) := by
  refine ⟨⟨fun h m hm => by rw [weilFullFunctional_congr h], fun h n hn => ?_⟩, fun m hm => ?_⟩
  · have hdiff := re_weilFullFunctional_sub_pairTest_eq w₁ w₂ hn 1
    rw [h n hn, sub_self, mul_one] at hdiff
    have hw_pos : 0 < 2 * (∫ t, (narrowBump n t) ^ 2) / Real.sqrt n := pairTest_weight_pos ⟨n, hn⟩
    have h0 : -(w₁ n - w₂ n) = 0 :=
      (mul_eq_zero.mp hdiff.symm).resolve_right hw_pos.ne'
    linarith
  · have hval := re_weilFullFunctional_pairTest_eq w₁ hm 1
    rw [mul_one] at hval
    have hw_pos : 0 < 2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m := pairTest_weight_pos ⟨m, hm⟩
    rw [eq_div_iff hw_pos.ne']
    linarith

/-- The real-valued narrow pair test `h_m(u) + σ h_m(u - log m)`, whose complexification is
`pairTest m σ`. -/
def realPairTest (m : ℕ) (σ : ℝ) (u : ℝ) : ℝ :=
  narrowBump m u + σ * narrowBump m (u - Real.log m)

theorem ofReal_realPairTest (m : ℕ) (σ : ℝ) :
    (fun u : ℝ => (realPairTest m σ u : ℂ)) = pairTest m σ := by
  funext u
  simp [realPairTest, pairTest, narrowBumpC]

theorem contDiff_realPairTest (m : ℕ) (σ : ℝ) :
    ContDiff ℝ 2 (realPairTest m σ) := by
  unfold realPairTest
  exact ((narrowBump m).contDiff.of_le (by norm_cast)).add
    (contDiff_const.mul (((narrowBump m).contDiff.of_le (by norm_cast)).comp
      (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_realPairTest (m : ℕ) (σ : ℝ) :
    HasCompactSupport (realPairTest m σ) := by
  unfold realPairTest
  exact (narrowBump m).hasCompactSupport.add
    (((narrowBump m).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (Real.log m))).mul_left)

theorem realPairTest_eq_zero_of_abs_gt {m : ℕ} (hm : 2 ≤ m) (σ : ℝ) {u : ℝ}
    (hu : Real.log m + 1 < |u|) :
    realPairTest m σ u = 0 := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hrOut : 1 / (4 * ((m : ℝ) + 1)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hu1 : 1 / (4 * ((m : ℝ) + 1)) < |u| := by linarith
  have hu2 : 1 / (4 * ((m : ℝ) + 1)) < |u - Real.log m| := by
    have htri : |u| - |Real.log m| ≤ |u - Real.log m| := abs_sub_abs_le_abs_sub u (Real.log m)
    rw [abs_of_nonneg hlog] at htri
    linarith
  have h1 := narrowBumpC_eq_zero m hu1
  have h2 := narrowBumpC_eq_zero m hu2
  simp only [narrowBumpC, Complex.ofReal_eq_zero] at h1 h2
  simp [realPairTest, h1, h2]

/-- **Real Pair-Test Bridge to `compactFullWeilEnergy` and Finite-Scale `gridTentPattern`.**
For every `m ≥ 2` and `σ : ℝ`, `realPairTest m σ` is `C_c²` and supported in
`[-(Real.log m + 1), Real.log m + 1]`, its `compactFullWeilEnergy` equals
`(weilFullFunctional Λ (EF.weilTest (pairTest m σ) (pairTest m σ))).re`, and single-scale factorial
grid tent patterns approximate it at every scale `n : ℕ` within
`gridTentApproximationConstant (Real.log m + 1) Mg Kg L * sourceFactorialWidth (n + 1)`. -/
theorem realPairTest_weilFullFunctional_and_gridTent_approximation {m : ℕ} (hm : 2 ≤ m) (σ : ℝ) :
    let F : ℝ → ℝ := realPairTest m σ
    let Fc : C_c(ℝ, ℝ) := ⟨⟨F, (contDiff_realPairTest m σ).continuous⟩,
      hasCompactSupport_realPairTest m σ⟩
    let R : ℝ := Real.log m + 1
    (∀ u, R < |u| → F u = 0) ∧
    compactFullWeilEnergy Fc =
      (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (EF.weilTest (pairTest m σ) (pairTest m σ))).re ∧
    ∀ {Mg Kg L : ℝ}, (∀ x, |F x| ≤ Mg) → (∀ x y, |F x - F y| ≤ Kg * |x - y|) →
      (∀ x y, |Real.exp (-(3 * x / 2)) * F x - Real.exp (-(3 * y / 2)) * F y| ≤ L * |x - y|) →
      ∀ n : ℕ,
        |compactFullWeilEnergy
            (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) -
          (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
            (EF.weilTest (pairTest m σ) (pairTest m σ))).re| ≤
          gridTentApproximationConstant R Mg Kg L * sourceFactorialWidth (n + 1) := by
  dsimp only
  set F : ℝ → ℝ := realPairTest m σ
  set Fc : C_c(ℝ, ℝ) := ⟨⟨F, (contDiff_realPairTest m σ).continuous⟩,
    hasCompactSupport_realPairTest m σ⟩
  set R : ℝ := Real.log m + 1
  have hR0 : 0 ≤ R := by
    have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    linarith
  have hsupp : ∀ u, R < |u| → F u = 0 := fun u hu => realPairTest_eq_zero_of_abs_gt hm σ hu
  have hF_complex : ContDiff ℝ 2 (fun u => (F u : ℂ)) := by
    rw [ofReal_realPairTest]; exact contDiff_pairTest m σ
  have hFc_complex : HasCompactSupport (fun u => (F u : ℂ)) := by
    rw [ofReal_realPairTest]; exact hasCompactSupport_pairTest m σ
  have hW_eq : compactFullWeilEnergy Fc =
      (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (EF.weilTest (pairTest m σ) (pairTest m σ))).re := by
    rw [← fullZeroForm_eq_compactFullWeilEnergy Fc]
    change fullZeroForm F = _
    rw [fullZeroForm_eq_zeta_W_re (contDiff_realPairTest m σ) (hasCompactSupport_realPairTest m σ),
      ofReal_realPairTest,
      zeta_W_eq_weilFullFunctional (contDiff_pairTest m σ) (hasCompactSupport_pairTest m σ)]
  refine ⟨hsupp, hW_eq, fun {Mg Kg L} hMg hKg hGL n => ?_⟩
  rw [← hW_eq]
  exact abs_compactFullWeilEnergy_gridTentPattern_sub_le Fc hR0 hsupp hMg hKg hGL n

/-! ## Section 2: Truncated Riemann-Kernel Exposure and Unconditional Refutation of Single-Index Perturbations -/

/-- The single-index perturbation `singleIndexDelta m δ` is inverse-square summable. -/
theorem summable_singleIndexDelta_div_sq (m : ℕ) (δ : ℝ) :
    Summable fun n : ℕ => |singleIndexDelta m δ n| / (n : ℝ) ^ 2 := by
  refine summable_of_ne_finset_zero (s := {m}) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  simp [singleIndexDelta, hn]

/-- **Single-Index Evaluation of `atomPairing`.**
For `m ≥ 2`, `atomPairing (singleIndexDelta m δ) g = (δ / √m) (g(log m) + g(-log m))`. -/
theorem atomPairing_singleIndexDelta {m : ℕ} (hm : 2 ≤ m) (δ : ℝ) (g : ℝ → ℝ) :
    atomPairing (singleIndexDelta m δ) g =
      (δ / Real.sqrt m) * (g (Real.log m) + g (-Real.log m)) := by
  unfold atomPairing
  rw [tsum_eq_single m]
  · simp [singleIndexDelta, hm]
  · intro n hnm
    simp [singleIndexDelta, hnm]

/-- **Strict Positivity of the Exposing Kernel Weight at Every Index `m ≥ 2`.**
Because `riemannKernelAutocorr` is strictly positive everywhere, the single-index exposing weight
`(riemannKernelAutocorr (log m) + riemannKernelAutocorr (-log m)) / √m` is strictly positive for
every `m ≥ 2`, so `atomPairing (singleIndexDelta m δ) riemannKernelAutocorr` has the exact sign of
`δ`. -/
theorem atomPairing_singleIndexDelta_riemannKernelAutocorr_sign {m : ℕ} (hm : 2 ≤ m) (δ : ℝ) :
    0 < (riemannKernelAutocorr (Real.log m) + riemannKernelAutocorr (-Real.log m)) / Real.sqrt m ∧
    (0 < atomPairing (singleIndexDelta m δ) riemannKernelAutocorr ↔ 0 < δ) ∧
    (atomPairing (singleIndexDelta m δ) riemannKernelAutocorr = 0 ↔ δ = 0) ∧
    (atomPairing (singleIndexDelta m δ) riemannKernelAutocorr < 0 ↔ δ < 0) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hK_pos : 0 < riemannKernelAutocorr (Real.log m) + riemannKernelAutocorr (-Real.log m) :=
    add_pos (riemannKernelAutocorr_pos (Real.log m)) (riemannKernelAutocorr_pos (-Real.log m))
  have hw_pos :
      0 < (riemannKernelAutocorr (Real.log m) + riemannKernelAutocorr (-Real.log m)) / Real.sqrt m :=
    div_pos hK_pos hsqrt_pos
  have heq : atomPairing (singleIndexDelta m δ) riemannKernelAutocorr =
      δ * ((riemannKernelAutocorr (Real.log m) + riemannKernelAutocorr (-Real.log m)) / Real.sqrt m) := by
    rw [atomPairing_singleIndexDelta hm δ riemannKernelAutocorr]
    ring
  refine ⟨hw_pos, ?_, ?_, ?_⟩
  · rw [heq, mul_pos_iff_of_pos_right hw_pos]
  · rw [heq, mul_eq_zero, or_iff_left hw_pos.ne']
  · rw [heq]
    exact ⟨fun h => by nlinarith, fun h => mul_neg_of_neg_of_pos h hw_pos⟩

/-- **Unconditional Refutation of Positive Single-Index Perturbations `Λ + δ · 1_{n = m}` (`δ > 0`)
by Truncated Riemann Kernels.**
For every index `m ≥ 2` and every `δ > 0`, **without assuming RH**, there exists `L₀ : ℝ` such that
for all truncation radii `L ≥ L₀`, the truncated Riemann kernel `truncatedRiemannKernelReal L` gives
a strictly negative full Weil functional for `vonMangoldtSingleIndexPerturbation m δ`. -/
theorem exists_truncatedRiemannKernelReal_weilFullFunctional_singleIndexPerturbation_neg
    {m : ℕ} (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ)
        (EF.weilTest (fun u => (truncatedRiemannKernelReal L u : ℂ))
          (fun u => (truncatedRiemannKernelReal L u : ℂ)))).re ≤
        -(atomPairing (singleIndexDelta m δ) riemannKernelAutocorr / 3) ∧
      (weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ)
        (EF.weilTest (fun u => (truncatedRiemannKernelReal L u : ℂ))
          (fun u => (truncatedRiemannKernelReal L u : ℂ)))).re < 0 := by
  set w := singleIndexDelta m δ
  have hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2 := summable_singleIndexDelta_div_sq m δ
  set ℓ := atomPairing w riemannKernelAutocorr
  have hℓ_pos : 0 < ℓ :=
    (atomPairing_singleIndexDelta_riemannKernelAutocorr_sign hm δ).2.1.mpr hδ
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_abs_atomPairing_truncatedAutocorr_sub_le hw2
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ℓ / 3) (by linarith)
  obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK₀0 (δ := ℓ / 3) (by linarith)
  refine ⟨max L₁ L₂, fun L hL => ?_⟩
  have h1 := hL₁ L ((le_max_left L₁ L₂).trans hL)
  have h2 := hL₂ L ((le_max_right L₁ L₂).trans hL)
  have h3 := (abs_le.mp (hK₀ L)).1
  have hW_bound : (zetaZeroConfig.W (fun u => (truncatedRiemannKernelReal L u : ℂ))
      (fun u => (truncatedRiemannKernelReal L u : ℂ))).re ≤
      (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 := by
    have h : (fun u => (truncatedRiemannKernelReal L u : ℂ)) = truncatedRiemannKernel L :=
      funext fun u => (truncatedRiemannKernel_eq L u).symm
    rw [h]
    obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    exact (Complex.re_le_norm _).trans (norm_W_le_of_zero_bound
      (truncatedRiemannTailEnergy_nonneg L) (truncatedRiemannKernel_zero_bound L hΛ'))
  have hre := re_weilFullFunctional_add_eq w
    (contDiff_ofReal_truncatedRiemannKernelReal L) (hasCompactSupport_truncatedRiemannKernelReal L)
  change (weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ)
    (EF.weilTest (fun u => (truncatedRiemannKernelReal L u : ℂ))
      (fun u => (truncatedRiemannKernelReal L u : ℂ)))).re = _ at hre
  have hle : (weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ)
      (EF.weilTest (fun u => (truncatedRiemannKernelReal L u : ℂ))
        (fun u => (truncatedRiemannKernelReal L u : ℂ)))).re ≤ -(ℓ / 3) := by
    linarith
  exact ⟨hle, by linarith⟩

/-- **Exact Full-Cone Classification of Single-Index Perturbations of `Λ`.**
For every index `m ≥ 2` and every `δ : ℝ`, `vonMangoldtSingleIndexPerturbation m δ` lies in the full
Weil cone if and only if the Riemann Hypothesis holds and `δ = 0`. -/
theorem weilPositiveFull_vonMangoldtSingleIndexPerturbation_iff {m : ℕ} (hm : 2 ≤ m) (δ : ℝ) :
    WeilPositiveFull (vonMangoldtSingleIndexPerturbation m δ) ↔
      RiemannHypothesis ∧ δ = 0 := by
  rw [weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt]
  constructor
  · rintro ⟨hRH, heq⟩
    have hm_eq := heq m hm
    simp only [vonMangoldtSingleIndexPerturbation, singleIndexPerturbation_self] at hm_eq
    exact ⟨hRH, by linarith⟩
  · rintro ⟨hRH, rfl⟩
    refine ⟨hRH, fun n _ => ?_⟩
    simp [vonMangoldtSingleIndexPerturbation]

/-- **Unconditional Exclusion of Every Nonzero Single-Index Perturbation `Λ + δ · 1_{n = m}`.**
For every index `m ≥ 2` (prime power or composite) and every `δ ≠ 0` (of either sign),
`vonMangoldtSingleIndexPerturbation m δ` is unconditionally outside the full Weil cone: there exists
a compactly supported `C²` test `f : ℝ → ℂ` with
`(weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ) (EF.weilTest f f)).re < 0`. -/
theorem not_weilPositiveFull_vonMangoldtSingleIndexPerturbation_of_ne_zero
    {m : ℕ} (hm : 2 ≤ m) {δ : ℝ} (hδ : δ ≠ 0) :
    ¬ WeilPositiveFull (vonMangoldtSingleIndexPerturbation m δ) ∧
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      (weilFullFunctional (vonMangoldtSingleIndexPerturbation m δ) (EF.weilTest f f)).re < 0 := by
  have hnot : ¬ WeilPositiveFull (vonMangoldtSingleIndexPerturbation m δ) := by
    rw [weilPositiveFull_vonMangoldtSingleIndexPerturbation_iff hm]
    exact fun h => hδ h.2
  refine ⟨hnot, ?_⟩
  unfold WeilPositiveFull at hnot
  push Not at hnot
  exact hnot

/-! ## Section 3: Unconditional One-Sided Cone Selection Without Summability Premises -/

/-- **Unconditional One-Sided Selection on the Nonpositive Cone (`PositiveOnNonposCone`).**
For *every* arithmetic weight `U : ℕ → ℝ` (with no summability or growth hypothesis on `U`), `U` is
Weil-positive on the nonpositive cone if and only if the Riemann Hypothesis holds and `Λ(n) ≤ U(n)`
for every `n ≥ 2`. -/
theorem positiveOnNonposCone_iff_riemannHypothesis_and_vonMangoldt_le (U : ℕ → ℝ) :
    PositiveOnNonposCone U ↔
      RiemannHypothesis ∧ ∀ n : ℕ, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ U n := by
  constructor
  · intro h
    obtain ⟨lam, hW, hle, -⟩ := exists_weilPositiveFull_le_of_positiveOnNonposCone h
    obtain ⟨hRH, heq⟩ := weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW
    exact ⟨hRH, fun n hn => (heq n hn).symm ▸ hle n hn⟩
  · rintro ⟨hRH, hle⟩ c hc hneg
    have hΛ := (riemannHypothesis_iff_positiveOnNonposCone.mp hRH) c hc hneg
    rw [sum_re_weilFullFunctional] at hΛ ⊢
    have hmono :
        linearCombination ℝ (fun j : LogIndex => U j) (linearCombination ℝ logVector c) ≤
          linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
            (linearCombination ℝ logVector c) := by
      rw [linearCombination_apply, linearCombination_apply]
      refine Finset.sum_le_sum fun j _ => ?_
      simp only [smul_eq_mul]
      have hj_neg : linearCombination ℝ logVector c j ≤ 0 := by
        rw [linearCombination_logVector_apply]
        exact hneg j j.2
      exact mul_le_mul_of_nonpos_left (hle j j.2) hj_neg
    linarith

/-- **Unconditional One-Sided Selection on the Nonnegative Cone (`PositiveOnNonnegCone`).**
For *every* arithmetic weight `L : ℕ → ℝ` (with no summability or growth hypothesis on `L`), `L` is
Weil-positive on the nonnegative cone if and only if the Riemann Hypothesis holds and `L(n) ≤ Λ(n)`
for every `n ≥ 2`. -/
theorem positiveOnNonnegCone_iff_riemannHypothesis_and_le_vonMangoldt (L : ℕ → ℝ) :
    PositiveOnNonnegCone L ↔
      RiemannHypothesis ∧ ∀ n : ℕ, 2 ≤ n → L n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro h
    obtain ⟨lam, hW, hge, -⟩ := exists_weilPositiveFull_ge_of_positiveOnNonnegCone h
    obtain ⟨hRH, heq⟩ := weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW
    exact ⟨hRH, fun n hn => (heq n hn) ▸ hge n hn⟩
  · rintro ⟨hRH, hle⟩ c hc hpos
    have hΛ := (riemannHypothesis_iff_positiveOnNonnegCone.mp hRH) c hc hpos
    rw [sum_re_weilFullFunctional] at hΛ ⊢
    have hmono :
        linearCombination ℝ (fun j : LogIndex => L j) (linearCombination ℝ logVector c) ≤
          linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
            (linearCombination ℝ logVector c) := by
      rw [linearCombination_apply, linearCombination_apply]
      refine Finset.sum_le_sum fun j _ => ?_
      simp only [smul_eq_mul]
      have hj_pos : 0 ≤ linearCombination ℝ logVector c j := by
        rw [linearCombination_logVector_apply]
        exact hpos j j.2
      exact mul_le_mul_of_nonneg_left (hle j j.2) hj_pos
    linarith

/-- **Full-Cone Positivity as the Intersection of the Two One-Sided Cones.**
For any `lam : ℕ → ℝ`, `WeilPositiveFull lam` holds if and only if both `PositiveOnNonposCone lam`
and `PositiveOnNonnegCone lam` hold. -/
theorem weilPositiveFull_iff_positiveOnNonposCone_and_positiveOnNonnegCone (lam : ℕ → ℝ) :
    WeilPositiveFull lam ↔ PositiveOnNonposCone lam ∧ PositiveOnNonnegCone lam := by
  rw [weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt,
    positiveOnNonposCone_iff_riemannHypothesis_and_vonMangoldt_le,
    positiveOnNonnegCone_iff_riemannHypothesis_and_le_vonMangoldt]
  constructor
  · rintro ⟨hRH, heq⟩
    exact ⟨⟨hRH, fun n hn => (heq n hn).ge⟩, ⟨hRH, fun n hn => (heq n hn).le⟩⟩
  · rintro ⟨⟨hRH, hge⟩, ⟨_, hle⟩⟩
    exact ⟨hRH, fun n hn => le_antisymm (hle n hn) (hge n hn)⟩

/-! ## Section 4: Source Identification vs. Cone Membership, and the Additional Estimates Proving the Sign -/

/-- A weight `lam : ℕ → ℝ` is **source-identified with `Λ` on the narrow pair-test family** if its
full Weil functional agrees with that of `Λ` on `pairTest m 1` for every `m ≥ 2`. -/
def SourceIdentifiedWithVonMangoldt (lam : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (weilFullFunctional lam (EF.weilTest (pairTest m 1) (pairTest m 1))).re =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (pairTest m 1) (pairTest m 1))).re

/-- **Equivalence of Pair-Test Source Identification and Pointwise Agreement on `n ≥ 2`.** -/
theorem sourceIdentifiedWithVonMangoldt_iff_forall_two_le_eq (lam : ℕ → ℝ) :
    SourceIdentifiedWithVonMangoldt lam ↔
      ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  (forall_two_le_eq_iff_forall_re_weilFullFunctional_pairTest_eq lam
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))).1.symm

/-- **Source Identification Alone Does Not Prove Cone Membership.**
The von Mangoldt weight `Λ` unconditionally satisfies `SourceIdentifiedWithVonMangoldt`, whereas for
any source-identified weight `lam`, full-cone membership `WeilPositiveFull lam` is equivalent to the
Riemann Hypothesis (and is refuted whenever RH fails). -/
theorem sourceIdentifiedWithVonMangoldt_vonMangoldt_and_membership_iff :
    SourceIdentifiedWithVonMangoldt (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
    ∀ {lam : ℕ → ℝ}, SourceIdentifiedWithVonMangoldt lam →
      (WeilPositiveFull lam ↔ RiemannHypothesis) := by
  refine ⟨fun _ _ => rfl, fun {lam} hid => ?_⟩
  have heq := (sourceIdentifiedWithVonMangoldt_iff_forall_two_le_eq lam).mp hid
  rw [weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt]
  exact ⟨fun h => h.1, fun hRH => ⟨hRH, heq⟩⟩

/-- **Master Equivalence: Which Additional Estimates Prove the Sign for an Identified Source.**
Let `lam : ℕ → ℝ` be identified with `Λ` via the narrow pair tests (`SourceIdentifiedWithVonMangoldt lam`).
Then `WeilPositiveFull lam` (the sign of the full Weil functional for `lam`) is unconditionally
equivalent to each of the following additional estimates:
1. **One-sided nonpositive-cone positivity (`PositiveOnNonposCone lam`)**, where the prime sum of
   `lam` is already nonnegative;
2. **One-sided nonnegative-cone positivity (`PositiveOnNonnegCone lam`)**;
3. **Prime-power node-deletion symbol slack bound**: for every prime power `m`, deleting `m` from
   `primePowerNodes` costs at most `lam m / √m` of zero-pole symbol slack;
4. **Constant-in-aperture odd grid-tent floor (`-C ∫ F²`)** across all apertures `r > 0`;
5. **Subexponential-in-aperture odd grid-tent floor (`-C_σ e^{2σ r} ∫ F²` for every `σ > 0`)**;
6. **Subexponential-in-aperture odd receiver floor (`-C_σ e^{2σ r} ∫ F²` on `fullZeroForm F`)**;
7. **The Riemann Hypothesis (`RiemannHypothesis`)**. -/
theorem weilPositiveFull_of_sourceIdentified_iff_additional_estimates {lam : ℕ → ℝ}
    (hid : SourceIdentifiedWithVonMangoldt lam) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
    (WeilPositiveFull lam ↔ PositiveOnNonposCone lam) ∧
    (WeilPositiveFull lam ↔ PositiveOnNonnegCone lam) ∧
    (WeilPositiveFull lam ↔
      ∀ m : ℕ, IsPrimePow m →
        ZeroPoleBlindSymbolSlackOn (primePowerNodes \ {m}) (lam m / Real.sqrt m)) ∧
    (WeilPositiveFull lam ↔
      ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊)) ∧
    (WeilPositiveFull lam ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊)) ∧
    (WeilPositiveFull lam ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) ∧
    (WeilPositiveFull lam ↔ RiemannHypothesis) := by
  have heq : ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
    (sourceIdentifiedWithVonMangoldt_iff_forall_two_le_eq lam).mp hid
  have hW_iff_RH : WeilPositiveFull lam ↔ RiemannHypothesis :=
    sourceIdentifiedWithVonMangoldt_vonMangoldt_and_membership_iff.2 hid
  have h1 : WeilPositiveFull lam ↔ PositiveOnNonposCone lam := by
    rw [hW_iff_RH, positiveOnNonposCone_iff_riemannHypothesis_and_vonMangoldt_le]
    exact ⟨fun hRH => ⟨hRH, fun n hn => (heq n hn).ge⟩, fun h => h.1⟩
  have h2 : WeilPositiveFull lam ↔ PositiveOnNonnegCone lam := by
    rw [hW_iff_RH, positiveOnNonnegCone_iff_riemannHypothesis_and_le_vonMangoldt]
    exact ⟨fun hRH => ⟨hRH, fun n hn => (heq n hn).le⟩, fun h => h.1⟩
  have h3 : WeilPositiveFull lam ↔
      ∀ m : ℕ, IsPrimePow m →
        ZeroPoleBlindSymbolSlackOn (primePowerNodes \ {m}) (lam m / Real.sqrt m) := by
    rw [hW_iff_RH, riemannHypothesis_iff_forall_zeroPoleBlindSymbolSlackOn_deleted]
    refine ⟨fun h m hm => ?_, fun h m hm => ?_⟩
    · rw [heq m hm.two_le]; exact h m hm
    · rw [← heq m hm.two_le]; exact h m hm
  have h4 : WeilPositiveFull lam ↔
      ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
    rw [hW_iff_RH, riemannHypothesis_iff_bddBelow_gridTentPattern_odd_floor]
  have h5 : WeilPositiveFull lam ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ᶠ n : ℕ in atTop,
          -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤
            compactFullWeilEnergy (gridTentPattern (fun x => Real.exp (-(3 * x / 2)) * F x)
              n (-(r + 1)) ⌈2 * (r + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
    rw [hW_iff_RH, riemannHypothesis_iff_subexponential_gridTentPattern_odd_floor]
  have h6 : WeilPositiveFull lam ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
    rw [hW_iff_RH]
    constructor
    · intro hRH σ _
      refine ⟨0, fun r _ F hF hFc _ _ => ?_⟩
      have hF_c : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
      have hFc_c : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
      rw [zero_mul, zero_mul, neg_zero, fullZeroForm_eq_zeta_W_re hF hFc,
        zeta_W_eq_weilFullFunctional hF_c hFc_c]
      exact (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) _ hF_c hFc_c
    · exact riemannHypothesis_of_subexponential_odd_floor
  exact ⟨heq, h1, h2, h3, h4, h5, h6, hW_iff_RH⟩

/-- **Graded Zero-Width and Finite-Aperture Horizon Transfer for an Identified Source.**
For any weight `lam : ℕ → ℝ` satisfying `SourceIdentifiedWithVonMangoldt lam`:
1. On every `f ∈ C_c²(ℝ, ℂ)` with compact support, `(weilFullFunctional lam (EF.weilTest f f)).re`
   coincides with `(zetaZeroConfig.W f f).re`.
2. If `ℱ` has `(α, β)`-norm-controlled receiver transfer (`α, β ≥ 0`) and `compactFullWeilEnergy`
   satisfies a rate-`2σ` floor `-(C * e^{2σ r} ∫ g²)` (`C, σ ≥ 0`) on `g ∈ ℱ r`, then
   `zetaZeroWidth ≤ σ + β`.
3. There exists an absolute constant `A₀ ≥ 1` such that at any fixed aperture `R ≥ e⁶` where `lam`
   is eventually nonnegative on the smoothed grid-tent detectors
   `smoothGridTentDetector G n (-(R + 1)) M_n q` (as `q → ∞`, then `n → ∞`) for all seeds
   `G ∈ C_c²([-R, R], ℝ)`, `ZetaWindowPositive R` holds and every zero `ρ ∈ zetaZeroConfig.carrier`
   with `2 ≤ |(ρ : ℂ).im| ≤ zetaClusterHorizonHeight A₀ R` has depth `|(ρ : ℂ).re - 1 / 2| < 1 / R`. -/
theorem graded_and_finite_aperture_sign_of_sourceIdentified {lam : ℕ → ℝ}
    (hid : SourceIdentifiedWithVonMangoldt lam) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (weilFullFunctional lam (EF.weilTest f f)).re = (zetaZeroConfig.W f f).re) ∧
    (∀ {ℱ : ℝ → Set C_c(ℝ, ℝ)} {α β σ C : ℝ},
      0 ≤ α → 0 ≤ β → 0 ≤ σ → 0 ≤ C →
      HasNormControlledReceiverTransfer ℱ α β →
      (∀ r : ℝ, 0 < r → ∀ g ∈ ℱ r,
        -(C * Real.exp (2 * σ * r) * ∫ x, g x ^ 2) ≤ compactFullWeilEnergy g) →
      zetaZeroWidth ≤ σ + β) ∧
    (∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ {R : ℝ}, Real.exp 6 ≤ R →
      (∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ q : ℕ in atTop,
          let M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
          let D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
          0 ≤ (weilFullFunctional lam (EF.weilTest D D)).re) →
      ZetaWindowPositive R ∧
      ∀ ρ ∈ zetaZeroConfig.carrier,
        2 ≤ |(ρ : ℂ).im| → |(ρ : ℂ).im| ≤ zetaClusterHorizonHeight A₀ R →
        |(ρ : ℂ).re - 1 / 2| < 1 / R) := by
  have heq : ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
    (sourceIdentifiedWithVonMangoldt_iff_forall_two_le_eq lam).mp hid
  have h1 : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (weilFullFunctional lam (EF.weilTest f f)).re = (zetaZeroConfig.W f f).re := by
    intro f hf hfc
    rw [weilFullFunctional_congr heq, ← zeta_W_eq_weilFullFunctional hf hfc]
  refine ⟨h1, fun hα hβ hσ hC htr hfl =>
    zetaZeroWidth_le_of_normControlled_subfamily_transfer hα hβ hσ hC htr hfl, ?_⟩
  obtain ⟨A₀, hA₀1, hexcl⟩ := zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg
  refine ⟨A₀, hA₀1, fun {R} hR6 hdet => ?_⟩
  have hgrid : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, R < |x| → G x = 0) →
      ∀ᶠ n : ℕ in atTop,
        0 ≤ compactFullWeilEnergy
          (gridTentPattern G n (-(R + 1)) ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊) := by
    intro G hG hGc hGR
    filter_upwards [hdet G hG hGc hGR] with n hn
    set M : ℕ := ⌈2 * (R + 1) / sourceFactorialWidth (n + 1)⌉₊
    set P : C_c(ℝ, ℝ) := gridTentPattern G n (-(R + 1)) M
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hq_small : ∀ᶠ q : ℕ in atTop, 1 / ((q : ℝ) + 1) ≤ ε := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      filter_upwards [eventually_ge_atTop N] with q hq
      rw [div_le_iff₀ (by positivity)]
      have hNq : (N : ℝ) ≤ q := by exact_mod_cast hq
      have h1' : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
      nlinarith
    obtain ⟨q, hq1, hq2⟩ := (hn.and hq_small).exists
    set D : ℝ → ℂ := smoothGridTentDetector G n (-(R + 1)) M q
    obtain ⟨hD_approx, -, -⟩ := smoothGridTentDetector_fullWeil_approximation G n (-(R + 1)) M q
    dsimp only at hq1
    rw [weilFullFunctional_congr heq] at hq1
    have hlow := (abs_le.mp hD_approx).2
    linarith
  have hR0 : 0 ≤ R := (Real.exp_pos 6).le.trans hR6
  have hwin := (zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius
    hR0 hgrid).1
  exact ⟨hwin, hexcl R hR6 hgrid⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end
