import GaloisForLFunctions.RHTower.ObserverJetSignedCurvatureAndPrefixTelescoping
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier

/-!
# Exact Fubini Normal Form of Signed Observer-Jet History and Pointwise Bridge to `integerLag`

This module advances the observer-jet and Weil-lag programme in three directions:

1. **Exact Fubini Identity and Single-Sum Square-Root Mass Action (`Section 1`):**
   - Exchanging the order of summation in
     `completedSourceObserverJetSignedHistoryAction M = ∑ j ∈ range (M - 3), History M j / √(j + 1)`
     evaluates the outer `j`-sum into the harmonic square-root prefix
     `harmonicSqrtPrefix k = ∑ j ∈ range k, 1 / √(j + 1)`:
     `completedSourceObserverJetSignedHistoryAction_eq_sum_harmonicSqrtPrefix_mul_mass_sub`.
   - Using the elementary sandwich `2 √(k + 1) - 2 ≤ harmonicSqrtPrefix k ≤ 2 √k`, we show
     `0 ≤ 2 √(k + 2) - harmonicSqrtPrefix k ≤ 4` for all `k : ℕ`, reducing the double-sum
     signed history action to the single-sum square-root mass action
     `completedSourceObserverJetSqrtMassAction M = ∑ k ∈ range (M - 2), 2 √(k + 2) * (Mass M - Mass (k + 2))`
     up to an unconditional `O(M)` (and `o(M)`) error (`abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le`,
     `exists_abs_mobiusDivisorSquareRootAbel_sub_sqrtMassAction_linear`), yielding exact one-sided
     and `M = N^m` RH equivalences for `completedSourceObserverJetSqrtMassAction`.

2. **Exact Pointwise Bridge Between `completedSourceObserverJetMass`, `lagBracketSlope`, and `integerLag / √d` (`Section 2`):**
   - Combining `tendsto_completedPrimePolarGammaHarmonicPrefix_zero` (`Mass M → 0`) and
     `tendsto_weilLagFunctionReal_mul_exp_neg_half` (`lagBracketSlope M → 0`), we pass to the
     infinite-aperture limit `N → ∞` in `abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le`
     to eliminate the reference point `N` completely: for every `d ≥ 2`,
     `|completedSourceObserverJetMass d - lagBracketSlope d| ≤ (1 + |2γ|) / d`
     (`abs_completedSourceObserverJetMass_sub_lagBracketSlope_le`).
   - Using `lagBracketSlope d = integerLag d / √d + (log(2π) - trivialZeroSeriesReal d) / d`,
     we obtain for every `d ≥ 2`:
     `|completedSourceObserverJetMass d - integerLag d / √d| ≤ (7 + |2γ|) / d` and
     `|√d * completedSourceObserverJetMass d - integerLag d| ≤ (7 + |2γ|) / √d`
     (`abs_completedSourceObserverJetMass_sub_integerLag_div_sqrt_le`,
     `abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le`), proving that RH is equivalent
     to one-sided boundedness of `√M * completedSourceObserverJetMass M` (`riemannHypothesis_iff_sqrt_mul_completedSourceObserverJetMass_bddAbove`,
     `_bddBelow`, `_pow_bddAbove`, `_pow_bddBelow`).

3. **Direct Bridge to `integerLagSqrtRatioAction`, Cesàro Integer-Lag Sum, and Prime-Jump-Free Bracket Steps (`Section 3`):**
   - Substituting `√d * Mass d = integerLag d + O(1 / √d)` into `completedSourceObserverJetSqrtMassAction M`
     cancels the `√d` weights identically, reducing `completedSourceObserverJetSqrtMassAction M` to
     `integerLagSqrtRatioAction M = 2 * ∑ k ∈ range (M - 2), (√((k + 2) / M) * integerLag M - integerLag (k + 2))`
     within an unconditional `6 * (7 + |2γ|) * √M = o(M)` error
     (`abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le`,
     `tendsto_mobiusDivisorSquareRootAbel_sub_integerLagSqrtRatioAction_div_zero`,
     `exists_abs_mobiusDivisorSquareRootAbel_sub_integerLagSqrtRatioAction_linear`).
   - We also prove the prime-jump-free unit-step identity for `d * lagBracketSlope d` and `lagBracket d`,
     showing that the prime-power jump `Λ(d + 1)` cancels identically between `-ψ(d)` and
     `d * mertensSum d`, leaving the Mertens deviation `mertensSum d - log d + γ` up to `O(1 / d)`.
-/

open Complex Filter Topology MeasureTheory Set Real
open scoped BigOperators Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: Exact Fubini Identity for `completedSourceObserverJetSignedHistoryAction` and
Single-Sum Square-Root Mass Action -/

/-- Harmonic square-root prefix `∑_{j < k} 1 / √(j + 1)` arising as the Fubini weight of
`completedSourceObserverJetSignedHistoryAction`. -/
def harmonicSqrtPrefix (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, 1 / Real.sqrt (j + 1 : ℕ)

@[simp]
theorem harmonicSqrtPrefix_zero : harmonicSqrtPrefix 0 = 0 := by
  simp [harmonicSqrtPrefix]

theorem harmonicSqrtPrefix_succ (k : ℕ) :
    harmonicSqrtPrefix (k + 1) = harmonicSqrtPrefix k + 1 / Real.sqrt (k + 1 : ℕ) := by
  simp [harmonicSqrtPrefix, Finset.sum_range_succ]

theorem harmonicSqrtPrefix_nonneg (k : ℕ) : 0 ≤ harmonicSqrtPrefix k :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Upper integral-comparison bound `harmonicSqrtPrefix k ≤ 2 * √k`. -/
theorem harmonicSqrtPrefix_le_two_mul_sqrt (k : ℕ) :
    harmonicSqrtPrefix k ≤ 2 * Real.sqrt (k : ℝ) := by
  unfold harmonicSqrtPrefix
  have h := sum_one_div_sqrt_le k
  rw [sum_Icc_eq_sum_range_shift] at h
  exact h

/-- Pointwise lower step `2 * (√(j + 2) - √(j + 1)) ≤ 1 / √(j + 1)`. -/
theorem two_mul_sqrt_succ_sub_sqrt_le_inv_sqrt (j : ℕ) :
    2 * (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) ≤ 1 / Real.sqrt (j + 1 : ℕ) := by
  have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hj2 : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  have hs1 : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr hj1
  have hle : Real.sqrt (j + 1 : ℕ) ≤ Real.sqrt (j + 2 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show j + 1 ≤ j + 2 by omega))
  have hsq1 : Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ) = (j + 1 : ℕ) :=
    Real.mul_self_sqrt hj1.le
  have hsq2 : Real.sqrt (j + 2 : ℕ) * Real.sqrt (j + 2 : ℕ) = (j + 2 : ℕ) :=
    Real.mul_self_sqrt hj2.le
  have hdiff :
      (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) *
        (Real.sqrt (j + 2 : ℕ) + Real.sqrt (j + 1 : ℕ)) = 1 := by
    calc
      (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) *
          (Real.sqrt (j + 2 : ℕ) + Real.sqrt (j + 1 : ℕ)) =
        Real.sqrt (j + 2 : ℕ) * Real.sqrt (j + 2 : ℕ) -
          Real.sqrt (j + 1 : ℕ) * Real.sqrt (j + 1 : ℕ) := by ring
      _ = (j + 2 : ℕ) - (j + 1 : ℕ) := by rw [hsq2, hsq1]
      _ = 1 := by push_cast; ring
  rw [le_div_iff₀ hs1]
  have hnonneg : 0 ≤ Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ) := sub_nonneg.mpr hle
  have hsum : 2 * Real.sqrt (j + 1 : ℕ) ≤ Real.sqrt (j + 2 : ℕ) + Real.sqrt (j + 1 : ℕ) := by
    linarith
  calc
    2 * (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) * Real.sqrt (j + 1 : ℕ) =
      (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) * (2 * Real.sqrt (j + 1 : ℕ)) := by ring
    _ ≤ (Real.sqrt (j + 2 : ℕ) - Real.sqrt (j + 1 : ℕ)) *
        (Real.sqrt (j + 2 : ℕ) + Real.sqrt (j + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum hnonneg
    _ = 1 := hdiff

/-- Lower integral-comparison bound `2 * √(k + 1) - 2 ≤ harmonicSqrtPrefix k`. -/
theorem two_mul_sqrt_succ_sub_two_le_harmonicSqrtPrefix (k : ℕ) :
    2 * Real.sqrt (k + 1 : ℕ) - 2 ≤ harmonicSqrtPrefix k := by
  induction k with
  | zero =>
    simp [harmonicSqrtPrefix]
  | succ k ih =>
    rw [harmonicSqrtPrefix_succ]
    have hstep := two_mul_sqrt_succ_sub_sqrt_le_inv_sqrt k
    rw [show k + 1 + 1 = k + 2 by omega]
    linarith

/-- For every `k : ℕ`, `harmonicSqrtPrefix k` lies within `[2 * √(k + 2) - 4, 2 * √(k + 2)]`. -/
theorem two_mul_sqrt_add_two_sub_harmonicSqrtPrefix_bounds (k : ℕ) :
    0 ≤ 2 * Real.sqrt (k + 2 : ℕ) - harmonicSqrtPrefix k ∧
      2 * Real.sqrt (k + 2 : ℕ) - harmonicSqrtPrefix k ≤ 4 := by
  have hup := harmonicSqrtPrefix_le_two_mul_sqrt k
  have hlow := two_mul_sqrt_succ_sub_two_le_harmonicSqrtPrefix k
  have hle1 : Real.sqrt (k : ℝ) ≤ Real.sqrt (k + 2 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show k ≤ k + 2 by omega))
  have hstep : Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ) ≤ 1 := by
    have h := two_mul_sqrt_succ_sub_sqrt_le_inv_sqrt k
    have hs1 : (1 : ℝ) ≤ Real.sqrt (k + 1 : ℕ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k + 1 by omega))
    have hinv : 1 / Real.sqrt (k + 1 : ℕ) ≤ 1 := div_le_one_of_le₀ hs1 (by positivity)
    linarith
  constructor <;> linarith

/-- General discrete Fubini identity exchanging `∑_{j < N} w j * ∑_{j + 1 ≤ k < N + 1} f k`
with `∑_{k < N + 1} (∑_{j < k} w j) * f k`. -/
theorem sum_range_mul_sum_Ico_eq_sum_range_prefix (w f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, w j * (∑ k ∈ Finset.Ico (j + 1) (N + 1), f k)) =
      ∑ k ∈ Finset.range (N + 1), (∑ j ∈ Finset.range k, w j) * f k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hlast : ∑ k ∈ Finset.Ico (N + 1) (N + 1 + 1), f k = f (N + 1) := by
      simp
    rw [hlast]
    have hsplit :
        (∑ j ∈ Finset.range N, w j * (∑ k ∈ Finset.Ico (j + 1) (N + 1 + 1), f k)) =
          (∑ j ∈ Finset.range N, w j * (∑ k ∈ Finset.Ico (j + 1) (N + 1), f k)) +
            (∑ j ∈ Finset.range N, w j) * f (N + 1) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < N := Finset.mem_range.mp hj
      rw [Finset.sum_Ico_succ_top (by omega : j + 1 ≤ N + 1)]
      ring
    rw [hsplit, ih, Finset.sum_range_succ (f := fun k => (∑ j ∈ Finset.range k, w j) * f k) (n := N + 1)]
    rw [Finset.sum_range_succ (f := w) (n := N)]
    ring

/-- **Exact Fubini Identity for `completedSourceObserverJetSignedHistoryAction`:**
Exchanging the summation order in `completedSourceObserverJetSignedHistoryAction M` evaluates the
outer `j`-sum into `harmonicSqrtPrefix k`. -/
theorem completedSourceObserverJetSignedHistoryAction_eq_sum_harmonicSqrtPrefix_mul_mass_sub
    {M : ℕ} (hM : 3 ≤ M) :
    completedSourceObserverJetSignedHistoryAction M =
      ∑ k ∈ Finset.range (M - 2),
        harmonicSqrtPrefix k *
          (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) := by
  unfold completedSourceObserverJetSignedHistoryAction harmonicSqrtPrefix
  have hcongr :
      (∑ j ∈ Finset.range (M - 3),
        completedSourceObserverJetHistory M j / Real.sqrt (j + 1 : ℕ)) =
      ∑ j ∈ Finset.range (M - 3),
        (1 / Real.sqrt (j + 1 : ℕ)) *
          (∑ k ∈ Finset.Ico (j + 1) (M - 3 + 1),
            (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM hj,
      show M - 3 + 1 = M - 2 by omega]
    ring
  rw [hcongr, sum_range_mul_sum_Ico_eq_sum_range_prefix]
  rw [show M - 3 + 1 = M - 2 by omega]

/-- Single-sum square-root mass action obtained by replacing `harmonicSqrtPrefix k` with `2 * √(k + 2)`. -/
def completedSourceObserverJetSqrtMassAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    2 * Real.sqrt (k + 2 : ℕ) *
      (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2))

/-- The difference between `completedSourceObserverJetSqrtMassAction M` and
`completedSourceObserverJetSignedHistoryAction M` is bounded by
`4 * ∑_{k < M - 2} |Mass M - Mass (k + 2)|`. -/
theorem abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le_sum_abs
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M| ≤
      4 * ∑ k ∈ Finset.range (M - 2),
        |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)| := by
  rw [completedSourceObserverJetSqrtMassAction,
    completedSourceObserverJetSignedHistoryAction_eq_sum_harmonicSqrtPrefix_mul_mass_sub hM,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hsub :
      2 * Real.sqrt (k + 2 : ℕ) *
          (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
        harmonicSqrtPrefix k *
          (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) =
      (2 * Real.sqrt (k + 2 : ℕ) - harmonicSqrtPrefix k) *
        (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) := by ring
  rw [hsub, abs_mul]
  have hb := two_mul_sqrt_add_two_sub_harmonicSqrtPrefix_bounds k
  rw [abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)

/-- Unconditional `8 * S * M` bound between `completedSourceObserverJetSqrtMassAction M` and
`completedSourceObserverJetSignedHistoryAction M`. -/
theorem abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M| ≤
      8 * (∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|) * (M : ℝ) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)| ≤ 2 * S := by
    intro k _
    have h1 := abs_completedSourceObserverJetMass_le M
    have h2 := abs_completedSourceObserverJetMass_le (k + 2)
    calc
      |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)| ≤
        |completedSourceObserverJetMass M| + |completedSourceObserverJetMass (k + 2)| :=
        abs_sub _ _
      _ ≤ S + S := add_le_add h1 h2
      _ = 2 * S := by ring
  have hsum :
      (∑ k ∈ Finset.range (M - 2),
        |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)|) ≤
      2 * S * (M : ℝ) := by
    calc
      (∑ k ∈ Finset.range (M - 2),
        |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)|) ≤
        ∑ _k ∈ Finset.range (M - 2), (2 * S) := Finset.sum_le_sum hterm
      _ = ((M - 2 : ℕ) : ℝ) * (2 * S) := by simp
      _ ≤ (M : ℝ) * (2 * S) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - 2 ≤ M by omega)) (by positivity)
      _ = 2 * S * (M : ℝ) := by ring
  calc
    |completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M| ≤
      4 * ∑ k ∈ Finset.range (M - 2),
        |completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)| :=
      abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le_sum_abs hM
    _ ≤ 4 * (2 * S * (M : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * S * (M : ℝ) := by ring

/-- Uniform `O(M)` comparison between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * completedSourceObserverJetSqrtMassAction M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_sqrtMassAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M| ≤ B * (M : ℝ) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_signedHistory_linear
  refine ⟨B₁ + 3 * S, by positivity, fun M hM => ?_⟩
  have h1 := hB₁ M hM
  have h2 := abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hM
  have hsplit :
      mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M =
      (mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M) -
      (3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M) := by ring
  rw [hsplit]
  calc
    |(mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M) -
      (3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M)| ≤
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| +
      |(3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M)| := abs_sub _ _
    _ = |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSignedHistoryAction M| +
      (3 / 8 : ℝ) * |completedSourceObserverJetSqrtMassAction M -
        completedSourceObserverJetSignedHistoryAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₁ * (M : ℝ) + (3 / 8 : ℝ) * (8 * S * (M : ℝ)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = (B₁ + 3 * S) * (M : ℝ) := by ring

/-- **One-sided upper RH equivalence for `completedSourceObserverJetSqrtMassAction`.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        completedSourceObserverJetSqrtMassAction M ≤ C * (M : ℝ) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  rw [riemannHypothesis_iff_completedSourceObserverJetSignedHistory_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hM)).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hM)).2
    linarith

/-- **One-sided lower RH equivalence for `completedSourceObserverJetSqrtMassAction`.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ completedSourceObserverJetSqrtMassAction M := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  rw [riemannHypothesis_iff_completedSourceObserverJetSignedHistory_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hM)).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hM)).1
    linarith

/-- **Polynomial-schedule (`M = N^m`) upper RH equivalence for `completedSourceObserverJetSqrtMassAction`.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        completedSourceObserverJetSqrtMassAction (N ^ m) ≤ C * (N ^ m : ℕ) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  rw [riemannHypothesis_iff_completedSourceObserverJetSignedHistory_pow_bddAbove hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun N hN => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN m
    have h1 := hC N hN
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hNm3)).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun N hN => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN m
    have h1 := hC N hN
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hNm3)).2
    linarith

/-- **Polynomial-schedule (`M = N^m`) lower RH equivalence for `completedSourceObserverJetSqrtMassAction`.** -/
theorem riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
        -C * (N ^ m : ℕ) ≤ completedSourceObserverJetSqrtMassAction (N ^ m) := by
  let S : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  have hS : 0 ≤ S := tsum_nonneg fun _ => abs_nonneg _
  rw [riemannHypothesis_iff_completedSourceObserverJetSignedHistory_pow_bddBelow hm]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun N hN => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN m
    have h1 := hC N hN
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hNm3)).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 8 * S, fun N hN => ?_⟩
    have hNm3 : 3 ≤ N ^ m := by
      calc 3 = 3 ^ 1 := (Nat.pow_one 3).symm
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by omega) hm
        _ ≤ N ^ m := Nat.pow_le_pow_left hN m
    have h1 := hC N hN
    have h2 := (abs_sub_le_iff.mp
      (abs_completedSourceObserverJetSqrtMassAction_sub_signedHistory_le hNm3)).1
    linarith

/-! ## Section 2: Exact Pointwise Bridge Between `completedSourceObserverJetMass`,
`lagBracketSlope`, and `integerLag / √d` -/

/-- Exact relation between `lagBracketSlope d` and `integerLag d / √d` for `2 ≤ d`. -/
theorem lagBracketSlope_eq_integerLag_div_sqrt_add {d : ℕ} (hd : 2 ≤ d) :
    lagBracketSlope d =
      integerLag d / Real.sqrt (d : ℝ) +
        (Real.log (2 * Real.pi) - trivialZeroSeriesReal d) / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0.le
  rw [integerLag_eq_lagBracket hd, lagBracketSlope]
  rw [div_div, hsq]
  ring

/-- For `1 ≤ d`, `|trivialZeroSeriesReal d - log(2π)| ≤ 6`. -/
theorem abs_trivialZeroSeriesReal_sub_log_two_pi_le {d : ℕ} (hd : 1 ≤ d) :
    |trivialZeroSeriesReal d - Real.log (2 * Real.pi)| ≤ 6 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 := trivialZeroSeriesReal_nonneg hd1
  have h1 := trivialZeroSeriesReal_le_one hd1
  have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise bound `|lagBracketSlope d - integerLag d / √d| ≤ 6 / d` for `2 ≤ d`. -/
theorem abs_lagBracketSlope_sub_integerLag_div_sqrt_le {d : ℕ} (hd : 2 ≤ d) :
    |lagBracketSlope d - integerLag d / Real.sqrt (d : ℝ)| ≤ 6 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [lagBracketSlope_eq_integerLag_div_sqrt_add hd, add_sub_cancel_left,
    abs_div, abs_of_pos hd0, abs_sub_comm]
  exact div_le_div_of_nonneg_right (abs_trivialZeroSeriesReal_sub_log_two_pi_le (by omega)) hd0.le

/-- Unconditional convergence `completedSourceObserverJetMass (N + 2) → 0` as `N → ∞`. -/
theorem tendsto_completedSourceObserverJetMass_add_two_zero :
    Tendsto (fun N : ℕ => completedSourceObserverJetMass (N + 2)) atTop (𝓝 0) := by
  have h := tendsto_completedPrimePolarGammaHarmonicPrefix_zero
  refine h.congr fun N => ?_
  rfl

/-- Unconditional convergence `integerLag n / √n → 0` as `n → ∞`. -/
theorem tendsto_integerLag_div_sqrt_zero :
    Tendsto (fun n : ℕ => integerLag n / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfront := tendsto_weilLagFunctionReal_mul_exp_neg_half.comp hlog
  refine hfront.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
    calc
      Real.sqrt (n : ℝ) = Real.sqrt (Real.exp (Real.log (n : ℝ))) := by
        rw [Real.exp_log hn0]
      _ = Real.sqrt (Real.exp (Real.log (n : ℝ) / 2) * Real.exp (Real.log (n : ℝ) / 2)) := by
        rw [← Real.exp_add, add_halves]
      _ = Real.exp (Real.log (n : ℝ) / 2) :=
        Real.sqrt_mul_self (Real.exp_pos _).le
  dsimp [Function.comp_def, integerLag]
  rw [hsqrt, eq_div_iff (Real.exp_pos _).ne', mul_assoc, ← Real.exp_add]
  have hzero : -Real.log (n : ℝ) / 2 + Real.log (n : ℝ) / 2 = 0 := by ring
  rw [hzero, Real.exp_zero, mul_one]

/-- Unconditional convergence `lagBracketSlope n → 0` as `n → ∞`. -/
theorem tendsto_lagBracketSlope_zero :
    Tendsto lagBracketSlope atTop (𝓝 0) := by
  have h1 := tendsto_integerLag_div_sqrt_zero
  have h2 : Tendsto (fun d : ℕ => (6 : ℝ) / (d : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun d : ℕ => lagBracketSlope d - integerLag d / Real.sqrt (d : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 2] with d hd
    rw [Real.norm_eq_abs]
    exact abs_lagBracketSlope_sub_integerLag_div_sqrt_le hd
  simpa using hdiff.add h1

/-- **Exact Pointwise Bridge Between `completedSourceObserverJetMass` and `lagBracketSlope`:**
Passing to the limit `N → ∞` in `abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le`
eliminates the second endpoint `N` completely, giving
`|completedSourceObserverJetMass d - lagBracketSlope d| ≤ (1 + |2γ|) / d` for every `d ≥ 2`. -/
theorem abs_completedSourceObserverJetMass_sub_lagBracketSlope_le {d : ℕ} (hd : 2 ≤ d) :
    |completedSourceObserverJetMass d - lagBracketSlope d| ≤
      (1 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlim1 : Tendsto (fun N : ℕ =>
      (completedSourceObserverJetMass (N + 2) - completedSourceObserverJetMass d) -
        (lagBracketSlope (N + 2) - lagBracketSlope d))
      atTop (𝓝 ((0 - completedSourceObserverJetMass d) - (0 - lagBracketSlope d))) :=
    (tendsto_completedSourceObserverJetMass_add_two_zero.sub tendsto_const_nhds).sub
      ((tendsto_lagBracketSlope_zero.comp (tendsto_add_atTop_nat 2)).sub tendsto_const_nhds)
  have hlim_abs : Tendsto (fun N : ℕ =>
      |(completedSourceObserverJetMass (N + 2) - completedSourceObserverJetMass d) -
        (lagBracketSlope (N + 2) - lagBracketSlope d)|)
      atTop (𝓝 |completedSourceObserverJetMass d - lagBracketSlope d|) := by
    have h := hlim1.abs
    have heq : |(0 - completedSourceObserverJetMass d) - (0 - lagBracketSlope d)| =
        |completedSourceObserverJetMass d - lagBracketSlope d| := by
      rw [← abs_neg]
      congr 1
      ring
    rwa [heq] at h
  refine le_of_tendsto hlim_abs ?_
  filter_upwards [eventually_ge_atTop (d - 2)] with N hN
  have hstep := abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le hN
  have hd2 : d - 2 + 2 = d := by omega
  have hd2R : ((d - 2 : ℕ) : ℝ) + 2 = (d : ℝ) := by exact_mod_cast hd2
  have hmassN : observerJetMass completedPrimePolarGammaHarmonicCharge N =
      completedSourceObserverJetMass (N + 2) := rfl
  have hmassd : observerJetMass completedPrimePolarGammaHarmonicCharge (d - 2) =
      completedSourceObserverJetMass d := rfl
  rw [hmassN, hmassd, hd2, hd2R] at hstep
  have hinv_nonneg : (0 : ℝ) ≤ 1 / ((N : ℝ) + 2) := by positivity
  have hgap_le : 1 / (d : ℝ) - 1 / ((N : ℝ) + 2) ≤ 1 / (d : ℝ) := by linarith
  calc
    |(completedSourceObserverJetMass (N + 2) - completedSourceObserverJetMass d) -
        (lagBracketSlope (N + 2) - lagBracketSlope d)| ≤
      (1 + |2 * Real.eulerMascheroniConstant|) * (1 / (d : ℝ) - 1 / ((N : ℝ) + 2)) := hstep
    _ ≤ (1 + |2 * Real.eulerMascheroniConstant|) * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap_le (by positivity)
    _ = (1 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ) := by ring

/-- **Pointwise Bridge Between `completedSourceObserverJetMass d` and `integerLag d / √d`:**
For every `d ≥ 2`, `|completedSourceObserverJetMass d - integerLag d / √d| ≤ (7 + |2γ|) / d`. -/
theorem abs_completedSourceObserverJetMass_sub_integerLag_div_sqrt_le {d : ℕ} (hd : 2 ≤ d) :
    |completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)| ≤
      (7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ) := by
  have h1 := abs_completedSourceObserverJetMass_sub_lagBracketSlope_le hd
  have h2 := abs_lagBracketSlope_sub_integerLag_div_sqrt_le hd
  calc
    |completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)| =
      |(completedSourceObserverJetMass d - lagBracketSlope d) +
        (lagBracketSlope d - integerLag d / Real.sqrt (d : ℝ))| := by ring_nf
    _ ≤ |completedSourceObserverJetMass d - lagBracketSlope d| +
        |lagBracketSlope d - integerLag d / Real.sqrt (d : ℝ)| := abs_add_le _ _
    _ ≤ (1 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ) + 6 / (d : ℝ) := add_le_add h1 h2
    _ = (7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ) := by ring

/-- **Pointwise Scaled Bridge Between `√d * completedSourceObserverJetMass d` and `integerLag d`:**
For every `d ≥ 2`, `|√d * completedSourceObserverJetMass d - integerLag d| ≤ (7 + |2γ|) / √d`. -/
theorem abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le {d : ℕ} (hd : 2 ≤ d) :
    |Real.sqrt (d : ℝ) * completedSourceObserverJetMass d - integerLag d| ≤
      (7 + |2 * Real.eulerMascheroniConstant|) / Real.sqrt (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0.le
  have h1 := abs_completedSourceObserverJetMass_sub_integerLag_div_sqrt_le hd
  have hmul := mul_le_mul_of_nonneg_left h1 hsd.le
  have hlhs :
      Real.sqrt (d : ℝ) * |completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)| =
        |Real.sqrt (d : ℝ) * completedSourceObserverJetMass d - integerLag d| := by
    have hinner :
        Real.sqrt (d : ℝ) * (completedSourceObserverJetMass d - integerLag d / Real.sqrt (d : ℝ)) =
          Real.sqrt (d : ℝ) * completedSourceObserverJetMass d - integerLag d := by
      rw [mul_sub, mul_div_cancel₀ _ hsd.ne']
    symm
    rw [← hinner, abs_mul, abs_of_pos hsd]
  have hrhs :
      Real.sqrt (d : ℝ) * ((7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ)) =
        (7 + |2 * Real.eulerMascheroniConstant|) / Real.sqrt (d : ℝ) := by
    apply (eq_div_iff hsd.ne').mpr
    calc
      Real.sqrt (d : ℝ) * ((7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ)) * Real.sqrt (d : ℝ) =
        ((7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ)) *
          (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by ring
      _ = ((7 + |2 * Real.eulerMascheroniConstant|) / (d : ℝ)) * (d : ℝ) := by rw [hsq]
      _ = 7 + |2 * Real.eulerMascheroniConstant| := div_mul_cancel₀ _ hd0.ne'
  linarith

/-- Uniform `O(1)` bound `|√d * completedSourceObserverJetMass d - integerLag d| ≤ 7 + |2γ|` for `d ≥ 2`. -/
theorem abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const {d : ℕ} (hd : 2 ≤ d) :
    |Real.sqrt (d : ℝ) * completedSourceObserverJetMass d - integerLag d| ≤
      7 + |2 * Real.eulerMascheroniConstant| := by
  have h1 := abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le hd
  have hsd1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
  exact h1.trans (div_le_self (by positivity) hsd1)

/-- **One-sided upper RH equivalence for `√M * completedSourceObserverJetMass M`.** -/
theorem riemannHypothesis_iff_sqrt_mul_completedSourceObserverJetMass_bddAbove :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M →
        Real.sqrt (M : ℝ) * completedSourceObserverJetMass M ≤ B := by
  rw [riemannHypothesis_iff_integerLag_bddAbove]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + (7 + |2 * Real.eulerMascheroniConstant|), fun M hM => ?_⟩
    have h1 := hB M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hM)).1
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B + (7 + |2 * Real.eulerMascheroniConstant|), fun M hM => ?_⟩
    have h1 := hB M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hM)).2
    linarith

/-- **One-sided lower RH equivalence for `√M * completedSourceObserverJetMass M`.** -/
theorem riemannHypothesis_iff_sqrt_mul_completedSourceObserverJetMass_bddBelow :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M →
        B ≤ Real.sqrt (M : ℝ) * completedSourceObserverJetMass M := by
  rw [riemannHypothesis_iff_integerLag_bddBelow]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B - (7 + |2 * Real.eulerMascheroniConstant|), fun M hM => ?_⟩
    have h1 := hB M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hM)).2
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B - (7 + |2 * Real.eulerMascheroniConstant|), fun M hM => ?_⟩
    have h1 := hB M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hM)).1
    linarith

/-- **Polynomial-schedule (`M = N^m`) upper RH equivalence for `√M * completedSourceObserverJetMass M`.** -/
theorem riemannHypothesis_iff_sqrt_mul_completedSourceObserverJetMass_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
        Real.sqrt (j ^ m : ℕ) * completedSourceObserverJetMass (j ^ m) ≤ B := by
  rw [riemannHypothesis_iff_integerLag_pow_bddAbove hm]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + (7 + |2 * Real.eulerMascheroniConstant|), fun j hj => ?_⟩
    have h1 := hB j hj
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hj)).1
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B + (7 + |2 * Real.eulerMascheroniConstant|), fun j hj => ?_⟩
    have h1 := hB j hj
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hj)).2
    linarith

/-- **Polynomial-schedule (`M = N^m`) lower RH equivalence for `√M * completedSourceObserverJetMass M`.** -/
theorem riemannHypothesis_iff_sqrt_mul_completedSourceObserverJetMass_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
        B ≤ Real.sqrt (j ^ m : ℕ) * completedSourceObserverJetMass (j ^ m) := by
  rw [riemannHypothesis_iff_integerLag_pow_bddBelow hm]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B - (7 + |2 * Real.eulerMascheroniConstant|), fun j hj => ?_⟩
    have h1 := hB j hj
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hj)).2
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B - (7 + |2 * Real.eulerMascheroniConstant|), fun j hj => ?_⟩
    have h1 := hB j hj
    have h2 := (abs_sub_le_iff.mp
      (abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le_const hj)).1
    linarith

/-! ## Section 3: Direct Bridge to `integerLagSqrtRatioAction`, Cesàro Integer-Lag Sum,
and Prime-Jump-Free Bracket Steps -/

/-- The single-sum square-root ratio action of `integerLag`:
`2 * ∑_{k < M - 2} (√((k + 2) / M) * integerLag M - integerLag (k + 2))`. -/
def integerLagSqrtRatioAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    2 * (Real.sqrt (k + 2 : ℕ) * (integerLag M / Real.sqrt (M : ℝ)) - integerLag (k + 2))

/-- Cesàro sum `∑_{k < M - 2} integerLag (k + 2) = ∑_{2 ≤ d < M} integerLag d`. -/
def integerLagCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), integerLag (k + 2)

/-- Exact decomposition of `integerLagSqrtRatioAction M` into the terminal `integerLag M`
term and `-2 * integerLagCesaroSum M`. -/
theorem integerLagSqrtRatioAction_eq_terminal_sub_two_mul_cesaroSum (M : ℕ) :
    integerLagSqrtRatioAction M =
      (∑ k ∈ Finset.range (M - 2), 2 * Real.sqrt (k + 2 : ℕ)) *
        (integerLag M / Real.sqrt (M : ℝ)) -
        2 * integerLagCesaroSum M := by
  unfold integerLagSqrtRatioAction integerLagCesaroSum
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Unconditional `O(√M)` Bridge Between `completedSourceObserverJetSqrtMassAction` and
`integerLagSqrtRatioAction`:**
Substituting `√(k + 2) * Mass (k + 2) = integerLag (k + 2) + O(1 / √(k + 2))` cancels the
`√(k + 2)` weights identically, leaving an error bounded unconditionally by
`6 * (7 + |2γ|) * √M = o(M)`. -/
theorem abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M| ≤
      6 * (7 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt (M : ℝ) := by
  let Cγ : ℝ := 7 + |2 * Real.eulerMascheroniConstant|
  have hCγ : 0 ≤ Cγ := by positivity
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM0
  have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM0.le
  unfold completedSourceObserverJetSqrtMassAction integerLagSqrtRatioAction
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |2 * Real.sqrt (k + 2 : ℕ) *
          (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
        2 * (Real.sqrt (k + 2 : ℕ) * (integerLag M / Real.sqrt (M : ℝ)) -
          integerLag (k + 2))| ≤
      2 * Cγ / Real.sqrt (M : ℝ) + 2 * Cγ / Real.sqrt (k + 1 : ℕ) := by
    intro k hk
    have hk' : k < M - 2 := Finset.mem_range.mp hk
    have hsplit :
        2 * Real.sqrt (k + 2 : ℕ) *
            (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
          2 * (Real.sqrt (k + 2 : ℕ) * (integerLag M / Real.sqrt (M : ℝ)) -
            integerLag (k + 2)) =
        2 * Real.sqrt (k + 2 : ℕ) *
            (completedSourceObserverJetMass M - integerLag M / Real.sqrt (M : ℝ)) -
          2 * (Real.sqrt (k + 2 : ℕ) * completedSourceObserverJetMass (k + 2) -
            integerLag (k + 2)) := by ring
    rw [hsplit]
    have h1 := abs_completedSourceObserverJetMass_sub_integerLag_div_sqrt_le (d := M) (by omega)
    have h2 := abs_sqrt_mul_completedSourceObserverJetMass_sub_integerLag_le (d := k + 2) (by omega)
    have hsk_le : Real.sqrt (k + 2 : ℕ) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ M by omega))
    have hpart1 :
        |2 * Real.sqrt (k + 2 : ℕ) *
          (completedSourceObserverJetMass M - integerLag M / Real.sqrt (M : ℝ))| ≤
        2 * Cγ / Real.sqrt (M : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (k + 2 : ℕ))]
      calc
        2 * Real.sqrt (k + 2 : ℕ) *
            |completedSourceObserverJetMass M - integerLag M / Real.sqrt (M : ℝ)| ≤
          2 * Real.sqrt (M : ℝ) * (Cγ / (M : ℝ)) :=
          mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)
        _ = 2 * Cγ / Real.sqrt (M : ℝ) := by
          apply (eq_div_iff hsM.ne').mpr
          calc
            2 * Real.sqrt (M : ℝ) * (Cγ / (M : ℝ)) * Real.sqrt (M : ℝ) =
              2 * ((Cγ / (M : ℝ)) * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ))) := by ring
            _ = 2 * ((Cγ / (M : ℝ)) * (M : ℝ)) := by rw [hsqM]
            _ = 2 * Cγ := by rw [div_mul_cancel₀ _ hM0.ne']
    have hpart2 :
        |2 * (Real.sqrt (k + 2 : ℕ) * completedSourceObserverJetMass (k + 2) -
          integerLag (k + 2))| ≤
        2 * Cγ / Real.sqrt (k + 1 : ℕ) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hsk1 : Real.sqrt (k + 1 : ℕ) ≤ Real.sqrt (k + 2 : ℕ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
      have hdiv : Cγ / Real.sqrt ((k + 2 : ℕ) : ℝ) ≤ Cγ / Real.sqrt (k + 1 : ℕ) :=
        div_le_div_of_nonneg_left hCγ (Real.sqrt_pos.mpr (by positivity)) hsk1
      have h2' : |Real.sqrt (k + 2 : ℕ) * completedSourceObserverJetMass (k + 2) -
          integerLag (k + 2)| ≤ Cγ / Real.sqrt (k + 1 : ℕ) := h2.trans hdiv
      calc
        2 * |Real.sqrt (k + 2 : ℕ) * completedSourceObserverJetMass (k + 2) -
            integerLag (k + 2)| ≤
          2 * (Cγ / Real.sqrt (k + 1 : ℕ)) :=
          mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = 2 * Cγ / Real.sqrt (k + 1 : ℕ) := by ring
    exact (abs_sub _ _).trans (add_le_add hpart1 hpart2)
  have hsum1 :
      (∑ _k ∈ Finset.range (M - 2), (2 * Cγ / Real.sqrt (M : ℝ))) ≤
        2 * Cγ * Real.sqrt (M : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hle : ((M - 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show M - 2 ≤ M by omega)
    calc
      ((M - 2 : ℕ) : ℝ) * (2 * Cγ / Real.sqrt (M : ℝ)) ≤
        (M : ℝ) * (2 * Cγ / Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 2 * Cγ * Real.sqrt (M : ℝ) := by
        calc
          (M : ℝ) * (2 * Cγ / Real.sqrt (M : ℝ)) =
            (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * (2 * Cγ / Real.sqrt (M : ℝ)) := by
            rw [hsqM]
          _ = Real.sqrt (M : ℝ) * ((2 * Cγ / Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ)) := by ring
          _ = Real.sqrt (M : ℝ) * (2 * Cγ) := by rw [div_mul_cancel₀ _ hsM.ne']
          _ = 2 * Cγ * Real.sqrt (M : ℝ) := by ring
  have hsum2 :
      (∑ k ∈ Finset.range (M - 2), (2 * Cγ / Real.sqrt (k + 1 : ℕ))) ≤
        4 * Cγ * Real.sqrt (M : ℝ) := by
    have hrewrite :
        (∑ k ∈ Finset.range (M - 2), (2 * Cγ / Real.sqrt (k + 1 : ℕ))) =
          2 * Cγ * harmonicSqrtPrefix (M - 2) := by
      unfold harmonicSqrtPrefix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hrewrite]
    have hinv := harmonicSqrtPrefix_le_two_mul_sqrt (M - 2)
    have hle : Real.sqrt ((M - 2 : ℕ) : ℝ) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show M - 2 ≤ M by omega))
    calc
      2 * Cγ * harmonicSqrtPrefix (M - 2) ≤
        2 * Cγ * (2 * Real.sqrt ((M - 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ 2 * Cγ * (2 * Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * Cγ * Real.sqrt (M : ℝ) := by ring
  calc
    |∑ k ∈ Finset.range (M - 2),
        (2 * Real.sqrt (k + 2 : ℕ) *
            (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
          2 * (Real.sqrt (k + 2 : ℕ) * (integerLag M / Real.sqrt (M : ℝ)) -
            integerLag (k + 2)))| ≤
      ∑ k ∈ Finset.range (M - 2),
        (2 * Cγ / Real.sqrt (M : ℝ) + 2 * Cγ / Real.sqrt (k + 1 : ℕ)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (∑ _k ∈ Finset.range (M - 2), (2 * Cγ / Real.sqrt (M : ℝ))) +
        (∑ k ∈ Finset.range (M - 2), (2 * Cγ / Real.sqrt (k + 1 : ℕ))) :=
      Finset.sum_add_distrib
    _ ≤ 2 * Cγ * Real.sqrt (M : ℝ) + 4 * Cγ * Real.sqrt (M : ℝ) :=
      add_le_add hsum1 hsum2
    _ = 6 * Cγ * Real.sqrt (M : ℝ) := by ring

/-- Uniform `O(M)` comparison between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * integerLagSqrtRatioAction M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_integerLagSqrtRatioAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagSqrtRatioAction M| ≤ B * (M : ℝ) := by
  let Cγ : ℝ := 7 + |2 * Real.eulerMascheroniConstant|
  have hCγ : 0 ≤ Cγ := by positivity
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_abs_mobiusDivisorSquareRootAbel_sub_sqrtMassAction_linear
  refine ⟨B₁ + (9 / 4 : ℝ) * Cγ, by positivity, fun M hM => ?_⟩
  have h1 := hB₁ M hM
  have h2 := abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM
  have hsM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hM0 : (0 : ℝ) ≤ M := by positivity
    nlinarith [Real.sq_sqrt hM0, Real.sqrt_le_sqrt hM1, Real.sqrt_one]
  have h2' : |completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M| ≤
      6 * Cγ * (M : ℝ) :=
    h2.trans (mul_le_mul_of_nonneg_left hsM (by positivity))
  have hsplit :
      mobiusDivisorSquareRootAbelMoment M - (3 / 8 : ℝ) * integerLagSqrtRatioAction M =
      (mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M) +
      (3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M) := by
    ring
  rw [hsplit]
  calc
    |(mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M) +
      (3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M)| ≤
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M| +
      |(3 / 8 : ℝ) * (completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M)| :=
      abs_add_le _ _
    _ = |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * completedSourceObserverJetSqrtMassAction M| +
      (3 / 8 : ℝ) * |completedSourceObserverJetSqrtMassAction M - integerLagSqrtRatioAction M| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)]
    _ ≤ B₁ * (M : ℝ) + (3 / 8 : ℝ) * (6 * Cγ * (M : ℝ)) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2' (by norm_num))
    _ = (B₁ + (9 / 4 : ℝ) * Cγ) * (M : ℝ) := by ring

/-- **One-sided upper RH equivalence for `integerLagSqrtRatioAction`.** -/
theorem riemannHypothesis_iff_integerLagSqrtRatioAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        integerLagSqrtRatioAction M ≤ C * (M : ℝ) := by
  let Cγ : ℝ := 7 + |2 * Real.eulerMascheroniConstant|
  have hCγ : 0 ≤ Cγ := by positivity
  rw [riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 6 * Cγ, fun M hM => ?_⟩
    have hsM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith [Real.sq_sqrt hM0, Real.sqrt_le_sqrt hM1, Real.sqrt_one]
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      ((abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM).trans
        (mul_le_mul_of_nonneg_left hsM (by positivity)))).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 6 * Cγ, fun M hM => ?_⟩
    have hsM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith [Real.sq_sqrt hM0, Real.sqrt_le_sqrt hM1, Real.sqrt_one]
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      ((abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM).trans
        (mul_le_mul_of_nonneg_left hsM (by positivity)))).1
    linarith

/-- **One-sided lower RH equivalence for `integerLagSqrtRatioAction`.** -/
theorem riemannHypothesis_iff_integerLagSqrtRatioAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ integerLagSqrtRatioAction M := by
  let Cγ : ℝ := 7 + |2 * Real.eulerMascheroniConstant|
  have hCγ : 0 ≤ Cγ := by positivity
  rw [riemannHypothesis_iff_completedSourceObserverJetSqrtMassAction_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + 6 * Cγ, fun M hM => ?_⟩
    have hsM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith [Real.sq_sqrt hM0, Real.sqrt_le_sqrt hM1, Real.sqrt_one]
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      ((abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM).trans
        (mul_le_mul_of_nonneg_left hsM (by positivity)))).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + 6 * Cγ, fun M hM => ?_⟩
    have hsM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith [Real.sq_sqrt hM0, Real.sqrt_le_sqrt hM1, Real.sqrt_one]
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      ((abs_completedSourceObserverJetSqrtMassAction_sub_integerLagSqrtRatioAction_le hM).trans
        (mul_le_mul_of_nonneg_left hsM (by positivity)))).2
    linarith

/-- **Prime-Jump-Free Unit Step of `d * lagBracketSlope d`:**
In `(d + 1) * lagBracketSlope (d + 1) - d * lagBracketSlope d`, the prime-power jump `Λ(d + 1)`
cancels identically between `-ψ(d + 1)` and `(d + 1) * mertensSum (d + 1)`, leaving the
Mertens deviation `mertensSum d - log d + γ` minus `(d + 1) * log((d + 1) / d) - 1`. -/
theorem mul_lagBracketSlope_succ_sub {d : ℕ} (hd : 1 ≤ d) :
    ((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d =
      (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) -
        (((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / (d : ℝ)) - 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) =
      (((d : ℝ) + 1) - Chebyshev.psi ((d : ℝ) + 1)) +
        ((d : ℝ) + 1) * (mertensSum (d + 1) - Real.log ((d : ℝ) + 1) +
          Real.eulerMascheroniConstant) := by
    unfold lagBracketSlope lagBracket
    push_cast
    field_simp
    ring
  have h2 : (d : ℝ) * lagBracketSlope d =
      ((d : ℝ) - Chebyshev.psi (d : ℝ)) +
        (d : ℝ) * (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) := by
    unfold lagBracketSlope lagBracket
    field_simp [hd0.ne']
    ring
  have hψ : Chebyshev.psi ((d : ℝ) + 1) = Chebyshev.psi (d : ℝ) + vonMangoldt (d + 1) := by
    have h := psi_sub_psi_eq (Nat.le_succ d)
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
    push_cast at h
    linarith
  have hM : mertensSum (d + 1) = mertensSum d + vonMangoldt (d + 1) / ((d : ℝ) + 1) := by
    have h := mertensSum_sub_eq (Nat.le_succ d)
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
    push_cast at h
    linarith
  have hlog : Real.log (((d : ℝ) + 1) / (d : ℝ)) = Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) :=
    Real.log_div (by positivity) hd0.ne'
  rw [h1, h2, hψ, hM, hlog]
  field_simp
  ring

/-- The unit step of `d * lagBracketSlope d` matches `mertensSum d - log d + γ` within `1 / d`. -/
theorem abs_mul_lagBracketSlope_succ_sub_mertensDeviation_le {d : ℕ} (hd : 1 ≤ d) :
    |(((d + 1 : ℕ) : ℝ) * lagBracketSlope (d + 1) - (d : ℝ) * lagBracketSlope d) -
        (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant)| ≤
      1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mul_lagBracketSlope_succ_sub hd, sub_sub_cancel_left, abs_neg]
  have hup : Real.log (((d : ℝ) + 1) / d) ≤ 1 / (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((d : ℝ) + 1) / d by positivity)
    have e : ((d : ℝ) + 1) / d - 1 = 1 / (d : ℝ) := by field_simp; ring
    linarith
  have hlow : 1 / ((d : ℝ) + 1) ≤ Real.log (((d : ℝ) + 1) / d) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d : ℝ) / (d + 1) by positivity)
    have e1 : (d : ℝ) / (d + 1) - 1 = -(1 / ((d : ℝ) + 1)) := by field_simp; ring
    have e2 : Real.log ((d : ℝ) / (d + 1)) = -Real.log (((d : ℝ) + 1) / d) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have hnonneg : 0 ≤ ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / (d : ℝ)) - 1 := by
    have hmul := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
    have heq : ((d : ℝ) + 1) * (1 / ((d : ℝ) + 1)) = 1 := by field_simp
    linarith
  have hle : ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / (d : ℝ)) - 1 ≤ 1 / (d : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hup (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
    have heq : ((d : ℝ) + 1) * (1 / (d : ℝ)) - 1 = 1 / (d : ℝ) := by field_simp; ring
    linarith
  rw [abs_of_nonneg hnonneg]
  exact hle

end

end GaloisForLFunctions.RHTower
