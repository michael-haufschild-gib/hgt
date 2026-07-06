/-
Sign changes of the completed carrier from first-moment cancellation.

A real function whose first moment over a segment is strictly smaller in absolute value than its
absolute first moment `∫ |F|` cannot keep one sign on the segment, so a two-point sign bracket
exists.  Feeding a second-moment floor through a sup bound via `∫ F² ≤ M·∫ |F|` produces the
bracket from three scalars: a second-moment supply, a line sup, and a first-moment cancellation
bound.  Applied to `u ↦ (completedGN N (linePt u)).re` — the completed carrier is real on the
critical line — this replaces the pointwise two-height sign face of the pinning gate by integral
data on a known segment, so every face of the resulting Riemann-hypothesis endpoint is an
integral, sup, or scalar inequality over explicitly named segments and circles.
-/
import GaloisForLFunctions.RHTower.CarrierLineSup
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.EnvelopeDerivBound
import GaloisForLFunctions.RHTower.DpolyBallFloor

open Complex Metric

namespace RHTower

/-- **Sign bracket from first-moment cancellation.**  If `|∫ F| < ∫ |F|` on `[α, β]`, then `F`
cannot have one strict sign throughout, so some ordered pair of points has `F t₁ · F t₂ ≤ 0`.
No continuity or integrability is needed: a strict sign forces `|F| = F` (or `|F| = −F`)
pointwise, collapsing the strict inequality to `|∫ F| < |∫ F|`. -/
theorem exists_sign_bracket_of_abs_integral_lt {F : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hlt : |∫ u in α..β, F u| < ∫ u in α..β, |F u|) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧ F t₁ * F t₂ ≤ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hαmem : α ∈ Set.Icc α β := ⟨le_rfl, hαβ⟩
  have hself : 0 < F α * F α := hcon α α hαmem hαmem le_rfl
  rcases lt_trichotomy (F α) 0 with hneg | hzero | hpos
  · have hall : ∀ t ∈ Set.Icc α β, F t < 0 := by
      intro t ht
      by_contra hnt
      rw [not_lt] at hnt
      have h1 := hcon α t hαmem ht ht.1
      have h2 : F α * F t ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hneg.le, hnt⟩)
      linarith
    have hEq : Set.EqOn (fun u => |F u|) (fun u => -F u) (Set.uIcc α β) := by
      rw [Set.uIcc_of_le hαβ]
      intro t ht
      exact abs_of_neg (hall t ht)
    have hint : (∫ u in α..β, |F u|) = -∫ u in α..β, F u := by
      rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_neg]
    have h3 := neg_abs_le (∫ u in α..β, F u)
    rw [hint] at hlt
    linarith
  · rw [hzero, mul_zero] at hself
    exact lt_irrefl 0 hself
  · have hall : ∀ t ∈ Set.Icc α β, 0 < F t := by
      intro t ht
      by_contra hnt
      rw [not_lt] at hnt
      have h1 := hcon α t hαmem ht ht.1
      have h2 : F α * F t ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hpos.le, hnt⟩)
      linarith
    have hEq : Set.EqOn (fun u => |F u|) F (Set.uIcc α β) := by
      rw [Set.uIcc_of_le hαβ]
      intro t ht
      exact abs_of_pos (hall t ht)
    have hint : (∫ u in α..β, |F u|) = ∫ u in α..β, F u :=
      intervalIntegral.integral_congr hEq
    have h3 := le_abs_self (∫ u in α..β, F u)
    rw [hint] at hlt
    linarith

/-- **Sign bracket from a moment gap.**  A second-moment supply `S ≤ ∫ F²`, a sup bound
`|F| ≤ M_line`, and the first-moment cancellation `M_line·|∫ F| < S` force a sign bracket:
`∫ F² ≤ M_line·∫ |F|` converts the supply into an absolute-moment floor exceeding `|∫ F|`. -/
theorem exists_sign_bracket_of_moment_gap {F : ℝ → ℝ} {α β S M_line : ℝ} (hαβ : α ≤ β)
    (hFc : ContinuousOn F (Set.Icc α β)) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, (F u) ^ 2)
    (hsup : ∀ u ∈ Set.Icc α β, |F u| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, F u| < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧ F t₁ * F t₂ ≤ 0 := by
  have hFc' : ContinuousOn F (Set.uIcc α β) := by
    rw [Set.uIcc_of_le hαβ]
    exact hFc
  have hM0 : 0 < M_line := by
    by_contra hM0
    rw [not_lt] at hM0
    have hEq : Set.EqOn (fun u => (F u) ^ 2) (fun _ => (0 : ℝ)) (Set.uIcc α β) := by
      rw [Set.uIcc_of_le hαβ]
      intro t ht
      have h1 := hsup t ht
      have h2 : F t = 0 :=
        abs_eq_zero.mp (le_antisymm (le_trans h1 hM0) (abs_nonneg _))
      simp [h2]
    have hzero : (∫ u in α..β, (F u) ^ 2) = 0 := by
      rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
    rw [hzero] at hsupply
    linarith
  have hpt : ∀ u ∈ Set.Icc α β, (F u) ^ 2 ≤ M_line * |F u| := by
    intro u hu
    have h1 := hsup u hu
    have h2 : |F u| * |F u| ≤ M_line * |F u| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have h3 : (F u) ^ 2 = |F u| * |F u| := by
      rw [pow_two, abs_mul_abs_self]
    rw [h3]
    exact h2
  have hint1 : IntervalIntegrable (fun u => (F u) ^ 2) MeasureTheory.volume α β :=
    (hFc'.pow 2).intervalIntegrable
  have hint2 : IntervalIntegrable (fun u => M_line * |F u|) MeasureTheory.volume α β :=
    (continuousOn_const.mul hFc'.abs).intervalIntegrable
  have hmono : (∫ u in α..β, (F u) ^ 2) ≤ ∫ u in α..β, M_line * |F u| :=
    intervalIntegral.integral_mono_on hαβ hint1 hint2 hpt
  have hconst : (∫ u in α..β, M_line * |F u|) = M_line * ∫ u in α..β, |F u| :=
    intervalIntegral.integral_const_mul M_line _
  have hchain : M_line * |∫ u in α..β, F u| < M_line * ∫ u in α..β, |F u| := by
    rw [← hconst]
    exact lt_of_lt_of_le hfm (le_trans hsupply hmono)
  exact exists_sign_bracket_of_abs_integral_lt hαβ
    (lt_of_mul_lt_mul_left hchain hM0.le)

/-- The completed carrier restricted to the critical line is continuous in the height. -/
theorem continuous_completedGN_line (N : ℕ) :
    Continuous fun u : ℝ => completedGN N (linePt u) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hline : Continuous fun u : ℝ => linePt u := by
    unfold linePt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact ((completedGN_analyticAt (N := N)
    (by rw [linePt_re]; norm_num) (by rw [linePt_re]; norm_num)).continuousAt).comp
    hline.continuousAt

/-- **Sign bracket for the completed carrier from segment moment data.**  The real part of the
completed carrier along the critical line changes sign in `[α, β]` as soon as its second moment
holds a floor `S`, its sup is at most `M_line`, and its first moment cancels below `S / M_line`.
Since the completed carrier is real on the line, this bracket is exactly the sign face of the
window-pinning gates. -/
theorem exists_completedGN_sign_bracket_of_moments (N : ℕ) {α β S M_line : ℝ}
    (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hsup : ∀ u ∈ Set.Icc α β, |(completedGN N (linePt u)).re| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, (completedGN N (linePt u)).re| < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  have hc : Continuous fun u : ℝ => (completedGN N (linePt u)).re :=
    Complex.continuous_re.comp (continuous_completedGN_line N)
  exact exists_sign_bracket_of_moment_gap hαβ hc.continuousOn hS hsupply hsup hfm

/-- **Sign bracket from scalar first-moment budget.**  On a positive segment, the closed-form
line sup `completedGNLineSupBudget N β` and the named first-moment budget together replace the
raw cancellation hypothesis `M_line * |∫ Re Φ̃_N| < S`. -/
theorem exists_completedGN_sign_bracket_of_firstMomentBudget (N : ℕ) (hN : 1 ≤ N)
    {α β S M₀ M₁ Cmain : ℝ} (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc α β, ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hCmain : ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (1 - linePt u)‖ ≤ Cmain)
    (hbudget : completedGNLineSupBudget N β *
        completedGNFirstMomentBudget N (β - α) M₀ M₁ Cmain < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  have hsup : ∀ u ∈ Set.Icc α β,
      |(completedGN N (linePt u)).re| ≤ completedGNLineSupBudget N β := by
    intro u hu
    exact abs_re_completedGN_line_le_segment_budget N hα0 hu
  have hfirst :=
    abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups
      hN hαβ hM₀ hM₀r hM₁ hM₁r hCmain
  have hline0 : 0 ≤ completedGNLineSupBudget N β :=
    completedGNLineSupBudget_nonneg N β
  have hfm : completedGNLineSupBudget N β *
        |∫ u in α..β, (completedGN N (linePt u)).re| < S :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfirst hline0) hbudget
  exact exists_completedGN_sign_bracket_of_moments N hαβ hS hsupply hsup hfm

/-- **Sign bracket with closed resonance and envelope budgets.**  The only remaining local
first-moment data is the derivative-envelope sup `M₁`; the envelope sup and resonance moment are
the closed-form scalar budgets from `ResonanceClosedForm`. -/
theorem exists_completedGN_sign_bracket_of_resonanceBudget (N : ℕ) (hN : 1 ≤ N)
    {α β S M₁ : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hbudget : completedGNLineSupBudget N β *
        completedGNFirstMomentBudget N (β - α) (archEnvelopeLineBudget β) M₁
          (resonanceMomentClosedFormBudget α β) < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  exact exists_completedGN_sign_bracket_of_firstMomentBudget N hN hα.le hαβ hS hsupply
    (fun u hu => norm_archFactor_line_le_segment_budget hα.le hu)
    (fun u hu => norm_archFactor_reflected_line_le_segment_budget hα.le hu)
    hM₁ hM₁r (resonance_moment_le_closedFormBudget hα hαβ hwind) hbudget

/-- Closed resonance sign bracket with only one derivative-envelope sup: the reflected derivative
sup is identical by conjugation. -/
theorem exists_completedGN_sign_bracket_of_resonanceBudget_oneDerivSup
    (N : ℕ) (hN : 1 ≤ N) {α β S M₁ : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hbudget : completedGNLineSupBudget N β *
        completedGNFirstMomentBudget N (β - α) (archEnvelopeLineBudget β) M₁
          (resonanceMomentClosedFormBudget α β) < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  exact exists_completedGN_sign_bracket_of_resonanceBudget N hN hα hαβ hwind hS hsupply
    hM₁ (fun u hu => by
      rw [norm_archFactorDeriv_reflected_line_eq u]
      exact hM₁ u hu) hbudget

/-- **Closed first-moment bound for the completed carrier.**  On a positive segment above the
winding threshold, the first moment is bounded by the named finite scalar built from the closed
envelope, derivative, and resonance budgets. -/
theorem abs_integral_re_completedGN_line_le_closedFirstMomentBudget
    (N : ℕ) (hN : 1 ≤ N) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      completedGNFirstMomentBudget N (β - α) (archEnvelopeLineBudget β)
        (archDerivSegmentBudget α β) (resonanceMomentClosedFormBudget α β) := by
  exact abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups
    hN hαβ
    (fun u hu => norm_archFactor_line_le_segment_budget hα.le hu)
    (fun u hu => norm_archFactor_reflected_line_le_segment_budget hα.le hu)
    (fun u hu => norm_archFactorDeriv_line_le_segmentBudget hα hu)
    (fun u hu => by
      rw [norm_archFactorDeriv_reflected_line_eq u]
      exact norm_archFactorDeriv_line_le_segmentBudget hα hu)
    (resonance_moment_le_closedFormBudget hα hαβ hwind)

/-- Relaxed closed first-moment bound: once the closed scalar inputs are available, any larger
length, envelope, derivative, and resonance scalars also bound the completed carrier's first
moment. -/
theorem abs_integral_re_completedGN_line_le_closedFirstMomentBudget_mono
    (N : ℕ) (hN : 1 ≤ N) {α β L M₀ M₁ Cmain : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hL : β - α ≤ L)
    (hM₀ : archEnvelopeLineBudget β ≤ M₀)
    (hM₁ : archDerivSegmentBudget α β ≤ M₁)
    (hCmain : resonanceMomentClosedFormBudget α β ≤ Cmain) :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      completedGNFirstMomentBudget N L M₀ M₁ Cmain := by
  exact abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups_mono
    hN hαβ
    (fun u hu => norm_archFactor_line_le_segment_budget hα.le hu)
    (fun u hu => norm_archFactor_reflected_line_le_segment_budget hα.le hu)
    (fun u hu => norm_archFactorDeriv_line_le_segmentBudget hα hu)
    (fun u hu => by
      rw [norm_archFactorDeriv_reflected_line_eq u]
      exact norm_archFactorDeriv_line_le_segmentBudget hα hu)
    (resonance_moment_le_closedFormBudget hα hαβ hwind)
    hL hM₀ hM₁ hCmain

/-- Closed first-moment budgets are nonnegative on every segment where the closed bound is valid.
This records the scalar-budget invariant needed when comparing line-sup prefactors. -/
theorem completedGNFirstMomentBudget_closed_nonneg
    (N : ℕ) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) :
    0 ≤ completedGNFirstMomentBudget N (β - α) (archEnvelopeLineBudget β)
      (archDerivSegmentBudget α β) (resonanceMomentClosedFormBudget α β) := by
  exact completedGNFirstMomentBudget_nonneg N (by linarith)
    (archEnvelopeLineBudget_nonneg β)
    (archDerivSegmentBudget_nonneg hα hαβ)
    (resonanceMomentClosedFormBudget_nonneg hα hαβ hwind)

/-- Local sign bracket from relaxed closed first-moment budgets.  The closed analytic estimates
prove the sharp scalar inputs, and monotonicity allows the sign face to consume any coarser scalar
budget supplied by the certificate. -/
theorem exists_completedGN_sign_bracket_of_closedFirstMomentBudget_mono
    (N : ℕ) (hN : 1 ≤ N) {α β S L M₀ M₁ Cmain : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hL : β - α ≤ L)
    (hM₀ : archEnvelopeLineBudget β ≤ M₀)
    (hM₁ : archDerivSegmentBudget α β ≤ M₁)
    (hCmain : resonanceMomentClosedFormBudget α β ≤ Cmain)
    (hbudget : completedGNLineSupBudget N β *
        completedGNFirstMomentBudget N L M₀ M₁ Cmain < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  have hsup : ∀ u ∈ Set.Icc α β,
      |(completedGN N (linePt u)).re| ≤ completedGNLineSupBudget N β := by
    intro u hu
    exact abs_re_completedGN_line_le_segment_budget N hα.le hu
  have hfirst :=
    abs_integral_re_completedGN_line_le_closedFirstMomentBudget_mono
      N hN hα hαβ hwind hL hM₀ hM₁ hCmain
  have hline0 : 0 ≤ completedGNLineSupBudget N β :=
    completedGNLineSupBudget_nonneg N β
  have hfm : completedGNLineSupBudget N β *
        |∫ u in α..β, (completedGN N (linePt u)).re| < S :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfirst hline0) hbudget
  exact exists_completedGN_sign_bracket_of_moments N hαβ hS hsupply hsup hfm

/-- **Local sign bracket from fully closed first-moment budgets.**  The first-moment side is now
entirely scalar: closed line sup, closed envelope sup, closed derivative-segment budget, and closed
resonance budget.  The only remaining analytic input on the segment is the completed-carrier
second-moment floor `S`. -/
theorem exists_completedGN_sign_bracket_of_closedFirstMomentBudget
    (N : ℕ) (hN : 1 ≤ N) {α β S : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hwind : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, ((completedGN N (linePt u)).re) ^ 2)
    (hbudget : completedGNLineSupBudget N β *
        completedGNFirstMomentBudget N (β - α) (archEnvelopeLineBudget β)
          (archDerivSegmentBudget α β) (resonanceMomentClosedFormBudget α β) < S) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc α β ∧ t₂ ∈ Set.Icc α β ∧ t₁ ≤ t₂ ∧
      (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0 := by
  exact exists_completedGN_sign_bracket_of_closedFirstMomentBudget_mono
    N hN hα hαβ hwind hS hsupply le_rfl le_rfl le_rfl le_rfl hbudget

/-- **Window certificate from Hardy zero brackets and the EM seam.**  For every candidate
right-half zero in the height window, disjoint Hardy moment packets produce closed xi sign
brackets; the EM remainder, finite `emCarrier`/`gN` closeness, and LOW floor transfer the finite
count budget through the seam.  The resulting on-line ball cover is consumed by the window
certificate layer. -/
theorem windowCertificate_of_emCarrier_hardy_zero_brackets {k : ℕ} {T : ℝ}
    (hcert : ∀ ρ ∈ boxZeros T,
      ∃ N M : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R ε₁ δ : ℝ, ∃ s : ℕ,
      ∃ lo hi : ℕ → ℝ,
        ρ ∈ ball a R ∧
        1 ≤ M ∧
        0 ≤ r₀ ∧ r₀ < R ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ) ∧
        (∀ i, i < s → lo i ≤ hi i) ∧
        (∀ i j, i < j → j < s → hi i < lo j) ∧
        (∀ i, i < s →
          ∃ S M_line : ℝ,
            0 < S ∧
            S ≤ ∫ u in lo i..hi i, ((xi (linePt u)).re) ^ 2 ∧
            (∀ u ∈ Set.Icc (lo i) (hi i), |(xi (linePt u)).re| ≤ M_line) ∧
            M_line * |∫ u in lo i..hi i, (xi (linePt u)).re| < S) ∧
        (∀ i, i < s → ∀ u : ℝ, lo i ≤ u → u ≤ hi i → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    WindowCertificate k T := by
  refine windowCertificate_of_ball_online_cover ?_
  intro ρ hρ
  rcases hcert ρ hρ with
    ⟨N, M, t₁, t₂, m₁, m₂, H, H', a, r₀, R, ε₁, δ, s, lo, hi,
      hρball, hM, h0, hrR, hm₁, hcl₁, hρ₁, hρ₂, hHan, hH0, hHpan, hHp0,
      hfact₁, hfact₂, hstripC, hE, hclose, hF, hord, hsep, hhardy, hseg,
      hcount₂⟩
  have hlineCont : Continuous fun u : ℝ => (xi (linePt u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  have hbrackets : ∀ i, ∃ u v : ℝ, i < s →
      u ∈ Set.Icc (lo i) (hi i) ∧ v ∈ Set.Icc (lo i) (hi i) ∧ u ≤ v ∧
        (xi (linePt u)).re * (xi (linePt v)).re ≤ 0 := by
    intro i
    by_cases hi_lt : i < s
    · rcases hhardy i hi_lt with ⟨S, M_line, hS, hsupply, hsup, hfm⟩
      have hcont : ContinuousOn (fun u : ℝ => (xi (linePt u)).re)
          (Set.Icc (lo i) (hi i)) :=
        hlineCont.continuousOn
      obtain ⟨u, v, hu, hv, huv, hprod⟩ :=
        exists_sign_bracket_of_moment_gap (F := fun u : ℝ => (xi (linePt u)).re)
          (hord i hi_lt) hcont hS hsupply hsup hfm
      exact ⟨u, v, fun _ => ⟨hu, hv, huv, hprod⟩⟩
    · exact ⟨lo i, hi i, fun h => absurd h hi_lt⟩
  choose u v huv using hbrackets
  have hord' : ∀ i, i < s → u i ≤ v i := by
    intro i hi_lt
    exact (huv i hi_lt).2.2.1
  have hsep' : ∀ i j, i < j → j < s → v i < u j := by
    intro i j hij hjs
    have hi_lt : i < s := lt_trans hij hjs
    have hvi : v i ≤ hi i := (huv i hi_lt).2.1.2
    have huj : lo j ≤ u j := (huv j hjs).1.1
    have hgap := hsep i j hij hjs
    linarith
  have hsign' : ∀ i, i < s →
      (xi (linePoint (u i))).re * (xi (linePoint (v i))).re ≤ 0 := by
    intro i hi_lt
    exact (huv i hi_lt).2.2.2
  have hseg' : ∀ i, i < s → ∀ x : ℝ, u i ≤ x → x ≤ v i → linePoint x ∈ ball a R := by
    intro i hi_lt x hux hxv
    have hui : lo i ≤ u i := (huv i hi_lt).1.1
    have hvi : v i ≤ hi i := (huv i hi_lt).2.1.2
    exact hseg i hi_lt x (le_trans hui hux) (le_trans hxv hvi)
  refine ⟨a, R, hρball, ?_⟩
  exact xi_window_online_of_emCarrier_close_floor_zero_brackets
    (N := N) (M := M) hM h0 hrR hm₁ hcl₁ hρ₁ hρ₂ hHan hH0 hHpan hHp0
    hfact₁ hfact₂ hstripC hE hclose hF hord' hsep' hsign' hseg' hcount₂

/-- Window-level integral ledger for the strongest Dpoly/Hardy outer-power endpoint.
The short completed-carrier sign face is recorded as moment data rather than as an explicit
point-pair bracket; the producer below derives the bracket before handing off to the Dpoly
window package. -/
def IntegralLedgerOuterPowerWindowData (T0 : ℝ) : Prop :=
  ∀ ρ ∈ boxZeros T0,
    ∃ (N M : ℕ) (δ : ℝ)
      (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ S_b M_line : ℝ),
      1 ≤ M ∧
      0 < U ∧
      0 < rz ∧
      0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
      P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
      rz < R ∧
      (ρ.re - 1 / 2) ^ 2 +
          (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
      0 < T + U - rz ∧ U ≤ 2 * rz ∧
      0 < S_b ∧
      S_b ≤ (∫ u in (T + U - rz)..(T + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
      (∀ u ∈ Set.Icc (T + U - rz) (T + rz),
        |(completedGN N (linePt u)).re| ≤ M_line) ∧
      M_line * |∫ u in (T + U - rz)..(T + rz), (completedGN N (linePt u)).re| < S_b ∧
      0 < m_J ∧
      m_J ^ 2 * U +
        (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
        4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
          - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|) ∧
      1 ≤ M_J ∧
      (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
      Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
      m_J / rz < M_J / (rJ - rz) ∧
      (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
      0 < a₀ ∧
      (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
        ‖completedGN N z‖ ≤ M_G) ∧
      max ((6 * R * M_G) / (P ^ 2 * a₀))
          ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
            (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
        (m_J / rz) *
          ((m_J / rz) / (M_J / (rJ - rz))) ^
            (2 * (R + rz) / (rJ - (R + rz))) ∧
      (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
        ‖emCarrier M z - gN N z‖ ≤ δ)

/-- Window-level integral ledgers produce the `WindowLinePackage` interface.  The moment ledger
discharges the explicit completed-carrier sign bracket consumed by the strongest Dpoly/Hardy
outer-power package. -/
theorem windowLinePackage_of_integral_ledger_outer_power_windowData {T0 : ℝ}
    (hwin : IntegralLedgerOuterPowerWindowData T0) :
    WindowLinePackage T0 := by
  refine windowLinePackage_of_secondMoment_orthogonal_saving_outer_power_endpoint_target ?_
  intro ρ hρ
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hbrpos, hUrz, hSb, hsupply, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩ := hwin ρ hρ
  have hαβ : T + U - rz ≤ T + rz := by linarith
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_completedGN_sign_bracket_of_moments N hαβ hSb hsupply hMline hfm
  exact ⟨N, M, δ, T, U, t₁, t₂, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    hM, hU, lt_of_lt_of_le hbrpos ht₁.1, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12, hrzR, hρquad, ht₁.1, ht₂.2, hmJ0, henergy,
    (by simpa [linePt] using hsign), hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

end RHTower

namespace RHTower

/-- **Riemann Hypothesis from a per-zero integral ledger.**  Every face of the per-zero
certificate is an integral, sup, or scalar inequality over explicitly named segments and circles:
the second-moment/orthogonal-energy budget supplies the carrier anchor somewhere in the window,
the short-segment moment triple (second-moment floor `S_b`, line sup `M_line`, first-moment
cancellation) forces the sign bracket of the real-valued completed carrier, and the remaining
faces are the Jensen count, minimum-modulus engine, and maximum-principle circle data of the
scalar pinning gate.  No face references a height that is not explicitly named by the window. -/
theorem riemannHypothesis_of_integral_ledger_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ S_b M_line : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T + U - rz ∧ U ≤ 2 * rz ∧
        0 < S_b ∧
        S_b ≤ (∫ u in (T + U - rz)..(T + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ u ∈ Set.Icc (T + U - rz) (T + rz),
          |(completedGN N (linePt u)).re| ≤ M_line) ∧
        M_line * |∫ u in (T + U - rz)..(T + rz), (completedGN N (linePt u)).re| < S_b ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hbrpos, hUrz, hSb, hsupply, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  have hαβ : T + U - rz ≤ T + rz := by linarith
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_completedGN_sign_bracket_of_moments N hαβ hSb hsupply hMline hfm
  exact ⟨N, M, δ, T, U, t₁, t₂, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    hM, hU, lt_of_lt_of_le hbrpos ht₁.1, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12, hrzR, hρquad, ht₁.1, ht₂.2, hmJ0, henergy,
    (by simpa [linePt] using hsign), hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

end RHTower

namespace RHTower

/-- **Decoupled integral ledger with center-dependent short moment and line-sup data.**  The
long-window anchor chooses one height `τ`; the sign bracket uses only the local second-moment
floor and local line sup at that selected height.  Thus neither short sign-face scalar needs to be
uniform across the whole anchor window. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_local_moment_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b M_line : ℝ → ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ u ∈ Set.Icc (τ - rz) (τ + rz),
          |(completedGN N (linePt u)).re| ≤ M_line τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          M_line τ * |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| <
            S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  let ε₁ : ℝ := (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
    (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)
  let Rprime : ℝ := R - rz
  let Rτ : ℝ := max |ρ.im - T| |ρ.im - (T + U)|
  have hR'0 : 0 < Rprime := by
    dsimp [Rprime]
    linarith
  have hR'rz : Rprime + rz ≤ R := by
    dsimp [Rprime]
    linarith
  have hρT : |ρ.im - T| ≤ Rτ := le_max_left _ _
  have hρTU : |ρ.im - (T + U)| ≤ Rτ := le_max_right _ _
  have hρquad' : (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < Rprime ^ 2 := by
    simpa [Rτ, Rprime] using hρquad
  have hR0 : 0 ≤ R := (lt_trans h0 hrR).le
  have hP0 : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hMJ0 : 0 < M_J := lt_of_lt_of_le zero_lt_one hMJ
  have hrzJ : rz < rJ := by linarith
  have hRJ0 : 0 < RJ := by linarith [h0, hrR, hRrzJ, hrJR, hrz0]
  have hε₁0 : 0 ≤ ε₁ := by
    have hden0 : 0 < 1 / 2 - RJ := by linarith
    have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    have hmax_nonneg : 0 ≤ max ‖linePt T‖ ‖linePt (T + U)‖ :=
      le_trans (norm_nonneg (linePt T)) (le_max_left _ _)
    have hlhs_nonneg : 0 ≤ (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
        (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) := by
      exact div_nonneg (mul_nonneg (add_nonneg hmax_nonneg hRJ0.le) hpow_nonneg) hden0.le
    simpa [ε₁] using hlhs_nonneg
  have hδ0 : 0 ≤ δ := by
    have hτT : T ∈ Set.Icc T (T + U) := ⟨le_rfl, by linarith [hU]⟩
    have hsample : linePt T + (RJ : ℂ) ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) RJ := by
      simpa [linePt] using linePt_add_radius_mem_sphere (τ := T) hRJ0.le
    exact le_trans (norm_nonneg (emCarrier M (linePt T + (RJ : ℂ)) -
      gN N (linePt T + (RJ : ℂ)))) (hclose T hτT (linePt T + (RJ : ℂ)) hsample)
  have hεδ : 0 ≤ ε₁ + δ := add_nonneg hε₁0 hδ0
  obtain ⟨τ, hτ, hAnchor⟩ :=
    exists_gN_line_anchor_in_window_of_secondMoment_orthogonal_energy N hU hmJ0.le henergy
  have hαβ : τ - rz ≤ τ + rz := by linarith
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_completedGN_sign_bracket_of_moments N hαβ (hSb τ hτ) (hsupply τ hτ)
      (hMline τ hτ)
      (hfm τ hτ)
  have ht₁0 : 0 < t₁ := by linarith [ht₁.1, hτ.1]
  have hMG_ball := completedGN_norm_le_line_closedBall_of_sphere hRJ0 hRJ12 (hMG τ hτ)
  have hE_ball : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
    intro z hz
    exact em_remainder_norm_le_window_closedBall_of_endpoint_bound
      (M := M) (T := T) (U := U) (RJ := RJ) (ε₁ := ε₁) hM hRJ12
      (by dsimp [ε₁]; exact le_rfl)
      τ hτ z (by simpa [linePt] using hz)
  have hclose_ball :=
    emCarrier_gN_norm_le_line_closedBall_of_sphere hM hRJ0 hRJ12 (hclose τ hτ)
  have ha₀_ball : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖ := by
    intro z hzre hz
    have him : z.im ∈ Set.Icc (T - rz) (T + U + rz) :=
      im_mem_expanded_window_of_mem_line_center_closedBall hτ hz
    have hzline : z = linePt z.im := eq_linePt_of_re_eq_half hzre
    rw [hzline]
    exact ha₀ z.im him
  obtain ⟨hcross, hfl⟩ :=
    canonical_cross_em_budgets_of_outer_power_floor_max
      (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
      (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
      hmJ0 hrz0 hMJ0 hrzJ hengine hP0 ha₀0 h0 hR0 hRrzJ (by
        dsimp [ε₁]
        exact hbudget_outer)
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I,
    t₁, t₂, rz, r₀, R, Rprime, P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁0, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    point_mem_line_center_ball_of_quadratic hR'0
      ((quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad') τ hτ),
    hR'rz, line_center_closedBall_strip hRJ12,
    (fun u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds
      (T := τ) (U := 0) (by linarith [ht₁.1]) (by linarith [ht₂.2])
      ⟨le_rfl, by linarith⟩ hu),
    (by simpa [linePt] using hsign), hmJ0, hAnchor, hMJ,
    (fun z hz => hbound τ hτ z hz),
    hjensen_floor, hengine, ha₀_ball, ha₀0, hMG_ball, hcross,
    hE_ball, hclose_ball, hfl⟩

/-- **Decoupled integral ledger with center-dependent short moment floors.**  The line sup remains
uniform on the expanded anchor window, but the short second-moment floor is local to the selected
height.  This is the constant-line-sup specialization of the local-moment ledger. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_moment_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b : ℝ → ℝ) (M_line : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz),
          |(completedGN N (linePt u)).re| ≤ M_line) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          M_line * |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_moment_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    (fun _ : ℝ => M_line), hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hrzR, hρquad, hTrz, hSb, hsupply,
    (fun τ hτ u hu => hMline u ⟨by linarith [hτ.1, hu.1], by linarith [hτ.2, hu.2]⟩),
    hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩

/-- **Variable-floor decoupled ledger with local closed-form line sup.**  The completed-carrier
line sup is evaluated at the right endpoint of the selected short segment, not at the far endpoint
of the expanded anchor window. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_local_line_sup_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b : ℝ → ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (τ + rz) *
              |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_moment_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  have hMline : ∀ τ ∈ Set.Icc T (T + U), ∀ u ∈ Set.Icc (τ - rz) (τ + rz),
      |(completedGN N (linePt u)).re| ≤ completedGNLineSupBudget N (τ + rz) := by
    intro τ hτ u hu
    have hα0 : 0 ≤ τ - rz := by linarith [hTrz, hτ.1]
    exact abs_re_completedGN_line_le_segment_budget N hα0 hu
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    (fun τ => completedGNLineSupBudget N (τ + rz)), hM, hU, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad, hTrz, hSb, hsupply, hMline, hfm,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩

/-- **Variable-floor decoupled ledger with local closed first-moment budget.**  Both scalar
budgets in the sign face are attached to the selected short segment `[τ-rz, τ+rz]`. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_local_closedFirstMoment_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b : ℝ → ℝ),
        1 ≤ N ∧
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          0 < (Real.log ((τ - rz) / (2 * Real.pi)) -
            (4 / (τ - rz) ^ 2 + Real.pi / (τ - rz))) / 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (τ + rz) *
              completedGNFirstMomentBudget N (2 * rz)
                (archEnvelopeLineBudget (τ + rz))
                (archDerivSegmentBudget (τ - rz) (τ + rz))
                (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) < S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_line_sup_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hN, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hwind, hfirstBudget, hmJ0, henergy, hMJ, hbound,
    hjensen_floor, hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  have hfm : ∀ τ ∈ Set.Icc T (T + U),
      completedGNLineSupBudget N (τ + rz) *
        |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b τ := by
    intro τ hτ
    have hα : 0 < τ - rz := by linarith [hTrz, hτ.1]
    have hαβ : τ - rz ≤ τ + rz := by linarith [hrz0]
    have hlen : (τ + rz) - (τ - rz) = 2 * rz := by ring
    have hfirst' : |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| ≤
        completedGNFirstMomentBudget N (2 * rz)
          (archEnvelopeLineBudget (τ + rz))
          (archDerivSegmentBudget (τ - rz) (τ + rz))
          (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) := by
      simpa [hlen] using
        abs_integral_re_completedGN_line_le_closedFirstMomentBudget
          N hN hα hαβ (hwind τ hτ)
    have hline0 : 0 ≤ completedGNLineSupBudget N (τ + rz) :=
      completedGNLineSupBudget_nonneg N (τ + rz)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfirst' hline0) (hfirstBudget τ hτ)
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

/-- **Riemann Hypothesis from a decoupled integral ledger.**  The anchor window `[T, T+U]` and the
sign-bracket scale `rz` are independent: the second-moment/orthogonal-energy budget selects an
anchor height `τ` anywhere in the window, and the sign bracket of the real-valued completed
carrier is produced *locally* in `[τ − rz, τ + rz]` from the per-height moment triple
(second-moment floor `S_b`, expanded-segment sup `M_line`, first-moment cancellation).  This
constant-floor endpoint is the uniform specialization of the center-dependent ledger. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ S_b M_line : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        0 < S_b ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz),
          |(completedGN N (linePt u)).re| ≤ M_line) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          M_line * |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_moment_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b, M_line,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hMline, hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    (fun _ : ℝ => S_b), M_line, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12, hrzR, hρquad, hTrz, (fun _ _ => hSb), hsupply, hMline,
    hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩

/-- **Variable-floor decoupled ledger with closed-form line sup.**  This variant removes the
`M_line` witness while keeping the short second-moment floor local to the selected center. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_explicit_line_sup_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b : ℝ → ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (T + U + rz) *
              |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_line_sup_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  have hfm_local : ∀ τ ∈ Set.Icc T (T + U),
      completedGNLineSupBudget N (τ + rz) *
        |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b τ := by
    intro τ hτ
    have hbudget_le :
        completedGNLineSupBudget N (τ + rz) ≤ completedGNLineSupBudget N (T + U + rz) := by
      exact completedGNLineSupBudget_mono_nonneg N (by linarith [hTrz, hτ.1, hrz0])
        (by linarith [hτ.2])
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hbudget_le (abs_nonneg _)) (hfm τ hτ)
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hfm_local, hmJ0, henergy, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

/-- **Variable-floor decoupled ledger with closed first-moment budget.**  The sign face is local
second-moment supply plus a scalar first-moment inequality at each possible center. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_variable_closedFirstMoment_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ) (S_b : ℝ → ℝ),
        1 ≤ N ∧
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        (∀ τ ∈ Set.Icc T (T + U), 0 < S_b τ) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b τ ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          0 < (Real.log ((τ - rz) / (2 * Real.pi)) -
            (4 / (τ - rz) ^ 2 + Real.pi / (τ - rz))) / 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (T + U + rz) *
              completedGNFirstMomentBudget N (2 * rz)
                (archEnvelopeLineBudget (τ + rz))
                (archDerivSegmentBudget (τ - rz) (τ + rz))
                (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) < S_b τ) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_closedFirstMoment_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hN, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hwind, hfirstBudget, hmJ0, henergy, hMJ, hbound,
    hjensen_floor, hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  have hfirstBudget_local : ∀ τ ∈ Set.Icc T (T + U),
      completedGNLineSupBudget N (τ + rz) *
          completedGNFirstMomentBudget N (2 * rz)
            (archEnvelopeLineBudget (τ + rz))
            (archDerivSegmentBudget (τ - rz) (τ + rz))
            (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) < S_b τ := by
    intro τ hτ
    have hα : 0 < τ - rz := by linarith [hTrz, hτ.1]
    have hαβ : τ - rz ≤ τ + rz := by linarith [hrz0]
    have hlen : (τ + rz) - (τ - rz) = 2 * rz := by ring
    have hfirst_nonneg :
        0 ≤ completedGNFirstMomentBudget N (2 * rz)
          (archEnvelopeLineBudget (τ + rz))
          (archDerivSegmentBudget (τ - rz) (τ + rz))
          (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) :=
      by
        simpa [hlen] using
          completedGNFirstMomentBudget_closed_nonneg N hα hαβ (hwind τ hτ)
    have hbudget_le :
        completedGNLineSupBudget N (τ + rz) ≤ completedGNLineSupBudget N (T + U + rz) := by
      exact completedGNLineSupBudget_mono_nonneg N (by linarith [hTrz, hτ.1, hrz0])
        (by linarith [hτ.2])
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hbudget_le hfirst_nonneg) (hfirstBudget τ hτ)
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hN, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hwind, hfirstBudget_local, hmJ0, henergy, hMJ, hbound,
    hjensen_floor, hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

/-- **Decoupled integral ledger with closed-form line sup.**  This is the decoupled endpoint with
the `M_line` witness removed: on the expanded positive segment `[T − rz, T + U + rz]`,
`completedGNLineSupBudget N (T + U + rz)` bounds the real completed carrier by the closed-form
line-sup theorem, so the sign face now asks only for the local second moment and the first-moment
cancellation against that explicit scalar. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_explicit_line_sup_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ S_b : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        0 < S_b ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (T + U + rz) *
              |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| < S_b) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_explicit_line_sup_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hfm, hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    (fun _ : ℝ => S_b), hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hrzR, hρquad, hTrz, (fun _ _ => hSb), hsupply, hfm, hmJ0, henergy,
    hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩

/-- **Decoupled integral ledger with closed first-moment budget.**  The sign face is now local
second-moment supply plus a fully scalar first-moment inequality.  The endpoint derives the old
first-moment cancellation internally from `completedGNFirstMomentBudget`; no raw integral
cancellation or free `M_line` witness remains. -/
theorem riemannHypothesis_of_decoupled_integral_ledger_closedFirstMoment_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ S_b : ℝ),
        1 ≤ N ∧
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        0 < S_b ∧
        (∀ τ ∈ Set.Icc T (T + U),
          S_b ≤ ∫ u in (τ - rz)..(τ + rz), ((completedGN N (linePt u)).re) ^ 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          0 < (Real.log ((τ - rz) / (2 * Real.pi)) -
            (4 / (τ - rz) ^ 2 + Real.pi / (τ - rz))) / 2) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (τ + rz) *
              completedGNFirstMomentBudget N (2 * rz)
                (archEnvelopeLineBudget (τ + rz))
                (archDerivSegmentBudget (τ - rz) (τ + rz))
                (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) < S_b) ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_decoupled_integral_ledger_variable_local_closedFirstMoment_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀, S_b,
    hN, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hSb, hsupply, hwind, hfirstBudget, hmJ0, henergy, hMJ, hbound,
    hjensen_floor, hengine, ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  exact ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    (fun _ : ℝ => S_b), hN, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hrzR, hρquad, hTrz, (fun _ _ => hSb), hsupply, hwind, hfirstBudget,
    hmJ0, henergy, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hbudget_outer, hclose⟩

end RHTower
