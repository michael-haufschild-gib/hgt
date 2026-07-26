import GaloisForLFunctions.RHTower.SuzukiJumpKernelLoewnerGap
import GaloisForLFunctions.RHTower.SuzukiShiftSpectralMonotoneRatio

/-!
# Affine two-shift resolvent defect is Krein-signed

Suzuki's two negative shifts suggest extrapolating a zero-shift response by

`(β R_α - α R_β) / (β - α)`.

For the scalar spectral resolvent `R_λ(t) = 1 / (t - λ)`, the difference from `R₀` is not
positive.  It is exactly

`αβ / (t (t - α) (t - β))`.

When `α < β < 0` and both shifts lie below the spectral node, this has the sign of `t`.
Consequently the anti-resolvent orientation gives a positive square on positive spectral
coordinates and a negative square on negative ones.  Bare resolvent algebra therefore supplies a
Krein form, not the Hilbert-space square needed for RH.

The final theorems isolate the missing global-to-local weld.  Against an arbitrary global target,
the sewn gap is the signed local defect plus an exact completion correction.  At every negative
spectral coordinate, positivity forces that correction to dominate the explicit Krein deficit.

Everything here is unconditional algebra.  No RH premise, estimate, or numerical computation is
used.
-/

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Point realization of the shift-resolvent kernel already used by Suzuki source-jet theory. -/
def suzukiPointSpectralResolvent (lambda t : ℝ) : ℝ :=
  suzukiShiftResolventKernel (fun x : ℝ => x) lambda t

/-- Affine extrapolation from two nonzero shifts to shift zero. -/
def suzukiAffineResolventExtrapolation (alpha beta t : ℝ) : ℝ :=
  (beta * suzukiPointSpectralResolvent alpha t -
      alpha * suzukiPointSpectralResolvent beta t) /
    (beta - alpha)

/-- Difference between the true zero-shift scalar resolvent and its two-shift extrapolation. -/
def suzukiAffineResolventKreinDefect (alpha beta t : ℝ) : ℝ :=
  suzukiPointSpectralResolvent 0 t -
    suzukiAffineResolventExtrapolation alpha beta t

/-- Negative-Stieltjes orientation of the scalar spectral resolvent. -/
def suzukiAntiResolventResponse (lambda t : ℝ) : ℝ :=
  -suzukiPointSpectralResolvent lambda t

/-- Bare two-shift anti-resolvent gap against its local zero-shift value. -/
def suzukiAffineAntiResolventGap (alpha beta t : ℝ) : ℝ :=
  (beta * suzukiAntiResolventResponse alpha t -
      alpha * suzukiAntiResolventResponse beta t) /
      (beta - alpha) -
    suzukiAntiResolventResponse 0 t

/-- Difference between the local zero-shift anti-resolvent and an arbitrary global target. -/
def suzukiGlobalLocalWeldCorrection (target t : ℝ) : ℝ :=
  suzukiAntiResolventResponse 0 t - target

/-- Two-shift anti-resolvent gap measured directly against an arbitrary global target. -/
def suzukiAffineAntiResolventTargetGap
    (alpha beta t target : ℝ) : ℝ :=
  (beta * suzukiAntiResolventResponse alpha t -
      alpha * suzukiAntiResolventResponse beta t) /
      (beta - alpha) - target

/-- Exact affine resolvent identity.  Its right side is the scalar Krein weight. -/
theorem suzukiAffineResolventKreinDefect_eq
    {alpha beta t : ℝ} (hab : alpha ≠ beta) (ht : t ≠ 0)
    (hta : t ≠ alpha) (htb : t ≠ beta) :
    suzukiAffineResolventKreinDefect alpha beta t =
      alpha * beta / (t * (t - alpha) * (t - beta)) := by
  simp only [suzukiAffineResolventKreinDefect,
    suzukiAffineResolventExtrapolation, suzukiPointSpectralResolvent,
    suzukiShiftResolventKernel]
  have hd : beta - alpha ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hd, ht, sub_ne_zero.mpr hta, sub_ne_zero.mpr htb]
  ring

/-- Ordinary resolvent orientation has the opposite of the Krein defect. -/
theorem suzukiAffineResolventGap_eq_neg_kreinDefect
    (alpha beta t : ℝ) :
    suzukiAffineResolventExtrapolation alpha beta t -
        suzukiPointSpectralResolvent 0 t =
      -suzukiAffineResolventKreinDefect alpha beta t := by
  simp only [suzukiAffineResolventKreinDefect]
  ring

/-- Anti-resolvent orientation exposes exactly the Krein defect. -/
theorem suzukiAffineAntiResolventGap_eq_kreinDefect
    (alpha beta t : ℝ) :
    suzukiAffineAntiResolventGap alpha beta t =
      suzukiAffineResolventKreinDefect alpha beta t := by
  simp only [suzukiAffineAntiResolventGap, suzukiAntiResolventResponse,
    suzukiAffineResolventKreinDefect, suzukiAffineResolventExtrapolation]
  ring

/-- Below-spectrum negative shifts make the defect positive exactly on positive spectral nodes. -/
theorem suzukiAffineResolventKreinDefect_pos_iff
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (ht : t ≠ 0) :
    0 < suzukiAffineResolventKreinDefect alpha beta t ↔ 0 < t := by
  have ha0 : alpha < 0 := lt_trans hab hb0
  have hp : 0 < alpha * beta := mul_pos_of_neg_of_neg ha0 hb0
  have hta : 0 < t - alpha := by linarith
  have htb : 0 < t - beta := by linarith
  have hs : 0 < (t - alpha) * (t - beta) := mul_pos hta htb
  rw [suzukiAffineResolventKreinDefect_eq (ne_of_lt hab) ht
    (ne_of_gt (lt_trans hab hbt)) (ne_of_gt hbt)]
  rw [mul_assoc]
  constructor
  · intro h
    by_contra hn
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hn) ht
    have hdneg : t * ((t - alpha) * (t - beta)) < 0 :=
      mul_neg_of_neg_of_pos htneg hs
    have : alpha * beta / (t * ((t - alpha) * (t - beta))) < 0 :=
      div_neg_of_pos_of_neg hp hdneg
    linarith
  · intro htpos
    exact div_pos hp (mul_pos htpos hs)

/-- Below-spectrum negative shifts make the defect negative exactly on negative spectral nodes. -/
theorem suzukiAffineResolventKreinDefect_neg_iff
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (ht : t ≠ 0) :
    suzukiAffineResolventKreinDefect alpha beta t < 0 ↔ t < 0 := by
  have ha0 : alpha < 0 := lt_trans hab hb0
  have hp : 0 < alpha * beta := mul_pos_of_neg_of_neg ha0 hb0
  have hta : 0 < t - alpha := by linarith
  have htb : 0 < t - beta := by linarith
  have hs : 0 < (t - alpha) * (t - beta) := mul_pos hta htb
  rw [suzukiAffineResolventKreinDefect_eq (ne_of_lt hab) ht
    (ne_of_gt (lt_trans hab hbt)) (ne_of_gt hbt)]
  rw [mul_assoc]
  constructor
  · intro h
    by_contra hn
    have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm ht)
    have : 0 < alpha * beta / (t * ((t - alpha) * (t - beta))) :=
      div_pos hp (mul_pos htpos hs)
    linarith
  · intro htneg
    exact div_neg_of_pos_of_neg hp (mul_neg_of_neg_of_pos htneg hs)

/-- Exact global/local decomposition: the actual target gap is signed local resolvent defect plus
the correction welding the local zero-shift model to the global target. -/
theorem suzukiAffineAntiResolventTargetGap_decomposition
    (alpha beta t target : ℝ) :
    suzukiAffineAntiResolventTargetGap alpha beta t target =
      suzukiAffineResolventKreinDefect alpha beta t +
        suzukiGlobalLocalWeldCorrection target t := by
  simp only [suzukiAffineAntiResolventTargetGap,
    suzukiGlobalLocalWeldCorrection]
  rw [← suzukiAffineAntiResolventGap_eq_kreinDefect]
  simp only [suzukiAffineAntiResolventGap]
  ring

/-- Sharp compensation boundary.  Positivity against the global target holds exactly when the
global/local weld pays the negative of the local Krein defect. -/
theorem suzukiAffineAntiResolventTargetGap_nonneg_iff
    (alpha beta t target : ℝ) :
    0 ≤ suzukiAffineAntiResolventTargetGap alpha beta t target ↔
      -suzukiAffineResolventKreinDefect alpha beta t ≤
        suzukiGlobalLocalWeldCorrection target t := by
  rw [suzukiAffineAntiResolventTargetGap_decomposition]
  constructor <;> intro h <;> linarith

/-- A negative spectral coordinate creates a strictly positive compensation debt. -/
theorem suzukiNegativeSpectralNode_compensationDeficit_pos
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0) :
    0 < -suzukiAffineResolventKreinDefect alpha beta t := by
  have hdefneg :=
    (suzukiAffineResolventKreinDefect_neg_iff hab hb0 hbt
      (ne_of_lt htneg)).2 htneg
  linarith

/-- On a negative spectral coordinate, nonnegativity of the global target gap forces a strictly
positive global/local correction. -/
theorem suzukiNegativeSpectralNode_forces_weldCorrection_pos
    {alpha beta t target : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0)
    (hgap : 0 ≤ suzukiAffineAntiResolventTargetGap alpha beta t target) :
    0 < suzukiGlobalLocalWeldCorrection target t := by
  have hdebt :=
    suzukiNegativeSpectralNode_compensationDeficit_pos hab hb0 hbt htneg
  have hdominates :=
    (suzukiAffineAntiResolventTargetGap_nonneg_iff alpha beta t target).1 hgap
  linarith

/-- Bare anti-resolvent sewing cannot be a nonnegative square on a negative spectral node. -/
theorem suzukiNegativeSpectralNode_bareAntiResolventGap_not_nonneg
    {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (htneg : t < 0) :
    ¬ 0 ≤ suzukiAffineAntiResolventGap alpha beta t := by
  rw [suzukiAffineAntiResolventGap_eq_kreinDefect]
  have hdefneg :=
    (suzukiAffineResolventKreinDefect_neg_iff hab hb0 hbt
      (ne_of_lt htneg)).2 htneg
  linarith

/-! ## Schur-complement cost of projective holonomy -/

/-- Two-channel model consisting of one positive local channel, one negative Krein channel, a
direct completion on the negative channel, and their projective coupling. -/
def suzukiTwoChannelKreinCompletionForm
    (positiveBlock coupling directCompletion debt x y : ℝ) : ℝ :=
  positiveBlock * x ^ 2 + 2 * coupling * x * y +
    (directCompletion - debt) * y ^ 2

/-- Exact completed-square form of the two-channel weld. -/
theorem suzukiTwoChannelKreinCompletionForm_eq_completedSquare
    {positiveBlock coupling directCompletion debt x y : ℝ}
    (hpositiveBlock : positiveBlock ≠ 0) :
    suzukiTwoChannelKreinCompletionForm
        positiveBlock coupling directCompletion debt x y =
      positiveBlock * (x + coupling / positiveBlock * y) ^ 2 +
        (directCompletion - debt - coupling ^ 2 / positiveBlock) * y ^ 2 := by
  simp only [suzukiTwoChannelKreinCompletionForm]
  field_simp [hpositiveBlock]
  ring

/-- **Sharp Schur weld law.**  Positivity on both channels is equivalent to paying not only the
negative spectral debt but also the projective coupling tax `coupling² / positiveBlock`. -/
theorem suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt
    {positiveBlock coupling directCompletion debt : ℝ}
    (hpositiveBlock : 0 < positiveBlock) :
    (∀ x y : ℝ, 0 ≤ suzukiTwoChannelKreinCompletionForm
        positiveBlock coupling directCompletion debt x y) ↔
      debt + coupling ^ 2 / positiveBlock ≤ directCompletion := by
  constructor
  · intro h
    have hspecial := h (-coupling / positiveBlock) 1
    rw [suzukiTwoChannelKreinCompletionForm_eq_completedSquare
      (ne_of_gt hpositiveBlock)] at hspecial
    have hcancel : -coupling / positiveBlock + coupling / positiveBlock = 0 := by ring
    rw [show -coupling / positiveBlock + coupling / positiveBlock * 1 = 0 by
      simpa using hcancel] at hspecial
    norm_num at hspecial
    linarith
  · intro h x y
    rw [suzukiTwoChannelKreinCompletionForm_eq_completedSquare
      (ne_of_gt hpositiveBlock)]
    have hfirst :
        0 ≤ positiveBlock * (x + coupling / positiveBlock * y) ^ 2 :=
      mul_nonneg (le_of_lt hpositiveBlock) (sq_nonneg _)
    have hresidual :
        0 ≤ directCompletion - debt - coupling ^ 2 / positiveBlock := by
      linarith
    have hsecond :
        0 ≤ (directCompletion - debt - coupling ^ 2 / positiveBlock) * y ^ 2 :=
      mul_nonneg hresidual (sq_nonneg _)
    linarith

/-- Nonzero holonomy coupling imposes a strictly positive cost beyond diagonal Krein debt. -/
theorem suzukiProjectiveCoupling_schurTax_strict
    {positiveBlock coupling debt : ℝ}
    (hpositiveBlock : 0 < positiveBlock) (hcoupling : coupling ≠ 0) :
    debt < debt + coupling ^ 2 / positiveBlock := by
  have hcouplingSq : 0 < coupling ^ 2 := sq_pos_of_ne_zero hcoupling
  have htax : 0 < coupling ^ 2 / positiveBlock :=
    div_pos hcouplingSq hpositiveBlock
  linarith

/-- At a negative spectral node, the exact resolvent debt is positive and the two-channel
completion threshold is its sum with the Schur holonomy tax. -/
theorem suzukiNegativeSpectralNode_twoChannelCompletionLaw
    {alpha beta t positiveBlock coupling directCompletion : ℝ}
    (hab : alpha < beta) (hb0 : beta < 0) (hbt : beta < t)
    (htneg : t < 0) (hpositiveBlock : 0 < positiveBlock) :
    0 < -suzukiAffineResolventKreinDefect alpha beta t ∧
      ((∀ x y : ℝ, 0 ≤ suzukiTwoChannelKreinCompletionForm
          positiveBlock coupling directCompletion
            (-suzukiAffineResolventKreinDefect alpha beta t) x y) ↔
        -suzukiAffineResolventKreinDefect alpha beta t +
            coupling ^ 2 / positiveBlock ≤ directCompletion) := by
  constructor
  · exact suzukiNegativeSpectralNode_compensationDeficit_pos
      hab hb0 hbt htneg
  · exact suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt
      hpositiveBlock

end

end RHTower
