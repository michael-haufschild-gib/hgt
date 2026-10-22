import GaloisForLFunctions.RHTower.Suzuki.SuzukiJumpKernelLoewnerGap
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftSpectralMonotoneRatio

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
  positiveBlock * x ^ (2 : ℕ) + 2 * coupling * x * y +
    (directCompletion - debt) * y ^ (2 : ℕ)

/-- Exact completed-square form of the two-channel weld. -/
theorem suzukiTwoChannelKreinCompletionForm_eq_completedSquare
    {positiveBlock coupling directCompletion debt x y : ℝ}
    (hpositiveBlock : positiveBlock ≠ 0) :
    suzukiTwoChannelKreinCompletionForm
        positiveBlock coupling directCompletion debt x y =
      positiveBlock * (x + coupling / positiveBlock * y) ^ (2 : ℕ) +
        (directCompletion - debt - coupling ^ (2 : ℕ) / positiveBlock) * y ^ (2 : ℕ) := by
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
      debt + coupling ^ (2 : ℕ) / positiveBlock ≤ directCompletion := by
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
        0 ≤ positiveBlock * (x + coupling / positiveBlock * y) ^ (2 : ℕ) :=
      mul_nonneg (le_of_lt hpositiveBlock) (sq_nonneg _)
    have hresidual :
        0 ≤ directCompletion - debt - coupling ^ (2 : ℕ) / positiveBlock := by
      linarith
    have hsecond :
        0 ≤ (directCompletion - debt - coupling ^ (2 : ℕ) / positiveBlock) * y ^ (2 : ℕ) :=
      mul_nonneg hresidual (sq_nonneg _)
    linarith

/-- Nonzero holonomy coupling imposes a strictly positive cost beyond diagonal Krein debt. -/
theorem suzukiProjectiveCoupling_schurTax_strict
    {positiveBlock coupling debt : ℝ}
    (hpositiveBlock : 0 < positiveBlock) (hcoupling : coupling ≠ 0) :
    debt < debt + coupling ^ (2 : ℕ) / positiveBlock := by
  have hcouplingSq : 0 < coupling ^ (2 : ℕ) := sq_pos_of_ne_zero hcoupling
  have htax : 0 < coupling ^ (2 : ℕ) / positiveBlock :=
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
            coupling ^ (2 : ℕ) / positiveBlock ≤ directCompletion) := by
  constructor
  · exact suzukiNegativeSpectralNode_compensationDeficit_pos
      hab hb0 hbt htneg
  · exact suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt
      hpositiveBlock

end

/-! ## The no-go at the level of a factorization

The scalar statement says the bare gap is negative at a negative node.  The no-go the frontier
argument needs is stronger: that no *presentation of the gap as a squared norm* can exist at all once
such a node is present.  It follows at once, since a squared norm is nonnegative — but it is a
statement about factorizations, not about one value, and that is what rules out a `B*B` form rather
than merely exhibiting a negative number.

The hypotheses are satisfiable, so the no-go is not vacuous. -/

/-- **No squared-norm presentation at a negative node.**  No assignment of vectors to spectral nodes
can present the bare anti-resolvent gap as a squared norm: at a negative node the value would be a
negative square. -/
theorem no_squaredNorm_presentation_of_negativeNode
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    {t : ι → ℝ} {j : ι} (hbt : beta < t j) (htneg : t j < 0)
    (B : ι → V) (hQ : ∀ i, suzukiAffineAntiResolventGap alpha beta (t i) = ‖B i‖ ^ (2 : ℕ)) :
    False := by
  refine suzukiNegativeSpectralNode_bareAntiResolventGap_not_nonneg hab hb0 hbt htneg ?_
  rw [hQ j]
  positivity

/-- The same with the factorization given by an inner product of a single map against itself, which
is the `B*B` form the retired claim proposed. -/
theorem no_innerSelf_presentation_of_negativeNode
    {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    {t : ι → ℝ} {j : ι} (hbt : beta < t j) (htneg : t j < 0)
    (B : ι → V) (hQ : ∀ i, suzukiAffineAntiResolventGap alpha beta (t i) = inner ℝ (B i) (B i)) :
    False := by
  refine no_squaredNorm_presentation_of_negativeNode hab hb0 hbt htneg B fun i => ?_
  rw [hQ i, ← real_inner_self_eq_norm_sq]

/-- **The no-go is not vacuous.**  A negative node in the required range exists. -/
theorem negativeNode_range_nonempty :
    ∃ alpha beta t : ℝ, alpha < beta ∧ beta < 0 ∧ beta < t ∧ t < 0 :=
  ⟨-2, -1, -1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The diagonal form and its negative index

On a finite diagonal spectral model the sewn form is the weighted sum of the defect over the nodes.
Splitting the index set by the sign of the node splits the form into a nonnegative part and a
nonpositive one, term by term — which is the exact sense in which the negative index counts the
negative nodes.  Nothing here is an estimate: each term's sign is decided by its own node. -/

/-- The sewn form of a finite diagonal spectral model. -/
noncomputable def suzukiDiagonalKreinForm {ι : Type*} (s : Finset ι) (alpha beta : ℝ) (t c : ι → ℝ) : ℝ :=
  ∑ j ∈ s, (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j)

/-- **`(8)`, the signed split.**  The form is its positive-node part plus its negative-node part. -/
theorem suzukiDiagonalKreinForm_split {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (alpha beta : ℝ) (t c : ι → ℝ) :
    suzukiDiagonalKreinForm s alpha beta t c
      = (∑ j ∈ s.filter (fun j => 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j))
        + ∑ j ∈ s.filter (fun j => ¬ 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j) :=
  (Finset.sum_filter_add_sum_filter_not s _ _).symm

/-- Every positive-node term is nonnegative. -/
theorem suzukiDiagonalKreinForm_posPart_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0) (t c : ι → ℝ)
    (hbt : ∀ j ∈ s, beta < t j) :
    0 ≤ ∑ j ∈ s.filter (fun j => 0 < t j),
      (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j) := by
  refine Finset.sum_nonneg fun j hj => ?_
  rw [Finset.mem_filter] at hj
  refine mul_nonneg (sq_nonneg _) (le_of_lt ?_)
  exact (suzukiAffineResolventKreinDefect_pos_iff hab hb0 (hbt j hj.1)
    (ne_of_gt hj.2)).2 hj.2

/-- Every negative-node term is nonpositive: the defect is negative there. -/
theorem suzukiDiagonalKreinForm_negPart_nonpos {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0) (t c : ι → ℝ)
    (hbt : ∀ j ∈ s, beta < t j) (hne : ∀ j ∈ s, t j ≠ 0) :
    ∑ j ∈ s.filter (fun j => ¬ 0 < t j),
      (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j) ≤ 0 := by
  refine Finset.sum_nonpos fun j hj => ?_
  rw [Finset.mem_filter] at hj
  have htneg : t j < 0 := lt_of_le_of_ne (le_of_not_gt hj.2) (hne j hj.1)
  refine mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_lt ?_)
  exact (suzukiAffineResolventKreinDefect_neg_iff hab hb0 (hbt j hj.1)
    (hne j hj.1)).2 htneg

/-- **An all-negative model has a nonpositive form.**  So a spectral model whose nodes are all
negative admits no nonnegative sewn form at all — the negative index is full. -/
theorem suzukiDiagonalKreinForm_nonpos_of_allNegative {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0) (t c : ι → ℝ)
    (hbt : ∀ j ∈ s, beta < t j) (hneg : ∀ j ∈ s, t j < 0) :
    suzukiDiagonalKreinForm s alpha beta t c ≤ 0 := by
  refine Finset.sum_nonpos fun j hj => ?_
  refine mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_lt ?_)
  exact (suzukiAffineResolventKreinDefect_neg_iff hab hb0 (hbt j hj)
    (ne_of_lt (hneg j hj))).2 (hneg j hj)

/-! ## The exact Krein factorization

The sign equivalences say *which way* the defect points; the factorization of `(5)` says more: it
names the positive magnitude the sign multiplies.  That magnitude is what `(11)`'s debt is measured
in, so it needs a definition rather than an inequality. -/

/-- The Krein magnitude of `(5)`: the positive size of the defect, with the node's sign removed. -/
noncomputable def suzukiKreinMagnitude (alpha beta t : ℝ) : ℝ :=
  alpha * beta / (|t| * (t - alpha) * (t - beta))

/-- **The magnitude is strictly positive** below the spectrum. -/
theorem suzukiKreinMagnitude_pos {alpha beta t : ℝ} (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : beta < t) (ht : t ≠ 0) : 0 < suzukiKreinMagnitude alpha beta t := by
  have ha0 : alpha < 0 := lt_trans hab hb0
  have hp : 0 < alpha * beta := mul_pos_of_neg_of_neg ha0 hb0
  have hta : 0 < t - alpha := by linarith
  have htb : 0 < t - beta := by linarith
  have habs : 0 < |t| := abs_pos.mpr ht
  exact div_pos hp (mul_pos (mul_pos habs hta) htb)

/-- **`(5)`, the exact Krein factorization.**  The defect is the node's sign times the magnitude. -/
theorem suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude {alpha beta t : ℝ}
    (hab : alpha ≠ beta) (ht : t ≠ 0) (hta : t ≠ alpha) (htb : t ≠ beta) :
    suzukiAffineResolventKreinDefect alpha beta t
      = Real.sign t * suzukiKreinMagnitude alpha beta t := by
  rw [suzukiAffineResolventKreinDefect_eq hab ht hta htb, suzukiKreinMagnitude]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    ring

/-- **`(11)`, the strictly positive debt.**  At a negative node the anti-resolvent gap's deficit is
exactly the magnitude, hence strictly positive. -/
theorem neg_kreinDefect_eq_magnitude_of_neg {alpha beta t : ℝ}
    (hab : alpha ≠ beta) (hta : t ≠ alpha) (htb : t ≠ beta) (htneg : t < 0) :
    -suzukiAffineResolventKreinDefect alpha beta t = suzukiKreinMagnitude alpha beta t := by
  rw [suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude hab (ne_of_lt htneg) hta htb,
    Real.sign_of_neg htneg]
  ring

/-! ## The form in magnitude terms

Rewriting each node's contribution through the factorization puts the diagonal form in the shape
`(8)` displays: a sum of magnitudes over the positive nodes minus a sum over the negative ones.  The
second sum is the completion debt, quantified coordinate by coordinate. -/

/-- At a positive node the defect equals the magnitude outright. -/
theorem kreinDefect_eq_magnitude_of_pos {alpha beta t : ℝ}
    (hab : alpha ≠ beta) (hta : t ≠ alpha) (htb : t ≠ beta) (htpos : 0 < t) :
    suzukiAffineResolventKreinDefect alpha beta t = suzukiKreinMagnitude alpha beta t := by
  rw [suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude hab (ne_of_gt htpos) hta htb,
    Real.sign_of_pos htpos, one_mul]

/-- **The completion debt.**  The negative-node part of the form is exactly minus the weighted sum of
magnitudes there — the contribution a completion must supply, coordinate by coordinate. -/
theorem suzukiDiagonalKreinForm_negPart_eq {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha ≠ beta) (t c : ι → ℝ)
    (hta : ∀ j ∈ s, t j ≠ alpha) (htb : ∀ j ∈ s, t j ≠ beta) (hne : ∀ j ∈ s, t j ≠ 0) :
    (∑ j ∈ s.filter (fun j => ¬ 0 < t j),
        (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j))
      = -∑ j ∈ s.filter (fun j => ¬ 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  have htneg : t j < 0 := lt_of_le_of_ne (le_of_not_gt hj.2) (hne j hj.1)
  rw [suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude hab (hne j hj.1) (hta j hj.1)
    (htb j hj.1), Real.sign_of_neg htneg]
  ring

/-- The positive-node part is the weighted sum of magnitudes there. -/
theorem suzukiDiagonalKreinForm_posPart_eq {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha ≠ beta) (t c : ι → ℝ)
    (hta : ∀ j ∈ s, t j ≠ alpha) (htb : ∀ j ∈ s, t j ≠ beta) :
    (∑ j ∈ s.filter (fun j => 0 < t j),
        (c j) ^ (2 : ℕ) * suzukiAffineResolventKreinDefect alpha beta (t j))
      = ∑ j ∈ s.filter (fun j => 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j) := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [kreinDefect_eq_magnitude_of_pos hab (hta j hj.1) (htb j hj.1) hj.2]

/-- **`(8)` as displayed.**  The sewn form is the magnitude sum over positive nodes minus the
magnitude sum over negative ones. -/
theorem suzukiDiagonalKreinForm_eq_magnitude_difference {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha ≠ beta) (t c : ι → ℝ)
    (hta : ∀ j ∈ s, t j ≠ alpha) (htb : ∀ j ∈ s, t j ≠ beta) (hne : ∀ j ∈ s, t j ≠ 0) :
    suzukiDiagonalKreinForm s alpha beta t c
      = (∑ j ∈ s.filter (fun j => 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j))
        - ∑ j ∈ s.filter (fun j => ¬ 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j) := by
  rw [suzukiDiagonalKreinForm_split, suzukiDiagonalKreinForm_posPart_eq s hab t c hta htb,
    suzukiDiagonalKreinForm_negPart_eq s hab t c hta htb hne]
  ring

/-! ## The positive survivor

The no-go retires the bare square, not the route: adding the completion debt to the sewn form
cancels its negative part exactly, leaving the positive-node sum.  So the survivor is the signed
factorization *plus* an explicit debt, and the debt is the one quantified above — not an unspecified
correction. -/

/-- **Adding the debt leaves the positive part.**  The completion cancels the negative-node sum
exactly. -/
theorem suzukiDiagonalKreinForm_add_debt_eq_posPart {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha ≠ beta) (t c : ι → ℝ)
    (hta : ∀ j ∈ s, t j ≠ alpha) (htb : ∀ j ∈ s, t j ≠ beta) (hne : ∀ j ∈ s, t j ≠ 0) :
    suzukiDiagonalKreinForm s alpha beta t c
        + ∑ j ∈ s.filter (fun j => ¬ 0 < t j),
            (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j)
      = ∑ j ∈ s.filter (fun j => 0 < t j),
          (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j) := by
  rw [suzukiDiagonalKreinForm_eq_magnitude_difference s hab t c hta htb hne]
  ring

/-- **The positive survivor.**  With the debt supplied the form is nonnegative — which is what the
no-go leaves standing once the bare square is retired. -/
theorem suzukiDiagonalKreinForm_add_debt_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {alpha beta : ℝ} (hab : alpha < beta) (hb0 : beta < 0) (t c : ι → ℝ)
    (hbt : ∀ j ∈ s, beta < t j) (hne : ∀ j ∈ s, t j ≠ 0) :
    0 ≤ suzukiDiagonalKreinForm s alpha beta t c
        + ∑ j ∈ s.filter (fun j => ¬ 0 < t j),
            (c j) ^ (2 : ℕ) * suzukiKreinMagnitude alpha beta (t j) := by
  have hta : ∀ j ∈ s, t j ≠ alpha := fun j hj =>
    ne_of_gt (lt_trans hab (hbt j hj))
  have htb : ∀ j ∈ s, t j ≠ beta := fun j hj => ne_of_gt (hbt j hj)
  rw [suzukiDiagonalKreinForm_add_debt_eq_posPart s (ne_of_lt hab) t c hta htb hne]
  refine Finset.sum_nonneg fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact mul_nonneg (sq_nonneg _)
    (le_of_lt (suzukiKreinMagnitude_pos hab hb0 (hbt j hj.1) (hne j hj.1)))

end RHTower
