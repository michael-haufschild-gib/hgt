import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventOperatorLift
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The coherent completion is the weighted negative part of the affine defect

The affine Krein defect of a lower-bounded self-adjoint operator with `0` in its resolvent set is a
rational function of the *bounded* operator `A⁻¹`.  Reading the defect in that inverse coordinate,

`d(x) = α β x³ / ((1 - α x)(1 - β x))`,

turns the whole signed functional-calculus theorem into continuous functional calculus of one
bounded self-adjoint operator: no spectral projections and no Borel calculus are needed, because
the two spectral halves of the defect are exactly its positive and negative parts.

The weight of the paper statement is recovered as `ω = |d|`, so `|D| = W` is an identity of
continuous functions, and the canonical Jordan decomposition `D = D₊ - D₋` is the positive/negative
part decomposition.  Minimality of `D₋` among commuting positive corrections becomes the pointwise
comparison `c ≥ d⁻` on the spectrum, and the coherent Gram law is ordinary positivity of `D₊` and
`D₋` tested on arbitrary finite node families.

Everything is unconditional: no RH premise, no Xi divisor, no estimate, no computation.
-/

open Polynomial ContinuousLinearMap

namespace RHTower

noncomputable section

/-! ## The defect and its weight in the inverse spectral coordinate -/

/-- The affine Krein defect read in the inverse coordinate `x = 1 / t`. -/
def suzukiInverseKreinDefect (alpha beta x : ℝ) : ℝ :=
  alpha * beta * x ^ 3 / ((1 - alpha * x) * (1 - beta * x))

/-- The positive weight of the coherent completion, in the inverse coordinate. -/
def suzukiInverseKreinWeight (alpha beta x : ℝ) : ℝ :=
  alpha * beta * |x| * x ^ 2 / ((1 - alpha * x) * (1 - beta * x))

@[simp] theorem suzukiInverseKreinDefect_zero (alpha beta : ℝ) :
    suzukiInverseKreinDefect alpha beta 0 = 0 := by
  simp [suzukiInverseKreinDefect]

@[simp] theorem suzukiInverseKreinWeight_zero (alpha beta : ℝ) :
    suzukiInverseKreinWeight alpha beta 0 = 0 := by
  simp [suzukiInverseKreinWeight]

/-- **Spectral bridge.**  In the inverse coordinate the defect is the affine Krein defect. -/
theorem suzukiInverseKreinDefect_inv
    {alpha beta t : ℝ} (hab : alpha ≠ beta) (ht0 : t ≠ 0) (hta : t ≠ alpha) (htb : t ≠ beta) :
    suzukiInverseKreinDefect alpha beta t⁻¹
      = suzukiAffineResolventKreinDefect alpha beta t := by
  have hta' : t - alpha ≠ 0 := sub_ne_zero.mpr hta
  have htb' : t - beta ≠ 0 := sub_ne_zero.mpr htb
  have h1 : 1 - alpha * t⁻¹ = (t - alpha) / t := by
    rw [eq_div_iff ht0, sub_mul, mul_assoc, inv_mul_cancel₀ ht0]
    ring
  have h2 : 1 - beta * t⁻¹ = (t - beta) / t := by
    rw [eq_div_iff ht0, sub_mul, mul_assoc, inv_mul_cancel₀ ht0]
    ring
  have key : (t - alpha) / t * ((t - beta) / t) = (t - alpha) * (t - beta) / t ^ 2 := by
    field_simp
  rw [suzukiAffineResolventKreinDefect_eq hab ht0 hta htb, suzukiInverseKreinDefect, h1, h2, key,
    div_div_eq_mul_div]
  rw [div_eq_div_iff (by
      exact mul_ne_zero hta' htb') (by
      exact mul_ne_zero (mul_ne_zero ht0 hta') htb')]
  field_simp

/-- **The weight is the absolute value of the defect.**  Positivity of the two shift factors and of
the shift product is exactly the below-spectrum hypothesis of the source. -/
theorem suzukiInverseKreinWeight_eq_abs
    {alpha beta x : ℝ} (hab : 0 < alpha * beta)
    (hden : 0 < (1 - alpha * x) * (1 - beta * x)) :
    suzukiInverseKreinWeight alpha beta x = |suzukiInverseKreinDefect alpha beta x| := by
  rw [suzukiInverseKreinDefect, suzukiInverseKreinWeight, abs_div,
    abs_of_pos hden]
  congr 1
  rw [abs_mul, abs_of_pos hab, abs_pow]
  rw [show |x| ^ 3 = |x| * x ^ 2 by
    rw [pow_succ, pow_two, ← abs_mul, abs_mul_self, ← pow_two]
    ring]
  ring

/-! ## The signed functional calculus of the defect -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The affine defect operator, realized as a continuous function of the bounded inverse `A⁻¹`. -/
def suzukiInverseDefectOperator (alpha beta : ℝ) (B : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (suzukiInverseKreinDefect alpha beta) B

theorem isSelfAdjoint_suzukiInverseDefectOperator (alpha beta : ℝ) (B : H →L[ℂ] H) :
    IsSelfAdjoint (suzukiInverseDefectOperator alpha beta B) := by
  rw [suzukiInverseDefectOperator]
  exact cfc_predicate (R := ℝ) _ B

/-- **`(5)`, the canonical Jordan decomposition.**  The defect is the difference of its positive
and negative parts, both positive operators. -/
theorem suzukiInverseDefect_posPart_sub_negPart (alpha beta : ℝ) (B : H →L[ℂ] H) :
    (suzukiInverseDefectOperator alpha beta B)⁺ - (suzukiInverseDefectOperator alpha beta B)⁻
      = suzukiInverseDefectOperator alpha beta B :=
  CFC.posPart_sub_negPart _ (isSelfAdjoint_suzukiInverseDefectOperator alpha beta B)

theorem suzukiInverseDefect_posPart_nonneg (alpha beta : ℝ) (B : H →L[ℂ] H) :
    0 ≤ (suzukiInverseDefectOperator alpha beta B)⁺ := CFC.posPart_nonneg _

theorem suzukiInverseDefect_negPart_nonneg (alpha beta : ℝ) (B : H →L[ℂ] H) :
    0 ≤ (suzukiInverseDefectOperator alpha beta B)⁻ := CFC.negPart_nonneg _

/-- **`(6)`.**  Adding the negative part completes the defect to its positive part. -/
theorem suzukiInverseDefect_add_negPart (alpha beta : ℝ) (B : H →L[ℂ] H) :
    suzukiInverseDefectOperator alpha beta B + (suzukiInverseDefectOperator alpha beta B)⁻
      = (suzukiInverseDefectOperator alpha beta B)⁺ :=
  (sub_eq_iff_eq_add.mp (suzukiInverseDefect_posPart_sub_negPart alpha beta B)).symm

theorem suzukiInverseDefect_add_negPart_nonneg (alpha beta : ℝ) (B : H →L[ℂ] H) :
    0 ≤ suzukiInverseDefectOperator alpha beta B
      + (suzukiInverseDefectOperator alpha beta B)⁻ := by
  rw [suzukiInverseDefect_add_negPart]
  exact suzukiInverseDefect_posPart_nonneg alpha beta B

/-- **`(7)`.**  Adding twice the negative part completes the defect to its absolute value. -/
theorem suzukiInverseDefect_add_two_negPart (alpha beta : ℝ) (B : H →L[ℂ] H) :
    suzukiInverseDefectOperator alpha beta B
        + 2 • (suzukiInverseDefectOperator alpha beta B)⁻
      = CFC.abs (suzukiInverseDefectOperator alpha beta B) := by
  have h := CFC.abs_sub_self (suzukiInverseDefectOperator alpha beta B)
    (isSelfAdjoint_suzukiInverseDefectOperator alpha beta B)
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-! ## `(8)`: sharp classification of commuting positive corrections -/

theorem continuousOn_suzukiInverseKreinDefect (alpha beta : ℝ) {s : Set ℝ}
    (hs : ∀ x ∈ s, (1 - alpha * x) * (1 - beta * x) ≠ 0) :
    ContinuousOn (suzukiInverseKreinDefect alpha beta) s := by
  unfold suzukiInverseKreinDefect
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hs

/-- **`(8)`.**  A commuting correction completes the affine defect to a positive operator exactly
when it dominates the defect pointwise on the spectrum. -/
theorem suzukiInverseDefect_add_nonneg_iff
    {alpha beta : ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (c : ℝ → ℝ)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0)
    (hc : ContinuousOn c (spectrum ℝ B)) :
    0 ≤ suzukiInverseDefectOperator alpha beta B + cfc c B ↔
      ∀ x ∈ spectrum ℝ B, 0 ≤ suzukiInverseKreinDefect alpha beta x + c x := by
  have hd : ContinuousOn (suzukiInverseKreinDefect alpha beta) (spectrum ℝ B) :=
    continuousOn_suzukiInverseKreinDefect alpha beta hden
  have hsum : suzukiInverseDefectOperator alpha beta B + cfc c B
      = cfc (fun x => suzukiInverseKreinDefect alpha beta x + c x) B := by
    rw [suzukiInverseDefectOperator, cfc_add B _ _ hd hc]
  rw [hsum]
  exact cfc_nonneg_iff _ B (hd.add hc) hB

/-- **Scalar minimality.**  A nonnegative correction dominating the defect dominates the negative
part of the defect pointwise; the negative part is the pointwise-minimal such correction. -/
theorem negPart_le_of_add_nonneg {d c : ℝ} (hc : 0 ≤ c) (hdc : 0 ≤ d + c) : d⁻ ≤ c := by
  rw [negPart_def]
  refine max_le ?_ hc
  linarith

/-! ## `(10)`-`(12)`: the coherent finite-node Gram kernel -/

/-- **Positive operators have positive semidefinite Gram kernels.**  Applied to the positive part
and to the negative part of the affine defect this is the coherent assembly law: the off-diagonal
entries are not free, they are the Gram entries of the operator. -/
theorem gram_re_nonneg_of_nonneg {D : H →L[ℂ] H} (hD : 0 ≤ D) {ι : Type*} (s : Finset ι)
    (Gamma : ι → H) (c : ι → ℂ) :
    0 ≤ RCLike.re (∑ i ∈ s, ∑ j ∈ s,
      (starRingEnd ℂ) (c i) * c j * inner ℂ (D (Gamma i)) (Gamma j)) := by
  classical
  set y : H := ∑ i ∈ s, c i • Gamma i with hy
  have hval : (∑ i ∈ s, ∑ j ∈ s,
      (starRingEnd ℂ) (c i) * c j * inner ℂ (D (Gamma i)) (Gamma j)) = inner ℂ (D y) y := by
    rw [hy, map_sum]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    ring
  rw [hval]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive D).mp hD).re_inner_nonneg_left y

/-- **`(12)`.**  The Gram kernel of the defect plus the Gram kernel of its negative part is the
Gram kernel of its positive part, and is positive semidefinite. -/
theorem gram_defect_add_negPart_nonneg (alpha beta : ℝ) (B : H →L[ℂ] H)
    {ι : Type*} (s : Finset ι) (Gamma : ι → H) (c : ι → ℂ) :
    0 ≤ RCLike.re (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
      * inner ℂ ((suzukiInverseDefectOperator alpha beta B
        + (suzukiInverseDefectOperator alpha beta B)⁻) (Gamma i)) (Gamma j)) :=
  gram_re_nonneg_of_nonneg (suzukiInverseDefect_add_negPart_nonneg alpha beta B) s Gamma c

/-- The negative part itself has a positive semidefinite Gram kernel. -/
theorem gram_negPart_nonneg (alpha beta : ℝ) (B : H →L[ℂ] H)
    {ι : Type*} (s : Finset ι) (Gamma : ι → H) (c : ι → ℂ) :
    0 ≤ RCLike.re (∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ) (c i) * c j
      * inner ℂ ((suzukiInverseDefectOperator alpha beta B)⁻ (Gamma i)) (Gamma j)) :=
  gram_re_nonneg_of_nonneg (suzukiInverseDefect_negPart_nonneg alpha beta B) s Gamma c

end

end RHTower
