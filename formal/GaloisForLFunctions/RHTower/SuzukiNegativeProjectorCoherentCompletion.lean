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

omit [CompleteSpace H] in
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

/-- **`(11)`, the square-root factorization.**  The Gram kernel of a positive operator is the Gram
kernel of its square root: the off-diagonal entries are genuine inner products of one family of
vectors, not merely a positive form. -/
theorem inner_eq_inner_sqrt {D : H →L[ℂ] H} (hD : 0 ≤ D) (v w : H) :
    inner ℂ (D w) v = inner ℂ (CFC.sqrt D w) (CFC.sqrt D v) := by
  have hsa : IsSelfAdjoint (CFC.sqrt D) := (CFC.sqrt_nonneg D).isSelfAdjoint
  have hsq : CFC.sqrt D * CFC.sqrt D = D := CFC.sqrt_mul_sqrt_self D hD
  have happ : D w = CFC.sqrt D (CFC.sqrt D w) := by
    conv_lhs => rw [← hsq]
    rfl
  rw [happ]
  have h := ContinuousLinearMap.adjoint_inner_left (CFC.sqrt D) (CFC.sqrt D w) v
  rw [hsa.adjoint_eq] at h
  simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) h.symm

/-- **`(11)` for the negative part.**  The coherent completion kernel is the Gram kernel of the
square root of the negative part of the affine defect. -/
theorem inner_negPart_eq_inner_sqrt (alpha beta : ℝ) (B : H →L[ℂ] H) (v w : H) :
    inner ℂ ((suzukiInverseDefectOperator alpha beta B)⁻ w) v
      = inner ℂ (CFC.sqrt ((suzukiInverseDefectOperator alpha beta B)⁻) w)
          (CFC.sqrt ((suzukiInverseDefectOperator alpha beta B)⁻) v) :=
  inner_eq_inner_sqrt (suzukiInverseDefect_negPart_nonneg alpha beta B) v w

/-- The negative part of a continuous function of a self-adjoint operator is the functional
calculus of the negative part of the function. -/
theorem negPart_cfc {f : ℝ → ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hf : ContinuousOn f (spectrum ℝ B)) :
    (cfc f B)⁻ = cfc (fun x => (f x)⁻) B := by
  have hcomp : cfc (fun x => (f x)⁻) B = cfc (fun y : ℝ => y⁻) (cfc f B) :=
    cfc_comp (fun y : ℝ => y⁻) f B
  rw [hcomp, CFC.negPart_def, cfcₙ_eq_cfc]

/-- **`(9)`, operator minimality.**  A commuting positive correction that completes the defect
dominates the negative part of the defect, which is therefore the Loewner-minimal such
correction. -/
theorem negPart_le_of_cfc_add_nonneg {alpha beta : ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    {c : ℝ → ℝ} (hc : ContinuousOn c (spectrum ℝ B))
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0)
    (hcnn : ∀ x ∈ spectrum ℝ B, 0 ≤ c x)
    (hdom : ∀ x ∈ spectrum ℝ B, 0 ≤ suzukiInverseKreinDefect alpha beta x + c x) :
    (suzukiInverseDefectOperator alpha beta B)⁻ ≤ cfc c B := by
  have hd : ContinuousOn (suzukiInverseKreinDefect alpha beta) (spectrum ℝ B) :=
    continuousOn_suzukiInverseKreinDefect alpha beta hden
  have hdneg : ContinuousOn (fun x => (suzukiInverseKreinDefect alpha beta x)⁻)
      (spectrum ℝ B) := hd.neg.sup continuousOn_const
  have hneg : (suzukiInverseDefectOperator alpha beta B)⁻
      = cfc (fun x => (suzukiInverseKreinDefect alpha beta x)⁻) B := by
    rw [suzukiInverseDefectOperator]
    exact negPart_cfc hB hd
  rw [hneg, ← sub_nonneg, ← cfc_sub c (fun x => (suzukiInverseKreinDefect alpha beta x)⁻) B hc hdneg]
  refine (cfc_nonneg_iff _ B (hc.sub hdneg) hB).mpr ?_
  intro x hx
  exact sub_nonneg.mpr (negPart_le_of_add_nonneg (hcnn x hx) (hdom x hx))

/-- The commuting positive corrections that complete the affine defect to a positive operator:
continuous functions of `B` that are nonnegative and dominate the defect on the spectrum. -/
def suzukiCommutingCompletions (alpha beta : ℝ) (B : H →L[ℂ] H) : Set (H →L[ℂ] H) :=
  {C | ∃ c : ℝ → ℝ, ContinuousOn c (spectrum ℝ B) ∧ C = cfc c B ∧
    (∀ x ∈ spectrum ℝ B, 0 ≤ c x) ∧
    (∀ x ∈ spectrum ℝ B, 0 ≤ suzukiInverseKreinDefect alpha beta x + c x)}

/-- The negative part of the defect is itself such a correction: it is nonnegative, and adding it
to the defect gives the positive part. -/
theorem negPart_mem_commutingCompletions {alpha beta : ℝ} {B : H →L[ℂ] H}
    (hB : IsSelfAdjoint B)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0) :
    (suzukiInverseDefectOperator alpha beta B)⁻ ∈ suzukiCommutingCompletions alpha beta B := by
  have hd : ContinuousOn (suzukiInverseKreinDefect alpha beta) (spectrum ℝ B) :=
    continuousOn_suzukiInverseKreinDefect alpha beta hden
  refine ⟨fun x => (suzukiInverseKreinDefect alpha beta x)⁻,
    hd.neg.sup continuousOn_const, ?_, fun x _ => negPart_nonneg _, fun x _ => ?_⟩
  · rw [suzukiInverseDefectOperator]
    exact negPart_cfc hB hd
  · have h1 := posPart_sub_negPart (suzukiInverseKreinDefect alpha beta x)
    have h2 : (0 : ℝ) ≤ (suzukiInverseKreinDefect alpha beta x)⁺ := posPart_nonneg _
    linarith

/-- **`(9)`, least element.**  The negative part of the defect is the least commuting positive
correction completing the defect, not merely a lower bound for such corrections. -/
theorem negPart_isLeast_commutingCompletions {alpha beta : ℝ} {B : H →L[ℂ] H}
    (hB : IsSelfAdjoint B)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0) :
    IsLeast (suzukiCommutingCompletions alpha beta B)
      ((suzukiInverseDefectOperator alpha beta B)⁻) := by
  refine ⟨negPart_mem_commutingCompletions hB hden, ?_⟩
  rintro C ⟨c, hc, rfl, hcnn, hdom⟩
  exact negPart_le_of_cfc_add_nonneg hB hc hden hcnn hdom

/-- **Uniqueness of the minimal correction.**  Any Loewner-minimal commuting positive completion of
the defect equals the negative part of the defect. -/
theorem eq_negPart_of_minimal_commutingCompletion {alpha beta : ℝ} {B : H →L[ℂ] H}
    (hB : IsSelfAdjoint B)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0)
    {C : H →L[ℂ] H} (hC : C ∈ suzukiCommutingCompletions alpha beta B)
    (hmin : ∀ C' ∈ suzukiCommutingCompletions alpha beta B, C' ≤ C → C' = C) :
    C = (suzukiInverseDefectOperator alpha beta B)⁻ := by
  have hleast := negPart_isLeast_commutingCompletions hB hden
  exact (hmin _ hleast.1 (hleast.2 hC)).symm

/-- The least commuting positive completion is unique, by antisymmetry of the Loewner order. -/
theorem isLeast_commutingCompletion_unique {alpha beta : ℝ} {B : H →L[ℂ] H}
    {C D : H →L[ℂ] H} (hC : IsLeast (suzukiCommutingCompletions alpha beta B) C)
    (hD : IsLeast (suzukiCommutingCompletions alpha beta B) D) : C = D :=
  hC.unique hD

/-- The absolute value of a continuous function of a self-adjoint operator is the functional
calculus of the absolute value of the function. -/
theorem abs_cfc {f : ℝ → ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hf : ContinuousOn f (spectrum ℝ B)) :
    CFC.abs (cfc f B) = cfc (fun x => |f x|) B := by
  have hcomp : cfc (fun x => |f x|) B = cfc (fun y : ℝ => |y|) (cfc f B) :=
    cfc_comp (fun y : ℝ => |y|) f B
  have hsa : IsSelfAdjoint (cfc f B) := cfc_predicate f B
  rw [hcomp, CFC.abs_eq_cfcₙ_norm (cfc f B) hsa, cfcₙ_eq_cfc]
  exact cfc_congr fun y _ => Real.norm_eq_abs y

/-- **`(4)`, the modulus identity.**  The absolute value of the affine defect operator is the
weight operator: `|D| = W`. -/
theorem abs_suzukiInverseDefect_eq_weight {alpha beta : ℝ} {B : H →L[ℂ] H}
    (hB : IsSelfAdjoint B) (hab : 0 < alpha * beta)
    (hden : ∀ x ∈ spectrum ℝ B, 0 < (1 - alpha * x) * (1 - beta * x)) :
    CFC.abs (suzukiInverseDefectOperator alpha beta B)
      = cfc (suzukiInverseKreinWeight alpha beta) B := by
  have hd : ContinuousOn (suzukiInverseKreinDefect alpha beta) (spectrum ℝ B) :=
    continuousOn_suzukiInverseKreinDefect alpha beta fun x hx => ne_of_gt (hden x hx)
  rw [suzukiInverseDefectOperator, abs_cfc hB hd]
  exact cfc_congr fun x hx => (suzukiInverseKreinWeight_eq_abs hab (hden x hx)).symm

/-- The positive part of a continuous function of a self-adjoint operator is the functional
calculus of the positive part of the function. -/
theorem posPart_cfc {f : ℝ → ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hf : ContinuousOn f (spectrum ℝ B)) :
    (cfc f B)⁺ = cfc (fun x => (f x)⁺) B := by
  have hcomp : cfc (fun x => (f x)⁺) B = cfc (fun y : ℝ => y⁺) (cfc f B) :=
    cfc_comp (fun y : ℝ => y⁺) f B
  rw [hcomp, CFC.posPart_def, cfcₙ_eq_cfc]

/-- **`(5)` at the level of the functional calculus.**  The two spectral halves of the affine
defect are the functional calculus of the two halves of its symbol. -/
theorem posPart_suzukiInverseDefect {alpha beta : ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0) :
    (suzukiInverseDefectOperator alpha beta B)⁺
      = cfc (fun x => (suzukiInverseKreinDefect alpha beta x)⁺) B := by
  rw [suzukiInverseDefectOperator]
  exact posPart_cfc hB (continuousOn_suzukiInverseKreinDefect alpha beta hden)

/-- The same for the negative half. -/
theorem negPart_suzukiInverseDefect {alpha beta : ℝ} {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hden : ∀ x ∈ spectrum ℝ B, (1 - alpha * x) * (1 - beta * x) ≠ 0) :
    (suzukiInverseDefectOperator alpha beta B)⁻
      = cfc (fun x => (suzukiInverseKreinDefect alpha beta x)⁻) B := by
  rw [suzukiInverseDefectOperator]
  exact negPart_cfc hB (continuousOn_suzukiInverseKreinDefect alpha beta hden)

/-! ## `(4)`, the resolvent product form -/

/-- The shifted resolvent factor in the inverse coordinate: `x / (1 - alpha x)` corresponds to
`(A - alpha)⁻¹`. -/
def suzukiInverseShiftFactor (alpha x : ℝ) : ℝ := x / (1 - alpha * x)

theorem continuousOn_suzukiInverseShiftFactor (alpha : ℝ) {s : Set ℝ}
    (hs : ∀ x ∈ s, 1 - alpha * x ≠ 0) :
    ContinuousOn (suzukiInverseShiftFactor alpha) s := by
  unfold suzukiInverseShiftFactor
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hs

/-- Scalar form of `(4)`: the defect is the product of the three resolvent factors, scaled. -/
theorem suzukiInverseKreinDefect_eq_product {alpha beta x : ℝ}
    (ha : 1 - alpha * x ≠ 0) (hb : 1 - beta * x ≠ 0) :
    suzukiInverseKreinDefect alpha beta x
      = alpha * beta * (x * (suzukiInverseShiftFactor alpha x
          * suzukiInverseShiftFactor beta x)) := by
  rw [suzukiInverseKreinDefect, suzukiInverseShiftFactor, suzukiInverseShiftFactor]
  field_simp

/-- **`(4)`, operator product form.**  The affine defect operator is the scaled product of the
three below-spectrum resolvents, realized in the inverse coordinate. -/
theorem suzukiInverseDefectOperator_eq_product {alpha beta : ℝ} {B : H →L[ℂ] H}
    (hB : IsSelfAdjoint B)
    (ha : ∀ x ∈ spectrum ℝ B, 1 - alpha * x ≠ 0)
    (hb : ∀ x ∈ spectrum ℝ B, 1 - beta * x ≠ 0) :
    suzukiInverseDefectOperator alpha beta B
      = (alpha * beta) • (B * (cfc (suzukiInverseShiftFactor alpha) B
          * cfc (suzukiInverseShiftFactor beta) B)) := by
  have hca : ContinuousOn (suzukiInverseShiftFactor alpha) (spectrum ℝ B) :=
    continuousOn_suzukiInverseShiftFactor alpha ha
  have hcb : ContinuousOn (suzukiInverseShiftFactor beta) (spectrum ℝ B) :=
    continuousOn_suzukiInverseShiftFactor beta hb
  have hid : ContinuousOn (fun x : ℝ => x) (spectrum ℝ B) := continuousOn_id
  have hprod : cfc (fun x => suzukiInverseShiftFactor alpha x
      * suzukiInverseShiftFactor beta x) B
      = cfc (suzukiInverseShiftFactor alpha) B * cfc (suzukiInverseShiftFactor beta) B :=
    cfc_mul _ _ B hca hcb
  have hprod2 : cfc (fun x => x * (suzukiInverseShiftFactor alpha x
      * suzukiInverseShiftFactor beta x)) B
      = cfc (fun x : ℝ => x) B * cfc (fun x => suzukiInverseShiftFactor alpha x
        * suzukiInverseShiftFactor beta x) B :=
    cfc_mul _ _ B hid (hca.mul hcb)
  have hcongr : suzukiInverseDefectOperator alpha beta B
      = cfc (fun x => alpha * beta * (x * (suzukiInverseShiftFactor alpha x
        * suzukiInverseShiftFactor beta x))) B := by
    rw [suzukiInverseDefectOperator]
    exact cfc_congr fun x hx =>
      suzukiInverseKreinDefect_eq_product (ha x hx) (hb x hx)
  have hconst : cfc (fun x => alpha * beta * (x * (suzukiInverseShiftFactor alpha x
      * suzukiInverseShiftFactor beta x))) B
      = (alpha * beta) • cfc (fun x => x * (suzukiInverseShiftFactor alpha x
        * suzukiInverseShiftFactor beta x)) B :=
    cfc_const_mul (alpha * beta) _ B (hid.mul (hca.mul hcb))
  have hidB : cfc (fun x : ℝ => x) B = B := cfc_id ℝ B
  rw [hcongr, hconst, hprod2, hprod, hidB]

/-- **`(12)`, the kernel identity.**  The Gram kernel of the defect plus the Gram kernel of its
negative part is the Gram kernel of its positive part.  Positivity of the sum is then automatic
from positivity of `D_+`. -/
theorem gram_add_negPart_eq_posPart (alpha beta : ℝ) (B : H →L[ℂ] H) (v w : H) :
    inner ℂ (suzukiInverseDefectOperator alpha beta B w) v
        + inner ℂ ((suzukiInverseDefectOperator alpha beta B)⁻ w) v
      = inner ℂ ((suzukiInverseDefectOperator alpha beta B)⁺ w) v := by
  rw [← inner_add_left]
  congr 1
  have h := suzukiInverseDefect_add_negPart alpha beta B
  rw [← h]
  rfl

/-! ## `(T1)` of the finite-Morse card: the jet square dominates the negative part -/

/-- **Finite-Morse `(T1)`, second half.**  A resolvent-jet square that completes the affine Krein
defect to a positive operator dominates the negative part of that defect.  Together with
`suzukiFiniteMorse_operatorCompletion_nonneg` this is the full statement
`C = D_- + P_+ C >= D_-`. -/
theorem negPart_operatorKreinDefect_le_jetSquare {alpha beta rho : ℝ} {R : H →L[ℂ] H}
    (hR : IsSelfAdjoint R) (q : ℝ[X])
    (hden : ∀ x ∈ spectrum ℝ R,
      (rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1) ≠ 0)
    (hdom : ∀ x ∈ spectrum ℝ R,
      0 ≤ suzukiKreinResolventWeight alpha beta rho x + (q.eval x) ^ 2) :
    (suzukiOperatorKreinDefect alpha beta rho R)⁻ ≤ suzukiResolventJetSquare q R := by
  have hw : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R) :=
    continuousOn_suzukiKreinResolventWeight alpha beta rho hden
  have hpoly : ContinuousOn (fun x : ℝ => q.eval x) (spectrum ℝ R) :=
    (Polynomial.continuous_aeval q).continuousOn
  have hwneg : ContinuousOn (fun x => (suzukiKreinResolventWeight alpha beta rho x)⁻)
      (spectrum ℝ R) := hw.neg.sup continuousOn_const
  have hsq : ContinuousOn (fun x : ℝ => (q.eval x) ^ 2) (spectrum ℝ R) := hpoly.pow 2
  have hneg : (suzukiOperatorKreinDefect alpha beta rho R)⁻
      = cfc (fun x => (suzukiKreinResolventWeight alpha beta rho x)⁻) R := by
    rw [suzukiOperatorKreinDefect]
    exact negPart_cfc hR hw
  have hC : suzukiResolventJetSquare q R = cfc (fun x : ℝ => (q.eval x) ^ 2) R := by
    rw [cfc_pow (fun x : ℝ => q.eval x) 2 R hpoly, suzukiResolventJetSquare, cfc_polynomial q R]
  rw [hneg, hC, ← sub_nonneg,
    ← cfc_sub (fun x : ℝ => (q.eval x) ^ 2)
      (fun x => (suzukiKreinResolventWeight alpha beta rho x)⁻) R hsq hwneg]
  refine (cfc_nonneg_iff _ R (hsq.sub hwneg) hR).mpr ?_
  intro x hx
  exact sub_nonneg.mpr (negPart_le_of_add_nonneg (sq_nonneg _) (hdom x hx))

end

end RHTower
