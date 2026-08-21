/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Strict operator concavity of the square root

Mathlib knows that `CFC.sqrt` is operator concave on the positive cone of a C⋆-algebra.  This file
adds the *strictness*: equality in the concavity inequality for a genuine convex combination forces
the two arguments to coincide.  This is the operator core of Kim–Mer–Pálfia (arXiv:2607.29142),
Theorem 3.2, whose proof reads exactly as follows: square the equality, use
`α - α² = β - β² = αβ`, and conclude `(√A - √B)² = 0`.
-/

open scoped NNReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- A self-adjoint element with vanishing square vanishes. -/
theorem eq_zero_of_isSelfAdjoint_of_mul_self_eq_zero {x : A} (hx : IsSelfAdjoint x)
    (h : x * x = 0) : x = 0 := by
  have hn : ‖x‖ * ‖x‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hx.star_eq, h, norm_zero]
  simpa using hn

/-- **Operator concavity of the square root** in the two-point form. -/
theorem smul_sqrt_add_smul_sqrt_le {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    α • CFC.sqrt a + β • CFC.sqrt b ≤ CFC.sqrt (α • a + β • b) :=
  CFC.concaveOn_sqrt.2 ha hb hα hβ hαβ

/-- **Strict operator concavity of the square root**: equality forces `a = b`. -/
theorem eq_of_sqrt_smul_add_eq {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (heq : CFC.sqrt (α • a + β • b) = α • CFC.sqrt a + β • CFC.sqrt b) : a = b := by
  have hznn : (0 : A) ≤ α • a + β • b := add_nonneg (smul_nonneg hα.le ha) (smul_nonneg hβ.le hb)
  have hsa : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
  have hsb : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
  have hsq : α • a + β • b
      = (α * α) • a + (α * β) • (CFC.sqrt a * CFC.sqrt b)
        + (β * α) • (CFC.sqrt b * CFC.sqrt a) + (β * β) • b := by
    have hz := CFC.sqrt_mul_sqrt_self (α • a + β • b) hznn
    rw [heq] at hz
    rw [← hz, add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
      smul_mul_smul_comm, smul_mul_smul_comm, hsa, hsb]
    abel
  have e1 : α * α = α - α * β := by nlinarith [hαβ]
  have e2 : β * β = β - α * β := by nlinarith [hαβ]
  have e3 : β * α = α * β := mul_comm _ _
  rw [e1, e2, e3] at hsq
  have hcancel : (α * β) • (a + b)
      = (α * β) • (CFC.sqrt a * CFC.sqrt b + CFC.sqrt b * CFC.sqrt a) := by
    have hs : α • a + β • b - ((α - α * β) • a + (α * β) • (CFC.sqrt a * CFC.sqrt b)
        + (α * β) • (CFC.sqrt b * CFC.sqrt a) + (β - α * β) • b) = 0 := sub_eq_zero_of_eq hsq
    rw [sub_smul, sub_smul] at hs
    have hid : (α * β) • (a + b)
        - (α * β) • (CFC.sqrt a * CFC.sqrt b + CFC.sqrt b * CFC.sqrt a)
        = α • a + β • b - ((α • a - (α * β) • a) + (α * β) • (CFC.sqrt a * CFC.sqrt b)
          + (α * β) • (CFC.sqrt b * CFC.sqrt a) + (β • b - (α * β) • b)) := by
      rw [smul_add, smul_add]; abel
    rw [← sub_eq_zero, hid]
    exact hs
  have hne : α * β ≠ 0 := by positivity
  have hkey : a + b = CFC.sqrt a * CFC.sqrt b + CFC.sqrt b * CFC.sqrt a :=
    smul_right_injective A hne hcancel
  have hzero : (CFC.sqrt a - CFC.sqrt b) * (CFC.sqrt a - CFC.sqrt b) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hsa, hsb]
    rw [show a - CFC.sqrt a * CFC.sqrt b - (CFC.sqrt b * CFC.sqrt a - b)
      = a + b - (CFC.sqrt a * CFC.sqrt b + CFC.sqrt b * CFC.sqrt a) by abel, hkey, sub_self]
  have hsasub : IsSelfAdjoint (CFC.sqrt a - CFC.sqrt b) :=
    ((CFC.sqrt_nonneg a).isSelfAdjoint).sub ((CFC.sqrt_nonneg b).isSelfAdjoint)
  have hsqeq : CFC.sqrt a = CFC.sqrt b :=
    sub_eq_zero.mp (eq_zero_of_isSelfAdjoint_of_mul_self_eq_zero hsasub hzero)
  rw [← hsa, ← hsb, hsqeq]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
