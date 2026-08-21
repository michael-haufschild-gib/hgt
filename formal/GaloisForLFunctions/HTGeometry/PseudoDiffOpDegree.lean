import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField
import GaloisForLFunctions.HTGeometry.ShiftedMatrixDegree

/-!
# The degree of a rational pseudodifferential operator

The operator degree is additive on nonzero operators, so it extends to the Ore field of rational
pseudodifferential operators as an integer-valued homomorphism `p/q ↦ deg p − deg q`.  The
well-definedness is the Ore-expansion condition: multiplying numerator and denominator by the same
nonzero operator shifts both degrees equally.

This is the `r = 1` case of the Cartan invariant, and the valuation whose completion carries the
lattice theory of a twisted matrix chain.

* `ordQ`, `ordQ_oreDiv`, `ordQ_zero`, `ordQ_numeratorRingHom`;
* `ordQ_mul` — **additivity**;
* `ordQ_inv`, `ordQ_eq_zero_iff_of_ne_zero`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

open OreLocalization
open scoped OreLocalization
open scoped Classical
open scoped nonZeroDivisors

variable {K : Type u} [Field K] [Differential K]

/-- The degree of a rational pseudodifferential operator. -/
def ordQ : PseudoDiffOp K → ℤ :=
  OreLocalization.liftExpand
    (fun r s => if r = 0 then 0 else (degree r : ℤ) - (degree (s : DiffOp K) : ℤ))
    (by
      intro r t s ht
      have hts : (t * (s : DiffOp K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ht
      have hs : (s : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.2
      have ht0 : t ≠ 0 := by
        intro h
        rw [h, zero_mul] at hts
        exact hts rfl
      by_cases hr : r = 0
      · subst hr
        rw [if_pos rfl, smul_eq_mul, mul_zero, if_pos rfl]
      · have htr : t * r ≠ 0 := mul_ne_zero ht0 hr
        rw [if_neg hr, smul_eq_mul, if_neg htr]
        show ((degree r : ℤ) - (degree (s : DiffOp K) : ℤ))
          = (degree (t * r) : ℤ) - (degree (t * (s : DiffOp K)) : ℤ)
        rw [degree_mul ht0 hr, degree_mul ht0 hs]
        push_cast
        ring)

theorem ordQ_oreDiv (r : DiffOp K) (s : (DiffOp K)⁰) :
    ordQ (OreLocalization.oreDiv r s) = if r = 0 then 0 else (degree r : ℤ) - (degree (s : DiffOp K) : ℤ) := rfl

@[simp] theorem ordQ_zero : ordQ (0 : PseudoDiffOp K) = 0 := by
  rw [show (0 : PseudoDiffOp K) = OreLocalization.oreDiv (0 : DiffOp K) 1 from (zero_oreDiv 1).symm, ordQ_oreDiv]
  simp

theorem ordQ_numeratorRingHom (p : DiffOp K) :
    ordQ (numeratorRingHom p : PseudoDiffOp K) = if p = 0 then 0 else (degree p : ℤ) := by
  rw [show (numeratorRingHom p : PseudoDiffOp K) = OreLocalization.oreDiv p 1 from rfl,
    ordQ_oreDiv]
  by_cases hp : p = 0
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    have h1 : degree ((1 : (DiffOp K)⁰) : DiffOp K) = 0 := degree_one
    rw [h1]
    simp

@[simp] theorem ordQ_one : ordQ (1 : PseudoDiffOp K) = 0 := by
  rw [show (1 : PseudoDiffOp K) = OreLocalization.oreDiv (1 : DiffOp K) 1 from
      OreLocalization.one_def, ordQ_oreDiv, if_neg one_ne_zero, degree_one]
  have h1 : degree ((1 : (DiffOp K)⁰) : DiffOp K) = 0 := degree_one
  rw [h1]
  simp

/-- **The degree is additive on the Ore field.**  The convention `deg 0 = 0` makes the statement
false at zero, so both factors are required nonzero. -/
theorem ordQ_mul : ∀ (x y : PseudoDiffOp K), x ≠ 0 → y ≠ 0 → ordQ (x * y) = ordQ x + ordQ y := by
  refine OreLocalization.ind (fun r₁ s₁ => ?_)
  refine OreLocalization.ind (fun r₂ s₂ => ?_)
  intro h₁ h₂
  have hs₁ : (s₁ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₁.2
  have hs₂ : (s₂ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₂.2
  have hr₁ : r₁ ≠ 0 := by
    intro h
    exact h₁ (by rw [h]; exact OreLocalization.zero_oreDiv s₁)
  have hr₂ : r₂ ≠ 0 := by
    intro h
    exact h₂ (by rw [h]; exact OreLocalization.zero_oreDiv s₂)
  rw [OreLocalization.oreDiv_mul_oreDiv, ordQ_oreDiv, ordQ_oreDiv, ordQ_oreDiv]
  have hsd : (oreDenom r₁ s₂ : DiffOp K) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (oreDenom r₁ s₂).2
  have hore := ore_eq r₁ s₂
  have hnum0 : oreNum r₁ s₂ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hore
    exact (mul_ne_zero hsd hr₁) hore
  have hprod : oreNum r₁ s₂ * r₂ ≠ 0 := mul_ne_zero hnum0 hr₂
  rw [if_neg hprod, if_neg hr₁, if_neg hr₂]
  have hdegeq : degree (oreDenom r₁ s₂ : DiffOp K) + degree r₁
      = degree (oreNum r₁ s₂) + degree (s₂ : DiffOp K) := by
    have h := congrArg degree hore
    rwa [degree_mul hsd hr₁, degree_mul hnum0 hs₂] at h
  have hnumer : degree (oreNum r₁ s₂ * r₂) = degree (oreNum r₁ s₂) + degree r₂ :=
    degree_mul hnum0 hr₂
  have hdenom : degree (((oreDenom r₁ s₂ * s₁ : (DiffOp K)⁰) : DiffOp K))
      = degree (oreDenom r₁ s₂ : DiffOp K) + degree (s₁ : DiffOp K) := by
    show degree ((oreDenom r₁ s₂ : DiffOp K) * (s₁ : DiffOp K)) = _
    exact degree_mul hsd hs₁
  rw [hnumer, hdenom]
  have hcast : ((degree (oreDenom r₁ s₂ : DiffOp K) : ℤ) + (degree r₁ : ℤ))
      = ((degree (oreNum r₁ s₂) : ℤ) + (degree (s₂ : DiffOp K) : ℤ)) := by
    exact_mod_cast hdegeq
  push_cast
  linarith

theorem ordQ_inv (x : PseudoDiffOp K) (hx : x ≠ 0) : ordQ x⁻¹ = -ordQ x := by
  have hinv : x⁻¹ ≠ 0 := inv_ne_zero hx
  have h := ordQ_mul x x⁻¹ hx hinv
  rw [mul_inv_cancel₀ hx, ordQ_one] at h
  linarith

end

end DiffOp

end GaloisForLFunctions.HTGeometry
