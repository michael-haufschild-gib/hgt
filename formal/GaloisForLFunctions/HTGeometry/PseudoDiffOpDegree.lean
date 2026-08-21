import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField

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
    ordQ (r /ₒ s) = if r = 0 then 0 else (degree r : ℤ) - (degree (s : DiffOp K) : ℤ) := rfl

@[simp] theorem ordQ_zero : ordQ (0 : PseudoDiffOp K) = 0 := by
  rw [show (0 : PseudoDiffOp K) = (0 : DiffOp K) /ₒ 1 from (zero_oreDiv 1).symm, ordQ_oreDiv]
  simp

theorem ordQ_numeratorRingHom (p : DiffOp K) :
    ordQ (numeratorRingHom p : PseudoDiffOp K) = if p = 0 then 0 else (degree p : ℤ) := by
  rw [show (numeratorRingHom p : PseudoDiffOp K) = p /ₒ 1 from rfl, ordQ_oreDiv]
  by_cases hp : p = 0
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp]
    have h1 : degree ((1 : (DiffOp K)⁰) : DiffOp K) = 0 := degree_one
    rw [h1]
    simp

@[simp] theorem ordQ_one : ordQ (1 : PseudoDiffOp K) = 0 := by
  rw [show (1 : PseudoDiffOp K) = (1 : DiffOp K) /ₒ 1 from rfl, ordQ_oreDiv, if_neg one_ne_zero,
    degree_one]
  have h1 : degree ((1 : (DiffOp K)⁰) : DiffOp K) = 0 := degree_one
  rw [h1]

/-- **The degree is additive on the Ore field.** -/
theorem ordQ_mul (x y : PseudoDiffOp K) : ordQ (x * y) = ordQ x + ordQ y := by
  refine OreLocalization.ind (fun r₁ s₁ => ?_) x
  refine OreLocalization.ind (fun r₂ s₂ => ?_) y
  have hs₁ : (s₁ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₁.2
  have hs₂ : (s₂ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₂.2
  rw [oreDiv_mul_oreDiv, ordQ_oreDiv, ordQ_oreDiv, ordQ_oreDiv]
  by_cases hr₁ : r₁ = 0
  · subst hr₁
    have hnum : oreNum (0 : DiffOp K) s₂ * (s₂ : DiffOp K)
        = (oreDenom (0 : DiffOp K) s₂ : DiffOp K) * 0 := (ore_eq (0 : DiffOp K) s₂).symm
    rw [mul_zero] at hnum
    have hnum0 : oreNum (0 : DiffOp K) s₂ = 0 := by
      rcases mul_eq_zero.mp hnum with h | h
      · exact h
      · exact absurd h hs₂
    rw [hnum0, zero_mul, if_pos rfl, if_pos rfl]
    ring
  by_cases hr₂ : r₂ = 0
  · subst hr₂
    rw [mul_zero, if_pos rfl, if_pos rfl]
    ring
  have hsd : (oreDenom r₁ s₂ : DiffOp K) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (oreDenom r₁ s₂).2
  have hore := ore_eq r₁ s₂
  have hnum0 : oreNum r₁ s₂ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hore
    exact (mul_ne_zero hsd hr₁) hore
  have hprod : oreNum r₁ s₂ * r₂ ≠ 0 := mul_ne_zero hnum0 hr₂
  rw [if_neg hprod, if_neg hr₁, if_neg hr₂]
  have hdeg : (degree (oreNum r₁ s₂) : ℤ) - (degree (oreDenom r₁ s₂ : DiffOp K) : ℤ)
      = (degree r₁ : ℤ) - (degree (s₂ : DiffOp K) : ℤ) := by
    have h := congrArg degree hore
    rw [degree_mul hsd hr₁, degree_mul hnum0 hs₂] at h
    push_cast [h]
    ring_nf
    omega
  have hnumer : degree (oreNum r₁ s₂ * r₂) = degree (oreNum r₁ s₂) + degree r₂ :=
    degree_mul hnum0 hr₂
  have hdenom : degree (((oreDenom r₁ s₂ * s₁ : (DiffOp K)⁰) : DiffOp K))
      = degree (oreDenom r₁ s₂ : DiffOp K) + degree (s₁ : DiffOp K) := by
    show degree ((oreDenom r₁ s₂ : DiffOp K) * (s₁ : DiffOp K)) = _
    exact degree_mul hsd hs₁
  rw [hnumer, hdenom]
  push_cast
  linarith [hdeg]

theorem ordQ_inv (x : PseudoDiffOp K) (hx : x ≠ 0) : ordQ x⁻¹ = -ordQ x := by
  have h := ordQ_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, ordQ_one] at h
  linarith

end

end DiffOp

end GaloisForLFunctions.HTGeometry
