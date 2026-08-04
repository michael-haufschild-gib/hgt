import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Fixed

/-!
# An invariant fraction is a ratio of invariants

A finite group acting on a domain acts on its fraction field, and the invariants of the fraction field
are no larger than the fractions of invariants: multiplying numerator and denominator by the other
translates of the denominator makes the denominator a norm, hence invariant, and then the numerator is
invariant because the fraction is.

This is the algebraic content of "the function field of a quotient by a finite group is the field of
invariant functions", with no geometry: it needs only a domain, a finite group of ring automorphisms,
and a fraction field.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {B L : Type*} [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G B] [MulSemiringAction G L]

/-- The norm of an element: the product of all its translates. -/
def actionNorm (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B] (b : B) : B :=
  ∏ g : G, g • b

omit [IsDomain B] [DecidableEq G] in
/-- **The norm is invariant.**  Translating permutes the factors. -/
theorem smul_actionNorm (b : B) (h : G) : h • actionNorm G b = actionNorm G b := by
  classical
  show h • (∏ g : G, g • b) = ∏ g : G, g • b
  rw [Finset.smul_prod']
  refine Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [Equiv.coe_mulLeft, mul_smul]

omit [DecidableEq G] in
/-- **The norm of a nonzero element is nonzero.** -/
theorem actionNorm_ne_zero {b : B} (hb : b ≠ 0) : actionNorm G b ≠ 0 := by
  show (∏ g : G, g • b) ≠ 0
  exact Finset.prod_ne_zero_iff.2 fun g _ => (smul_ne_zero_iff_ne g).2 hb

omit [IsDomain B] in
/-- The norm, split off its first factor. -/
theorem actionNorm_eq_mul (b : B) : actionNorm G b = b * ∏ g ∈ (univ : Finset G).erase 1, g • b := by
  classical
  show (∏ g : G, g • b) = _
  rw [← Finset.mul_prod_erase (univ : Finset G) (fun g : G => g • b) (mem_univ 1), one_smul]

variable (hcompat : ∀ (g : G) (b : B), g • (algebraMap B L b) = algebraMap B L (g • b))

include hcompat in
/-- **An invariant fraction is a ratio of invariants.**  Multiplying through by the remaining
translates of the denominator turns it into a norm, which is invariant; the numerator is then
invariant because the fraction is. -/
theorem exists_invariant_ratio_of_isInvariant (x : L) (hx : ∀ g : G, g • x = x) :
    ∃ a n : B, (∀ g : G, g • a = a) ∧ (∀ g : G, g • n = n) ∧ n ≠ 0 ∧
      x = algebraMap B L a / algebraMap B L n := by
  classical
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := B) (K := L) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqL : algebraMap B L q ≠ 0 := by
    simpa using (IsFractionRing.to_map_eq_zero_iff (R := B) (K := L)).not.2 hq0
  set c : B := ∏ g ∈ (univ : Finset G).erase 1, g • q with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Finset.prod_ne_zero_iff.2 fun g _ => (smul_ne_zero_iff_ne g).2 hq0
  have hcL : algebraMap B L c ≠ 0 := by
    simpa using (IsFractionRing.to_map_eq_zero_iff (R := B) (K := L)).not.2 hc0
  refine ⟨p * c, actionNorm G q, ?_, fun g => smul_actionNorm q g, actionNorm_ne_zero hq0, ?_⟩
  · -- the numerator is invariant, because the fraction and the norm are
    intro g
    refine IsFractionRing.injective B L ?_
    have hnum : algebraMap B L (p * c) = x * algebraMap B L (actionNorm G q) := by
      rw [actionNorm_eq_mul, map_mul, ← hpq, map_mul, ← hc]
      field_simp
    rw [← hcompat, hnum, smul_mul', hx g, hcompat, smul_actionNorm]
  · rw [actionNorm_eq_mul, map_mul, map_mul, ← hpq, ← hc]
    field_simp

include hcompat in
/-- **A subfield containing the invariant ring contains every invariant.**  Since an invariant
fraction is a ratio of invariant ring elements, a subfield through which all invariant ring elements
factor already contains the whole invariant field.  This is the field-level half of "the functions on
a quotient are the invariant functions": the geometric input it leaves is purely ring-level. -/
theorem mem_of_invariant_of_invariant_ring_le {C : Type*} [Field C] [Algebra C L]
    (M : IntermediateField C L)
    (hring : ∀ b : B, (∀ g : G, g • b = b) → algebraMap B L b ∈ M)
    (x : L) (hx : ∀ g : G, g • x = x) : x ∈ M := by
  obtain ⟨a, n, ha, hn, -, rfl⟩ := exists_invariant_ratio_of_isInvariant hcompat x hx
  exact div_mem (hring a ha) (hring n hn)

include hcompat in
/-- **The invariant field is exactly the subfield of invariant ring elements.** -/
theorem eq_fixedPoints_of_invariant_ring {C : Type*} [Field C] [Algebra C L]
    (M : IntermediateField C L)
    (hring : ∀ b : B, (∀ g : G, g • b = b) → algebraMap B L b ∈ M)
    (hM : ∀ (g : G) (x : L), x ∈ M → g • x = x) :
    {x : L | ∀ g : G, g • x = x} = (M : Set L) := by
  ext x
  constructor
  · exact mem_of_invariant_of_invariant_ring_le hcompat M hring x
  · intro hx g
    exact hM g x hx

end

end GaloisForLFunctions.HTGeometry
