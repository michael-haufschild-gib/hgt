import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Fixed

/-!
# Fixed fractions are fractions of invariants

An element of a fraction field fixed by a finite group of ring automorphisms of the base is a ratio
of invariant elements of the base: multiply numerator and denominator by the other translates of the
denominator, which makes the denominator invariant and forces the numerator to be so too.

This is what identifies the fixed field of a group acting on a rational function field with the
fraction field of the invariant polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {R : Type v} [CommRing R] [IsDomain R] [MulSemiringAction G R]
variable {L : Type w} [Field L] [Algebra R L] [IsFractionRing R L] [MulSemiringAction G L]
  [SMulDistribClass G R L]

omit [IsDomain R] [Fintype G] [IsFractionRing R L] in
/-- The action is compatible with the embedding of the base. -/
theorem smul_algebraMap_eq (g : G) (r : R) :
    g • algebraMap R L r = algebraMap R L (g • r) := by
  have h := smul_distrib_smul g r (1 : L)
  rw [smul_one, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  exact h

omit [IsDomain R] in
/-- The product of all translates of an element is invariant. -/
theorem prod_smul_invariant (q : R) (h : G) :
    h • (∏ g : G, g • q) = ∏ g : G, g • q := by
  classical
  rw [Finset.smul_prod']
  refine Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  rw [smul_smul]
  rfl

/-- The product of all translates of a nonzero element is nonzero. -/
theorem prod_smul_ne_zero {q : R} (hq : q ≠ 0) : (∏ g : G, g • q) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 (fun g _ => ?_)
  intro hc
  exact hq (by simpa using congrArg (fun y => g⁻¹ • y) hc)

/-- **A fixed element of the fraction field is a ratio of invariants.** -/
theorem exists_invariant_ratio (x : L) (hx : ∀ g : G, g • x = x) :
    ∃ a b : R, (∀ g : G, g • a = a) ∧ (∀ g : G, g • b = b) ∧ b ≠ 0 ∧
      x = algebraMap R L a / algebraMap R L b := by
  classical
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqL : algebraMap R L q ≠ 0 := fun hc =>
    hq0 (IsFractionRing.injective R L (by rw [hc, map_zero]))
  set P : R := ∏ g ∈ Finset.univ.erase (1 : G), g • q with hPdef
  have hbq : (∏ g : G, g • q) = q * P := by
    rw [hPdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), one_smul]
  have hbne : (∏ g : G, g • q) ≠ 0 := prod_smul_ne_zero hq0
  have hbL : algebraMap R L (∏ g : G, g • q) ≠ 0 := fun hc =>
    hbne (IsFractionRing.injective R L (by rw [hc, map_zero]))
  have hax : algebraMap R L (p * P)
      = algebraMap R L p / algebraMap R L q * algebraMap R L (∏ g : G, g • q) := by
    rw [hbq, map_mul, map_mul, div_mul_eq_mul_div, mul_comm (algebraMap R L q),
      ← mul_assoc, mul_div_assoc, div_self hqL, mul_one]
  refine ⟨p * P, ∏ g : G, g • q, ?_, fun h => prod_smul_invariant q h, hbne, ?_⟩
  · intro g
    refine IsFractionRing.injective R L ?_
    rw [← smul_algebraMap_eq, hax, smul_mul', hx g, smul_algebraMap_eq,
      prod_smul_invariant q g, ← hax]
  · rw [hax, mul_div_assoc, div_self hbL, mul_one]

end GaloisForLFunctions.HTGeometry
