import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

/-!
# Primitive reduction of integer polynomial relations

Dividing a nonzero integer relation by its coefficient gcd preserves the
relation and ensures that reduction modulo three has a nonzero coefficient.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {ι : Type*} [Fintype ι]

/-- Remove integer content from a nonzero polynomial relation before reduction modulo three. -/
theorem exists_primitive_integer_polynomial_relation (A : ι → ℤ[X]) (c : ι → ℤ)
    (hc : ∃ i, c i ≠ 0) (hrel : ∑ i, C (c i) * A i = 0) :
    ∃ d : ι → ℤ, Finset.univ.gcd d = 1 ∧ (∃ i, (d i : ZMod 3) ≠ 0) ∧
      ∑ i, C (d i) * A i = 0 := by
  classical
  obtain ⟨i, hi⟩ := hc
  obtain ⟨d, hfac, hprim⟩ := Finset.extract_gcd c ⟨i, Finset.mem_univ i⟩
  let g : ℤ := Finset.univ.gcd c
  have hg : g ≠ 0 := by
    intro hg
    apply hi
    rw [hfac i (Finset.mem_univ i)]
    change g * d i = 0
    rw [hg, zero_mul]
  have hprod : C g * (∑ j, C (d j) * A j) = 0 := by
    rw [Finset.mul_sum]
    calc
      ∑ j, C g * (C (d j) * A j) = ∑ j, C (c j) * A j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfac j hj, map_mul, mul_assoc]
      _ = 0 := hrel
  have hdrel : ∑ j, C (d j) * A j = 0 := (mul_eq_zero.mp hprod).resolve_left
    (fun h => hg (Polynomial.C_eq_zero.mp h))
  have hmod : ∃ j, (d j : ZMod 3) ≠ 0 := by
    by_contra h
    push Not at h
    have hdiv : (3 : ℤ) ∣ Finset.univ.gcd d := Finset.dvd_gcd fun j _ =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (d j) 3).mp (h j)
    rw [hprim] at hdiv
    exact (by decide : ¬ (3 : ℤ) ∣ 1) hdiv
  exact ⟨d, hprim, hmod, hdrel⟩

/-- Every nonzero integer relation has a nonzero relation after primitive reduction. -/
theorem exists_nonzero_mod_three_polynomial_relation (A : ι → ℤ[X]) (c : ι → ℤ)
    (hc : ∃ i, c i ≠ 0) (hrel : ∑ i, C (c i) * A i = 0) :
    ∃ d : ι → ZMod 3, (∃ i, d i ≠ 0) ∧
      ∑ i, C (d i) * (A i).map (Int.castRingHom (ZMod 3)) = 0 := by
  obtain ⟨d, _, hne, hd⟩ := exists_primitive_integer_polynomial_relation A c hc hrel
  refine ⟨fun i => (d i : ZMod 3), hne, ?_⟩
  have h := congrArg (Polynomial.mapRingHom (Int.castRingHom (ZMod 3))) hd
  simpa using h

end GaloisForLFunctions.HTGeometry
