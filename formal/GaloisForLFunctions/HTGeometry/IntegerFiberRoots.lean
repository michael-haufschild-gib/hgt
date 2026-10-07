import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact descent of complete integer root multisets

Every occurrence of a complex root is lifted to its integer representative.
The resulting monic integer polynomial retains degree and multiplicities.
If all roots have one residue modulo three, reduction is a translated power.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- Lift every occurrence of a complex root; repeated roots remain repeated. -/
theorem exists_integer_root_multiset (s : Multiset ℂ) (j : ZMod 3)
    (hs : ∀ z ∈ s, ∃ k : ℤ, z = k ∧ (k : ZMod 3) = j) :
    ∃ t : Multiset ℤ, t.map (fun k : ℤ => (k : ℂ)) = s ∧
      ∀ k ∈ t, (k : ZMod 3) = j := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @cons z s ih =>
    obtain ⟨k, hk, hj⟩ := hs z (by simp)
    obtain ⟨t, ht, hlabel⟩ := ih (fun w hw => hs w (by simp [hw]))
    refine ⟨k ::ₘ t, ?_, ?_⟩
    · simp [ht, hk]
    · intro l hl
      rcases Multiset.mem_cons.mp hl with rfl | hl
      · exact hj
      · exact hlabel l hl

/-- A complete residue-class root multiset reduces to a translated power. -/
theorem integer_root_product_mod_three (t : Multiset ℤ) (j : ZMod 3)
    (ht : ∀ k ∈ t, (k : ZMod 3) = j) :
    ((t.map (fun k => (X : ℤ[X]) - C k)).prod).map (Int.castRingHom (ZMod 3)) =
      (X - C j) ^ t.card := by
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons k t ih =>
    have hk := ht k (by simp)
    have hrest := ih (fun l hl => ht l (by simp [hl]))
    simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
      Multiset.card_cons]
    rw [hk, hrest, pow_succ, mul_comm]

/-- Complete integer fibers produce monic integer polynomials with their exact multiplicities. -/
theorem integer_polynomial_of_labeled_complex_roots (f : ℂ[X]) (j : ZMod 3)
    (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, f.eval z = 0 → ∃ k : ℤ, z = k ∧ (k : ZMod 3) = j) :
    ∃ A : ℤ[X], A.Monic ∧ A.natDegree = f.natDegree ∧
      f = C f.leadingCoeff * A.map (Int.castRingHom ℂ) ∧
      A.map (Int.castRingHom (ZMod 3)) = (X - C j) ^ f.natDegree := by
  obtain ⟨t, ht, hlabel⟩ := exists_integer_root_multiset f.roots j
    (fun z hz => hroots z ((Polynomial.mem_roots hf).mp hz))
  let A : ℤ[X] := (t.map (fun k => (X : ℤ[X]) - C k)).prod
  have hcard : t.card = f.natDegree := by
    have h := congrArg Multiset.card ht
    simpa only [Multiset.card_map, (IsAlgClosed.splits f).natDegree_eq_card_roots] using h
  have hmap : A.map (Int.castRingHom ℂ) = (f.roots.map (fun z => (X : ℂ[X]) - C z)).prod := by
    rw [← ht]
    simp [A, Polynomial.map_multiset_prod, Multiset.map_map]
  refine ⟨A, monic_multisetProd_X_sub_C t, ?_, ?_, ?_⟩
  · exact (natDegree_multiset_prod_X_sub_C_eq_card t).trans hcard
  · rw [hmap]
    exact (IsAlgClosed.splits f).eq_prod_roots
  · exact (integer_root_product_mod_three t j hlabel).trans (by rw [hcard])

end
end GaloisForLFunctions.HTGeometry
