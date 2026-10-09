import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry

/-- If every critical point lies in the zero fiber, that fiber has exactly one distinct point. -/
theorem card_roots_eq_one_of_critical_roots_zero {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] [DecidableEq K] (p : K[X]) (hp : 0 < p.natDegree)
    (hcrit : ∀ z, p.derivative.IsRoot z → p.IsRoot z) : p.roots.toFinset.card = 1 := by
  classical
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hpd : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hp.ne'
  have hsum : ∑ a ∈ p.roots.toFinset, p.derivative.roots.count a = p.derivative.roots.card := by
    apply Multiset.sum_count_eq_card
    intro a ha
    exact Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr (hcrit a ((mem_roots hpd).mp ha)))
  have hcounts : ∀ a ∈ p.roots.toFinset,
      p.roots.count a = p.derivative.roots.count a + 1 := by
    intro a ha
    have hra : p.IsRoot a := (mem_roots hp0).mp (Multiset.mem_toFinset.mp ha)
    simp only [count_roots]
    rw [derivative_rootMultiplicity_of_root hra]
    exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr ((rootMultiplicity_pos hp0).mpr hra))).symm
  have hcard : p.roots.card = p.derivative.roots.card + p.roots.toFinset.card := by
    calc
      p.roots.card = ∑ a ∈ p.roots.toFinset, p.roots.count a :=
        (Multiset.toFinset_sum_count_eq _).symm
      _ = ∑ a ∈ p.roots.toFinset, (p.derivative.roots.count a + 1) :=
        Finset.sum_congr rfl hcounts
      _ = p.derivative.roots.card + p.roots.toFinset.card := by
        rw [Finset.sum_add_distrib, hsum]
        simp
  have hrootcard := (IsAlgClosed.splits p).natDegree_eq_card_roots
  have hdrootcard := (IsAlgClosed.splits p.derivative).natDegree_eq_card_roots
  rw [natDegree_derivative] at hdrootcard
  omega

/-- A monic polynomial whose critical values all vanish is a translated pure power. -/
theorem eq_X_sub_C_pow_of_critical_roots_zero {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (p : K[X]) (hp : 0 < p.natDegree) (hm : p.Monic)
    (hcrit : ∀ z, p.derivative.IsRoot z → p.IsRoot z) :
    ∃ a : K, p = (X - C a) ^ p.natDegree := by
  classical
  obtain ⟨_, a, ha⟩ := (Multiset.toFinset_card_eq_one_iff p.roots).mp
    (card_roots_eq_one_of_critical_roots_zero p hp hcrit)
  refine ⟨a, ?_⟩
  have hf := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  rw [ha, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
    Multiset.prod_singleton, ← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hf
  exact hf

/-- Centering eliminates the translation: the zero critical-value fiber is exactly the pure power. -/
theorem eq_X_pow_of_centered_critical_roots_zero {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (p : K[X]) (hp : 0 < p.natDegree) (hm : p.Monic)
    (hc : p.nextCoeff = 0) (hcrit : ∀ z, p.derivative.IsRoot z → p.IsRoot z) :
    p = X ^ p.natDegree := by
  obtain ⟨a, ha⟩ := eq_X_sub_C_pow_of_critical_roots_zero p hp hm hcrit
  have hh := congrArg Polynomial.nextCoeff ha
  rw [hc, (monic_X_sub_C a).nextCoeff_pow, nextCoeff_X_sub_C, nsmul_eq_mul] at hh
  have hdegree : (p.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hz : a = 0 := neg_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_left hdegree)
  simpa only [hz, C_0, sub_zero] using ha

end GaloisForLFunctions.HTGeometry
