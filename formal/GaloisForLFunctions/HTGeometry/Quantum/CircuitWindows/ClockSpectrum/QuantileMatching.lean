import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # Matching a phase spectrum to a clock with equal multiplicities -/
open Set Finset
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

/-- Number of points strictly below a specified angular threshold, in turns. -/
def countBelow {n : ℕ} (x : Fin n→ℝ) (a : ℝ) : ℕ := (univ.filter (fun i => x i<a)).card

private theorem count_perm {n : ℕ} (x : Fin n→ℝ) (e : Equiv.Perm (Fin n)) (a : ℝ) :
    countBelow (x ∘ e) a=countBelow x a := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  · exact fun _ _ _ _ h => e.injective h
  · intro j hj
    refine ⟨e.symm j,mem_filter.mpr ⟨mem_univ _,?_⟩,e.apply_symm_apply j⟩
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using (mem_filter.mp hj).2

/-- If the counts at the Q bin boundaries are within one bin's mass
of their uniform values, the order statistics match the clock to
within two bins. Each of the Q clock phases is repeated m times. -/
theorem match_repeated_clock {Q m : ℕ} (hQ : 0 < Q) (hm : 0 < m)
    (x : Fin (Q*m)→ℝ) (hx : ∀ i, x i∈Icc 0 1)
    (h : ∀ b : ℕ, b ≤ Q →
      b*m ≤ countBelow x (b/(Q:ℝ))+m ∧ countBelow x (b/(Q:ℝ)) ≤ b*m+m) :
    ∃ p : Equiv.Perm (Fin (Q*m)), ∀ i : Fin (Q*m),
      |x (p i)-((i.val/m:ℕ):ℝ)/Q| ≤ 2/Q := by
  let p := Tuple.sort x
  let y := x ∘ p
  have hs : Monotone y := Tuple.monotone_sort x
  have hp : 0 < (Q:ℝ) := Nat.cast_pos.mpr hQ
  refine ⟨p,fun i => ?_⟩
  let b := i.val/m
  have hi : i.val < Q*m := i.isLt
  have hb : b < Q := (Nat.div_lt_iff_lt_mul hm).mpr hi
  have hlow : b*m ≤ i.val := Nat.div_mul_le_self _ _
  have hhigh : i.val < (b+1)*m := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self b)
  have hl : (b:ℝ)/Q-2/Q ≤ y i := by
    by_cases hz : b=0
    · rw [hz,Nat.cast_zero,zero_div,zero_sub]
      exact (neg_nonpos.mpr (by positivity)).trans (hx (p i)).1
    have hcount := (h (b-1) (by omega)).2
    have hbm : (b-1)*m+m=b*m := by rw [←Nat.succ_mul,show b-1+1=b by omega]
    rw [hbm,←count_perm x p] at hcount
    have hy : ((b-1:ℕ):ℝ)/Q ≤ y i := by
      by_contra! hh
      have ht := (Tuple.lt_card_lt_iff_apply_lt_of_monotone hs).mpr hh
      exact (not_lt_of_ge (hcount.trans hlow)) ht
    apply le_trans _ hy
    rw [Nat.cast_sub (by omega : 1 ≤ b),Nat.cast_one,←sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  have hu : y i ≤ (b:ℝ)/Q+2/Q := by
    by_cases hh : b+2 ≤ Q
    · have hcount := (h (b+2) hh).1
      have hstep : (b+2)*m=(b+1)*m+m := Nat.succ_mul _ _
      rw [hstep,←count_perm x p] at hcount
      have ht : i.val < countBelow y (((b+2:ℕ):ℝ)/Q) := hhigh.trans_le (Nat.le_of_add_le_add_right hcount)
      have hy := (Tuple.lt_card_lt_iff_apply_lt_of_monotone hs).mp ht
      simpa only [Nat.cast_add,Nat.cast_ofNat,add_div] using hy.le
    · apply (hx (p i)).2.trans
      rw [←add_div]
      exact (one_le_div hp).mpr (by exact_mod_cast (show Q ≤ b+2 by omega))
  exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

#print axioms match_repeated_clock
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
