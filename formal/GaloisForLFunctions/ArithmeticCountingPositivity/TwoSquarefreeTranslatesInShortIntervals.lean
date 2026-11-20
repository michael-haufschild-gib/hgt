import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicator
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Simultaneous squarefree translates in short intervals

Two integer windows of the same length have a positive proportion of
squarefree sites in the same relative positions once their length
exceeds forty times the square root of their greatest endpoint.
There is no bound on the distance between the windows.
-/
noncomputable section
open Finset _root_.RHTower.Sieve
namespace GaloisForLFunctions.ArithmeticCountingPositivity

/-- Relative positions in a length-L interval at which two prescribed
translates are both squarefree. -/
def pairedSquarefreeSites (a b L : ℕ) :=
  (Icc 1 L).filter fun k => Squarefree (a+k) ∧ Squarefree (b+k)

private theorem shifted_sites_card (a L : ℕ) :
    ((Icc 1 L).filter (fun k => Squarefree (a+k))).card =
      ((Ioc a (a+L)).filter Squarefree).card := by
  classical
  refine card_bij (fun k _ => a+k) ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk,hs⟩ := mem_filter.mp hk
    obtain ⟨hk1,hkL⟩ := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hs⟩
  · exact fun _ _ _ _ => Nat.add_left_cancel
  · intro n hn
    obtain ⟨hn,hs⟩ := mem_filter.mp hn
    obtain ⟨han,hnL⟩ := mem_Ioc.mp hn
    have h : a+(n-a)=n := by omega
    exact ⟨n-a,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,h.symm ▸ hs⟩,h⟩

/-- The uniform pair coefficient is twice the squarefree density
minus one. The error is the sum of the two local sieve errors. -/
theorem simultaneous_squarefree_interval_lower {a b L R : ℕ} (hR : 1 ≤ R)
    (ha : a+L ≤ R^2) (hb : b+L ≤ R^2) :
    (12/Real.pi^2-1)*(L:ℝ)-2*((R:ℝ)+(L:ℝ)/R) ≤
      ((pairedSquarefreeSites a b L).card:ℝ) := by
  classical
  let S := (Icc 1 L).filter fun k => Squarefree (a+k)
  let T := (Icc 1 L).filter fun k => Squarefree (b+k)
  have hlocal (c : ℕ) (hc : c+L ≤ R^2) : (L:ℝ)*(6/Real.pi^2)-((R:ℝ)+(L:ℝ)/R) ≤
      (((Icc 1 L).filter (fun k => Squarefree (c+k))).card:ℝ) := by
    have he := abs_window_squarefree_sub_le hR hc
    rw [sum_moebius_sq_eq_card,squarefreeDensity_eq,←shifted_sites_card] at he
    linarith only [(abs_le.mp he).1]
  have hsubset : S ∪ T ⊆ Icc 1 L := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcount := card_le_card hsubset
  have hp : S ∩ T = pairedSquarefreeSites a b L := by
    ext k
    simp only [S,T,pairedSquarefreeSites,mem_inter,mem_filter,and_assoc]
    tauto
  have hs := card_union_add_card_inter S T
  rw [hp] at hs
  rw [Nat.card_Icc] at hcount
  have hn : S.card+T.card ≤ L+(pairedSquarefreeSites a b L).card := by omega
  have hcast : (S.card:ℝ)+(T.card:ℝ) ≤ L+((pairedSquarefreeSites a b L).card:ℝ) := by exact_mod_cast hn
  have hA : _ ≤ (S.card:ℝ) := hlocal a ha
  have hB : _ ≤ (T.card:ℝ) := hlocal b hb
  linarith only [hcast,hA,hB]

/-- At least one in ten relative positions works for both shifts at
length forty times the square root scale, with explicit constants. -/
theorem tenth_of_two_shifted_windows {a b L R : ℕ} (hR : 1 ≤ R)
    (ha : a+L ≤ R^2) (hb : b+L ≤ R^2) (hL : 40*R ≤ L) :
    (L:ℝ)/10 ≤ ((pairedSquarefreeSites a b L).card:ℝ) := by
  have hp : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have h10 : Real.pi^2 ≤ 10 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
    linarith only [h]
  have hc : (1/5:ℝ) ≤ 12/Real.pi^2-1 := by
    have hh := (le_div_iff₀ hp).mpr (show (6/5:ℝ)*Real.pi^2 ≤ 12 by linarith only [h10])
    linarith only [hh]
  have hrp : 0 < (R:ℝ) := Nat.cast_pos.mpr hR
  have hrl : (L:ℝ)/R ≤ R := (div_le_iff₀ hrp).mpr (by
    have hx : L ≤ R^2 := (Nat.le_add_left L a).trans ha
    exact_mod_cast (show L ≤ R*R by simpa only [sq] using hx))
  have h40 : 40*(R:ℝ) ≤ L := by exact_mod_cast hL
  have hlow := simultaneous_squarefree_interval_lower hR ha hb
  linarith only [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg L),h40,hrl,hlow]

#print axioms simultaneous_squarefree_interval_lower
#print axioms tenth_of_two_shifted_windows
end GaloisForLFunctions.ArithmeticCountingPositivity
