import GaloisForLFunctions.RHTower.SquarefreeLowerDensity

/-!
# A squarefree majority at every cutoff

Separate 2 and 3 in the prime-square union bound. For the remaining
possible primes, the reciprocal squares of 5,7,9,… telescope against
the two adjacent reciprocal even integers. The bound is uniform even
before the squarefree counting asymptotic becomes effective.
-/
noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCountingPositivity

/-- Reciprocal-square mass on the odd progression from five onward. -/
theorem odd_square_tail_reciprocals (N : ℕ) :
    (∑ j ∈ range N, 1/(2*(j:ℝ)+5)^2) ≤ 1/8-1/(4*((N:ℝ)+2)) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    have h1 : 0<(n:ℝ)+2 := by positivity
    have h2 : 0<(n:ℝ)+3 := by positivity
    have h := one_div_le_one_div_of_le (mul_pos (by positivity : 0<4*((n:ℝ)+2)) h2)
      (show 4*((n:ℝ)+2)*((n:ℝ)+3) ≤ (2*(n:ℝ)+5)^2 by nlinarith only [])
    have hd : 1/(4*((n:ℝ)+2)*((n:ℝ)+3)) =
        1/(4*((n:ℝ)+2))-1/(4*((n:ℝ)+3)) := by field_simp; ring
    rw [hd] at h
    rw [Finset.sum_range_succ,Nat.cast_succ,show (n:ℝ)+1+2=n+3 by ring]
    linarith only [ih,h]

private def squareMultiples (N m : ℕ) := (Icc 1 N).filter fun n => m^2 ∣ n

private theorem square_multiple_price (N m : ℕ) :
    ((squareMultiples N m).card:ℝ) ≤ (N:ℝ)*(1/(m:ℝ)^2) := by
  rw [squareMultiples,_root_.RHTower.card_filter_dvd]
  have h : ((N/m^2:ℕ):ℝ) ≤ (N:ℝ)/((m^2:ℕ):ℝ) := Nat.cast_div_le
  simpa only [Nat.cast_pow,div_eq_mul_inv,one_mul] using h

/-- At every cutoff at least 37/72 of the integers in [1,N] are
squarefree. Separating 3 gives a fixed surplus above one half. -/
theorem squarefree_majority_all_cutoffs (N : ℕ) :
    (37/72:ℝ)*N ≤ (((Icc 1 N).filter Squarefree).card:ℝ) := by
  classical
  let B := (Icc 1 N).filter fun n => ¬Squarefree n
  let R := (range N).biUnion fun j => squareMultiples N (2*j+5)
  have cover : B ⊆ squareMultiples N 2 ∪ squareMultiples N 3 ∪ R := by
    intro n hn
    obtain ⟨hnI,hbad⟩ := mem_filter.mp hn
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    simp only [not_forall,not_not] at hbad
    obtain ⟨p,hp,hpn⟩ := hbad
    have hmem : n∈squareMultiples N p := mem_filter.mpr ⟨hnI,by simpa only [pow_two] using hpn⟩
    by_cases h2 : p=2
    · exact mem_union_left _ (mem_union_left _ (h2 ▸ hmem))
    by_cases h3 : p=3
    · exact mem_union_left _ (mem_union_right _ (h3 ▸ hmem))
    obtain ⟨t,ht⟩ := hp.odd_of_ne_two h2
    have hpN := (Nat.le_mul_of_pos_left p hp.pos).trans
      ((Nat.le_of_dvd (mem_Icc.mp hnI).1 hpn).trans (mem_Icc.mp hnI).2)
    have hp2 := hp.two_le
    let j := t-2
    have hj : j<N := by dsimp only [j]; omega
    have hrepr : p=2*j+5 := by dsimp only [j]; omega
    exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_range.mpr hj,hrepr ▸ hmem⟩)
  have hR : R.card ≤ ∑ j ∈ range N,(squareMultiples N (2*j+5)).card := card_biUnion_le
  have hb : B.card ≤ (squareMultiples N 2).card+(squareMultiples N 3).card+
      ∑ j ∈ range N,(squareMultiples N (2*j+5)).card :=
    (card_le_card cover).trans ((card_union_le _ _).trans
      (add_le_add (card_union_le _ _) hR))
  have hbr : (B.card:ℝ) ≤ ((squareMultiples N 2).card:ℝ)+((squareMultiples N 3).card:ℝ)+
      ∑ j ∈ range N,((squareMultiples N (2*j+5)).card:ℝ) := by exact_mod_cast hb
  have hm := sum_le_sum (s:=range N) (fun j _ => square_multiple_price N (2*j+5))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hm
  rw [←mul_sum] at hm
  have ht := (odd_square_tail_reciprocals N).trans (sub_le_self _ (by positivity))
  have hs := hm.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N))
  have h2 := square_multiple_price N 2
  have h3 := square_multiple_price N 3
  norm_num at h2 h3
  have hsplitNat : ((Icc 1 N).filter Squarefree).card+B.card=N := by
    dsimp only [B]
    rw [card_filter_add_card_filter_not,Nat.card_Icc]; omega
  have hsplit : (((Icc 1 N).filter Squarefree).card:ℝ)+(B.card:ℝ)=N := by exact_mod_cast hsplitNat
  linarith only [h2,h3,hs,hbr,hsplit]

#print axioms odd_square_tail_reciprocals
#print axioms squarefree_majority_all_cutoffs
end GaloisForLFunctions.ArithmeticCountingPositivity
