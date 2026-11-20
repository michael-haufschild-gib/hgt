import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePivotalBlockAtTheUnitaryMidpoint
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Boundary measure of the small unitary divisors

On the cube of full prime-power blocks, adding and deleting a block are inverse
moves. The finite birth-and-death balance of Erbar, Huesmann and Stange
(arXiv:2611.22924, equation (2.1) and Corollary 2.5) gives a summation by
parts on the smaller-divisor side. A rank-dependent edge flux counts exactly
where a random ordering of the blocks first crosses the square root.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
noncomputable section

/-- The flux through one prime direction equals the signed sum of its outgoing
and incoming edges over the smaller unitary divisors. Internal edges cancel. -/
theorem unitaryPivot_flux {A : Type*} [AddCommGroup A] {k p : ℕ}
    (hp : p ∈ k.primeFactors) (w : Finset ℕ → A) :
    ∑ S ∈ unitaryPivots k p, w S =
      ∑ S ∈ smallUnitarySubsets k, if p ∈ S then -w (S.erase p) else w S := by
  let P := k.primeFactors.erase p
  have hpP : p ∉ P := notMem_erase _ _
  have hk := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
  let f (S : Finset ℕ) := if (primePowerSubset k S)^2 ≤ k then
    (if p ∈ S then -w (S.erase p) else w S) else 0
  have hl : (∑ S ∈ smallUnitarySubsets k, if p ∈ S then -w (S.erase p) else w S) =
      ∑ S ∈ k.primeFactors.powerset, f S := by
    rw [smallUnitarySubsets, sum_filter]
    exact sum_congr rfl fun S hS => by
      simp only [f, unitarySubset_small_iff_square hk (mem_powerset.mp hS)]
  rw [hl, ← insert_erase hp, sum_powerset_insert hpP, ← sum_add_distrib,
    unitaryPivots, sum_filter]
  refine sum_congr rfl fun S hS => ?_
  have hps : p ∉ S := fun h => hpP (mem_powerset.mp hS h)
  have hblock : 0 < p^k.factorization p := pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hs : primePowerSubset k (insert p S) = p^k.factorization p * primePowerSubset k S :=
    prod_insert hps
  have hle := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left (primePowerSubset k S) hblock) 2
  simp only [f, hs, if_neg hps, mem_insert_self, if_true, erase_insert hps]
  split_ifs <;> first | omega | simp_all only [add_zero, add_neg_cancel, not_le]

/-- Summing all directions turns a radial edge weight into the difference
between the available birth rate and the occupied death rate at each rank. -/
theorem unitaryPivots_radial_flux {A : Type*} [AddCommGroup A] (k : ℕ) (w : ℕ → A) :
    ∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p, w S.card =
      ∑ S ∈ smallUnitarySubsets k,
        ((k.primeFactors.card - S.card) • w S.card - S.card • w (S.card-1)) := by
  calc
    _ = ∑ p ∈ k.primeFactors, ∑ S ∈ smallUnitarySubsets k,
        if p ∈ S then -w (S.erase p).card else w S.card :=
      sum_congr rfl fun p hp => unitaryPivot_flux hp (fun S => w S.card)
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun S hS => ?_
      have hs := mem_powerset.mp (mem_filter.mp hS).1
      rw [← sum_sdiff hs]
      have out : (∑ p ∈ k.primeFactors \ S,
          if p ∈ S then -w (S.erase p).card else w S.card) =
          (k.primeFactors.card - S.card) • w S.card := by
        rw [← card_sdiff_of_subset hs, ← sum_const]
        exact sum_congr rfl fun p hp => if_neg (mem_sdiff.mp hp).2
      have inn : (∑ p ∈ S, if p ∈ S then -w (S.erase p).card else w S.card) =
          S.card • (-w (S.card - 1)) := by
        rw [← sum_const]
        exact sum_congr rfl fun p hp => by rw [if_pos hp, card_erase_of_mem hp]
      rw [out,inn,smul_neg,sub_eq_add_neg]

/-- Integer-valued rank prices in the radial flux formula. -/
theorem unitaryPivots_rank_flux (k : ℕ) (w : ℕ → ℤ) :
    ∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p, w S.card =
      ∑ S ∈ smallUnitarySubsets k,
        (((k.primeFactors.card-S.card : ℕ):ℤ)*w S.card - (S.card:ℤ)*w (S.card-1)) := by
  simpa only [nsmul_eq_mul] using unitaryPivots_radial_flux k w

/-- Number of oriented crossing edges from subsets of rank `j`. -/
def unitaryCrossingsAtRank (k j : ℕ) : ℕ :=
  ∑ p ∈ k.primeFactors, ((unitaryPivots k p).filter (fun S => S.card = j)).card

/-- Number of small unitary divisors using exactly `j` prime-power blocks. -/
def smallUnitaryRankCount (k j : ℕ) : ℕ :=
  ((smallUnitarySubsets k).filter (fun S => S.card = j)).card

/-- A rank loses exactly its outgoing square-root crossings after all births
are counted and the `j+1` parents of each still-small child are removed. -/
theorem unitaryCrossings_rank_balance (k j : ℕ) :
    unitaryCrossingsAtRank k j + (j + 1) * smallUnitaryRankCount k (j + 1) =
      (k.primeFactors.card - j) * smallUnitaryRankCount k j := by
  let w (i : ℕ) : ℤ := if i = j then 1 else 0
  have flux := unitaryPivots_rank_flux k w
  have lhs : (∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p, w S.card) =
      (unitaryCrossingsAtRank k j : ℤ) := by
    simp only [w, sum_boole, unitaryCrossingsAtRank, Nat.cast_sum]
  have rhs (S : Finset ℕ) :
      ((k.primeFactors.card - S.card : ℕ) : ℤ) * w S.card -
        (S.card : ℤ) * w (S.card - 1) =
      (if S.card = j then ((k.primeFactors.card - j : ℕ) : ℤ) else 0) -
        (if S.card = j + 1 then ((j + 1 : ℕ) : ℤ) else 0) := by
    dsimp only [w]
    split_ifs <;> simp_all <;> omega
  rw [lhs, sum_congr rfl (fun S _ => rhs S), sum_sub_distrib, ← sum_filter, ← sum_filter,
    sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at flux
  rw [eq_sub_iff_add_eq] at flux
  simpa only [smallUnitaryRankCount, mul_comm (j+1), mul_comm (k.primeFactors.card-j)] using
    (show unitaryCrossingsAtRank k j + smallUnitaryRankCount k (j+1) * (j+1) =
      smallUnitaryRankCount k j * (k.primeFactors.card-j) by exact_mod_cast flux)

/-- Every ordering of the prime-power blocks crosses the square root exactly once.
A pivotal subset of size `s` accounts for `s! (r-s-1)!` orderings. -/
theorem unitaryPivots_factorial_mass {k : ℕ} (hk : 1 < k) :
    ∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p,
      S.card.factorial * (k.primeFactors.card - S.card - 1).factorial =
      k.primeFactors.card.factorial := by
  let r := k.primeFactors.card
  let w (j : ℕ) : ℤ := (j.factorial : ℤ) * (r-j-1).factorial
  have hr : 0 < r := card_pos.mpr (Nat.nonempty_primeFactors.mpr hk)
  have hempty : ∅ ∈ smallUnitarySubsets k := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (empty_subset _), ?_⟩
    rw [unitarySubset_small_iff_square (by omega) (empty_subset _)]
    simpa only [primePowerSubset, prod_empty, one_pow] using hk.le
  have step (j : ℕ) (hj : j < r) :
      ((r-j : ℕ) : ℤ) * w j - (j : ℤ) * w (j-1) =
        if j = 0 then (r.factorial : ℤ) else 0 := by
    cases j with
    | zero =>
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
      simp [w, hm, Nat.factorial_succ]
    | succ j =>
      have htail : r - j - 1 = (r - (j+1) - 1) + 1 := by omega
      simp only [w, Nat.succ_sub_one, Nat.factorial_succ j, Nat.cast_mul, Nat.succ_ne_zero,
        if_false]
      rw [htail, Nat.factorial_succ]
      have hcount : r - (j+1) = (r - (j+1) - 1) + 1 := by omega
      rw [sub_eq_zero]
      conv_lhs => lhs; rw [hcount]
      push_cast
      ring
  have flux := unitaryPivots_rank_flux k w
  change _ = ∑ S ∈ smallUnitarySubsets k,
    (((r-S.card:ℕ):ℤ) * w S.card - (S.card:ℤ) * w (S.card-1)) at flux
  rw [sum_congr rfl (fun S hS => step S.card (small_unitary_subset_card hk hS).1)] at flux
  simp only [card_eq_zero, sum_ite_eq', hempty, if_true] at flux
  dsimp only [w, r] at flux
  exact_mod_cast flux

#print axioms unitaryPivot_flux
#print axioms unitaryPivots_radial_flux
#print axioms unitaryPivots_rank_flux
#print axioms unitaryCrossings_rank_balance
#print axioms unitaryPivots_factorial_mass

/-- Along a uniformly random ordering of the blocks, the probability of
crossing at the next step is the drop in the fraction of small subsets. -/
theorem unitaryCrossings_probability {k j : ℕ} (hj : j < k.primeFactors.card) :
    (unitaryCrossingsAtRank k j : ℚ) /
        ((k.primeFactors.card-j : ℕ) * (k.primeFactors.card.choose j : ℚ)) =
      (smallUnitaryRankCount k j : ℚ) / k.primeFactors.card.choose j -
      (smallUnitaryRankCount k (j+1) : ℚ) / k.primeFactors.card.choose (j+1) := by
  let r := k.primeFactors.card
  have hpos : 0 < r - j := Nat.sub_pos_of_lt hj
  have hc : 0 < r.choose j := Nat.choose_pos hj.le
  have hd : 0 < r.choose (j+1) := Nat.choose_pos hj
  have step : (r.choose (j+1) : ℚ) * (j+1 : ℕ) = (r.choose j : ℚ) * (r-j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq r j
  have flow : (unitaryCrossingsAtRank k j : ℚ) +
      (j+1 : ℕ) * (smallUnitaryRankCount k (j+1) : ℚ) =
      (r-j : ℕ) * (smallUnitaryRankCount k j : ℚ) := by
    exact_mod_cast unitaryCrossings_rank_balance k j
  change _ / (((r-j : ℕ) : ℚ) * r.choose j) = _ / (r.choose j : ℚ) - _ / (r.choose (j+1) : ℚ)
  field_simp [show (r.choose j : ℚ) ≠ 0 by exact_mod_cast hc.ne',
    show (r.choose (j+1) : ℚ) ≠ 0 by exact_mod_cast hd.ne',
    show ((r-j : ℕ) : ℚ) ≠ 0 by exact_mod_cast hpos.ne']
  linear_combination (r.choose (j+1) : ℚ) * flow -
    (smallUnitaryRankCount k (j+1) : ℚ) * step

/-- The log-weighted midpoint price is a sum of signed pivotal counts, one
per possible crossing block, priced by the logarithm of that block alone. -/
theorem unitaryHalfWeight_log_flux (k : ℕ) :
    (unitaryHalfWeight k : ℝ) * Real.log k =
      ∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p,
        (-1 : ℝ)^S.card * Real.log (p^k.factorization p : ℕ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hm : (k : ℝ) = ∏ p ∈ k.primeFactors, ((p^k.factorization p : ℕ) : ℝ) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hk
  have hl : Real.log k = ∑ p ∈ k.primeFactors, Real.log (p^k.factorization p : ℕ) := by
    conv_lhs => arg 1; rw [hm]
    exact Real.log_prod fun p hp => by
      exact_mod_cast (pow_pos (Nat.prime_of_mem_primeFactors hp).pos (k.factorization p)).ne'
  rw [hl, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [unitaryHalfWeight_eq_sum_pivots hp, Int.cast_sum, sum_mul]
  simp

#print axioms unitaryCrossings_probability
#print axioms unitaryHalfWeight_log_flux

end
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
