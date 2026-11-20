import GaloisForLFunctions.GaloisTheoryOfZeros.JensenQuartetExhaustion
import GaloisForLFunctions.FiniteFreeProbability.NonRealJensenCountBound
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.StaircasePacking

/-!
# The multiplicity spectrum in one Jensen quadrant

A nonreal root of the centered Xi Jensen polynomial occurs in a quartet.
Slonim's staircase bound for distinct row lengths, applied to quadrant
multiplicities, charges each represented order separately. The saddle bound
on the total number of nonreal roots yields fourth-root growth of the
number of distinct multiplicities.
-/

open Finset Polynomial Complex Filter Topology RHTower FiniteFreeProbability
namespace GaloisForLFunctions.GaloisTheoryOfZeros
noncomputable section
open scoped Classical

/-- One quadrant of the centered Jensen root divisor, with multiplicity. -/
def jensenQuadrantRoots (d : ℕ) : Multiset ℂ :=
  (xiJensen (1/2) d).roots.filter fun z => 0 < z.re ∧ 0 < z.im

/-- Multiplicities present among quadrant roots of order at least b. -/
def jensenQuartetOrders (d b : ℕ) : Finset ℕ :=
  let M := jensenQuadrantRoots d
  (M.toFinset.filter fun z => b ≤ M.count z).image M.count

/-- A high-multiplicity cutoff charges b for every repeated occupied level
and successively more for each distinct level above b. -/
theorem jensenQuartetOrders_cost (d b : ℕ) :
    let M := jensenQuadrantRoots d
    let S := M.toFinset.filter fun z => b ≤ M.count z
    let k := (jensenQuartetOrders d b).card
    4 * ((b+k).choose 2 + (S.card-k)*b) ≤ 4*b.choose 2 + jensenNonrealCount d := by
  let M := jensenQuadrantRoots d
  let S := M.toFinset.filter fun z => b ≤ M.count z
  have h := StaircasePacking.multiplicity_binomial_bound S M.count b 1
    (fun z hz => (mem_filter.mp hz).2)
  have hsum : ∑ z ∈ M.toFinset, M.count z = M.card :=
    Multiset.sum_count_eq_card fun _ hz => Multiset.mem_toFinset.mpr hz
  have hle := sum_le_sum_of_subset (f := M.count) (show S ⊆ M.toFinset from filter_subset _ _)
  simp only [Nat.choose_one_right] at h
  rw [hsum] at hle
  have hall := Nat.mul_le_mul_left 4 (h.trans (Nat.add_le_add_left hle _))
  rw [jensenNonrealCount_eq_four_mul]
  have hM : M.card = jensenQuartetCount d := by
    unfold M jensenQuadrantRoots jensenQuartetCount
    congr!
  calc
    _ ≤ 4 * (b.choose 2 + M.card) := hall
    _ = _ := by rw [hM,Nat.mul_add]

/-- The whole quartet spectrum costs a triangular number even before
the extra charge for a second orbit of the same multiplicity. -/
theorem quartet_orders_triangular (d : ℕ) :
    4 * ((jensenQuartetOrders d 1).card + 1).choose 2 ≤ jensenNonrealCount d := by
  have h := jensenQuartetOrders_cost d 1
  simp only [Nat.choose_succ_self, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    Nat.add_comm 1 (jensenQuartetOrders d 1).card] at h
  omega

/-- A multiplicity census at one finite Jensen degree gives a lower bound
on the complete off-line zeta divisor, counting zero copies. -/
theorem quartet_orders_le_offline (d : ℕ) :
    ((4 * ((jensenQuartetOrders d 1).card+1).choose 2 : ℕ) : ℕ∞) ≤
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard := by
  rw [← iSup_jensenNonrealCount]
  exact (Nat.cast_le.mpr (quartet_orders_triangular d)).trans
    (le_iSup (fun d : ℕ => (jensenNonrealCount d : ℕ∞)) d)

private theorem twice_triangle (k : ℕ) : 2*(k+1).choose 2 = k*(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ (k+1) 1, Nat.choose_one_right, Nat.mul_add, ih]
    ring

/-- An unconditional fourth-power estimate for the number of distinct
nonreal multiplicities. It holds even if the off-line divisor is infinite. -/
theorem eventually_jensenQuartetOrders_fourth :
    ∀ᶠ d : ℕ in atTop, ((jensenQuartetOrders d 1).card : ℝ)^4 ≤
      22500 * (d : ℝ) * Real.log d := by
  filter_upwards [eventually_jensenNonrealCount_le_sqrt] with d hd
  let k := (jensenQuartetOrders d 1).card
  have ht := quartet_orders_triangular d
  change 4*(k+1).choose 2 ≤ _ at ht
  rw [show 4*(k+1).choose 2 = 2*(2*(k+1).choose 2) by ring, twice_triangle] at ht
  have htR : 2*((k:ℝ)*((k:ℝ)+1)) ≤ (jensenNonrealCount d : ℝ) := by exact_mod_cast ht
  have hk : (k:ℝ)^2 ≤ 150 * Real.sqrt ((d:ℝ)*Real.log d) := by
    nlinarith only [htR, hd, Nat.cast_nonneg (α := ℝ) k]
  have hs := pow_le_pow_left₀ (sq_nonneg (k:ℝ)) hk 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))] at hs
  change (k:ℝ)^4 ≤ _
  nlinarith only [hs]

#print axioms jensenQuartetOrders_cost
#print axioms quartet_orders_le_offline
#print axioms eventually_jensenQuartetOrders_fourth
end
end GaloisForLFunctions.GaloisTheoryOfZeros
