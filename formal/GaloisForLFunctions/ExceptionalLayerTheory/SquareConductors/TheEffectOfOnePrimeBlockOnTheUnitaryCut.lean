import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheResponseOfTheUnitaryCutToBlockActivity

/-!
# Independent occupation probabilities on the unitary divisor cut

Finite birth-and-death balance determines the response to changing one
prime-power block while every other block keeps its own probability.
The difference is exactly the pivotal probability on the remaining cube
times the change in the selected coordinate. This identity is polynomial
and holds up to and including deterministic occupation choices.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Product probability of a prescribed occupation pattern on P. -/
def unitaryBlockPatternMass (P : Finset ℕ) (u : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∏ q ∈ P, if q∈S then u q else 1-u q

/-- Probability of selecting the smaller unitary divisor under separate
occupation probabilities for its prime-power blocks. -/
def unitaryIndependentCut (k : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ S ∈ smallUnitarySubsets k,unitaryBlockPatternMass k.primeFactors u S

/-- Probability on the other blocks that changing p crosses the square root. -/
def unitaryPivotalProbability (k p : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ S ∈ unitaryPivots k p,unitaryBlockPatternMass (k.primeFactors.erase p) u S

private theorem factor_at_site {P : Finset ℕ} {p : ℕ} (hp : p∈P)
    (u : ℕ → ℝ) (x : ℝ) (S : Finset ℕ) :
    unitaryBlockPatternMass P (Function.update u p x) S=
      (if p∈S then x else 1-x)*unitaryBlockPatternMass (P.erase p) u S := by
  unfold unitaryBlockPatternMass
  conv_lhs => rw [←insert_erase hp,prod_insert (notMem_erase p P)]
  rw [Function.update_self]
  congr 1
  exact prod_congr rfl fun q hq => by rw [Function.update_of_ne (mem_erase.mp hq).1]

/-- The reduced product law ignores the deleted coordinate. -/
theorem unitary_pattern_mass_erase (P S : Finset ℕ) (p : ℕ) (u : ℕ → ℝ) :
    unitaryBlockPatternMass (P.erase p) u (S.erase p)=unitaryBlockPatternMass (P.erase p) u S := by
  apply prod_congr rfl
  intro q hq
  simp only [mem_erase,(mem_erase.mp hq).1,true_and]

/-- Separate a single Bernoulli factor from the full pattern mass. -/
theorem unitary_pattern_mass_at_site {P : Finset ℕ} {p : ℕ} (hp : p∈P) (u : ℕ → ℝ) (S : Finset ℕ) :
    unitaryBlockPatternMass P u S=(if p∈S then u p else 1-u p)*unitaryBlockPatternMass (P.erase p) u S := by
  unfold unitaryBlockPatternMass
  conv_lhs => rw [←insert_erase hp,prod_insert (notMem_erase p P)]

/-- Exact one-coordinate finite difference. The coefficient is
independent of the selected coordinate's starting probability. -/
theorem unitary_cut_single_block_response {k p : ℕ} (hp : p∈k.primeFactors) (u : ℕ → ℝ) (x y : ℝ) :
    unitaryIndependentCut k (Function.update u p y)-unitaryIndependentCut k (Function.update u p x)=
      -(y-x)*unitaryPivotalProbability k p u := by
  rw [unitaryIndependentCut,unitaryIndependentCut,←sum_sub_distrib,unitaryPivotalProbability,
    unitaryPivot_flux hp,mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [factor_at_site hp,factor_at_site hp,unitary_pattern_mass_erase]
  by_cases hit : p∈S <;> simp only [hit,if_true,if_false] <;> ring

/-- At interior occupation probabilities a single increase in p detects
the existence of any arithmetic pivot in that direction. -/
theorem unitary_block_strict_response_iff {k p : ℕ} (hp : p∈k.primeFactors) {u : ℕ → ℝ}
    (inside : ∀ q∈k.primeFactors.erase p, 0<u q ∧ u q<1) {x y : ℝ} (hxy : x<y) :
    unitaryIndependentCut k (Function.update u p y)<unitaryIndependentCut k (Function.update u p x) ↔
      (unitaryPivots k p).Nonempty := by
  have mass (S : Finset ℕ) : 0<unitaryBlockPatternMass (k.primeFactors.erase p) u S := by
    apply prod_pos
    intro q hq
    split_ifs <;> first | exact (inside q hq).1 | exact sub_pos.mpr (inside q hq).2
  rw [←sub_lt_zero,unitary_cut_single_block_response hp]
  constructor
  · intro small
    by_contra empty
    rw [unitaryPivotalProbability,not_nonempty_iff_eq_empty.mp empty,sum_empty,mul_zero] at small
    exact lt_irrefl 0 small
  · intro live
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hxy)) (sum_pos (fun S _ => mass S) live)

/-- The common Gibbs activity z gives occupation probability z/(1+z)
in every coordinate and recovers the smaller-side partition quotient. -/
theorem unitary_independent_cut_at_common_activity (k : ℕ) {z : ℝ} (hz : 0≤z) :
    unitaryIndependentCut k (fun _ => z/(1+z))=unitaryCutProbability k z := by
  have den : 1+z≠0 := (add_pos_of_pos_of_nonneg zero_lt_one hz).ne'
  rw [unitaryIndependentCut,unitaryCutProbability,unitaryCutPartition,sum_div]
  refine sum_congr rfl fun S hs => ?_
  let P := k.primeFactors
  have sub : S⊆P := mem_powerset.mp (mem_filter.mp hs).1
  have each (q : ℕ) : (if q∈S then z/(1+z) else 1-z/(1+z))=(if q∈S then z else 1)/(1+z) := by
    split_ifs
    · rfl
    · field_simp [den]
  have cap : P.filter (·∈S)=S := by
    ext q
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨sub h,h⟩⟩
  change (∏ q ∈ P, (if q∈S then z/(1+z) else 1-z/(1+z)))=z^S.card/(1+z)^P.card
  simp_rw [each]
  rw [prod_div_distrib,prod_const,←prod_filter,cap,prod_const]

private theorem deterministic_pattern {P S T : Finset ℕ} (hs : S⊆P) (ht : T⊆P) :
    unitaryBlockPatternMass P (fun q => if q∈T then 1 else 0) S=if S=T then 1 else 0 := by
  by_cases eq : S=T
  · rw [if_pos eq,eq,unitaryBlockPatternMass]
    apply prod_eq_one
    intro q _
    by_cases h : q∈T <;> simp [h]
  · rw [if_neg eq,unitaryBlockPatternMass]
    have different : ∃ q∈P, ¬(q∈S ↔ q∈T) := by
      by_contra! same
      apply eq
      ext q
      by_cases h : q∈P
      · exact same q h
      · exact ⟨fun hS => False.elim (h (hs hS)),fun hT => False.elim (h (ht hT))⟩
    obtain ⟨q,hq,ne⟩ := different
    apply prod_eq_zero hq
    by_cases s : q∈S <;> by_cases t : q∈T <;> simp_all

/-- The deterministic settings of the other blocks recover the entire
pivotal family from a single-coordinate probability difference. -/
theorem unitary_pivot_pattern_readout {k p : ℕ} (T : Finset ℕ) (hT : T⊆k.primeFactors.erase p) :
    unitaryPivotalProbability k p (fun q => if q∈T then 1 else 0)=if T∈unitaryPivots k p then 1 else 0 := by
  rw [unitaryPivotalProbability]
  calc _ = ∑ S ∈ unitaryPivots k p, (if S=T then (1:ℝ) else 0) :=
              sum_congr rfl fun _ hs => deterministic_pattern (mem_powerset.mp (mem_filter.mp hs).1) hT
       _ = _ := by simp

/-- Deterministic coordinate choices recover each smaller unitary divisor
from the independent occupation probability. -/
theorem unitary_cut_pattern_readout {k : ℕ} (T : Finset ℕ) (hT : T⊆k.primeFactors) :
    unitaryIndependentCut k (fun q => if q∈T then 1 else 0)=if T∈smallUnitarySubsets k then 1 else 0 := by
  rw [unitaryIndependentCut]
  calc _ = ∑ S ∈ smallUnitarySubsets k, (if S=T then (1:ℝ) else 0) :=
              sum_congr rfl fun _ hs => deterministic_pattern (mem_powerset.mp (mem_filter.mp hs).1) hT
       _ = _ := by simp

#print axioms unitary_cut_single_block_response
#print axioms unitary_block_strict_response_iff
#print axioms unitary_independent_cut_at_common_activity
#print axioms unitary_cut_pattern_readout
#print axioms unitary_pivot_pattern_readout
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
