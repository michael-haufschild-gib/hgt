import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheResponseOfTheUnitaryCutToBlockActivity
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RankDefectsAtTheUnitaryMidpoint

/-!
# Reciprocal birth activities at the unitary square root

Complementation exchanges the two sides of every nontrivial unitary
factorization. Under finite-volume activity weights this operation
inverts the activity. Hence the smaller-side probability is one half
at exactly one activity, independently of the prime-power block sizes.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A family containing one representative of each complementary pair
recovers every rank test on the cube by adding its reflected test. -/
theorem reflected_rank_sum_of_complement_pairing {A : Type*} [AddCommMonoid A]
    (P : Finset ℕ) (F : Finset (Finset ℕ)) (sub : ∀ {S}, S∈F → S⊆P)
    (flip : ∀ {S}, S⊆P → (P \ S∈F ↔ S∉F)) (w : ℕ → A) :
    (∑ S ∈ F, (w S.card+w (P.card-S.card)))=∑ S ∈ P.powerset,w S.card := by
  have whole : P.powerset.filter (·∈F)=F := by
    ext S
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_powerset.mpr (sub h),h⟩⟩
  have comp : (∑ S ∈ F,w (P.card-S.card))=∑ S ∈ P.powerset.filter (·∉F),w S.card := by
    apply sum_nbij' (fun S => P \ S) (fun S => P \ S)
    · intro S hS
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset,fun h => (flip (sub hS)).mp h hS⟩
    · intro S hS
      obtain ⟨inside,out⟩ := mem_filter.mp hS
      exact (flip (mem_powerset.mp inside)).mpr out
    · exact fun S hS => Finset.sdiff_sdiff_eq_self (sub hS)
    · exact fun S hS => Finset.sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hS).1)
    · exact fun S hS => congrArg w (card_sdiff_of_subset (sub hS)).symm
  have both := sum_filter_add_sum_filter_not P.powerset (·∈F) (fun S => w S.card)
  rw [whole] at both
  rw [sum_add_distrib,comp]
  exact both

/-- Adding the reflected rank test on the smaller unitary divisors
recovers the full block cube for every additive observable. -/
theorem unitary_cut_reflected_rank_sum {A : Type*} [AddCommMonoid A] {k : ℕ}
    (hk : 1<k) (w : ℕ → A) :
    (∑ S ∈ smallUnitarySubsets k, (w S.card+w (k.primeFactors.card-S.card)))=
      ∑ S ∈ k.primeFactors.powerset,w S.card :=
  reflected_rank_sum_of_complement_pairing _ _ (fun h => mem_powerset.mp (mem_filter.mp h).1)
    (fun hs => unitary_complement_mem_small_iff hk hs) w

/-- The entire partition polynomial splits into the small-divisor
polynomial and its reciprocal with the complementary rank shift. -/
theorem unitary_cut_partition_reciprocity {k : ℕ} (hk : 1<k) {z : ℝ} (hz : z≠0) :
    unitaryCutPartition k z+z^k.primeFactors.card*unitaryCutPartition k z⁻¹=(1+z)^k.primeFactors.card := by
  let P := k.primeFactors
  have split := unitary_cut_reflected_rank_sum hk (fun j => z^j)
  have full : (∑ S ∈ P.powerset,z^S.card)=(1+z)^P.card := by
    simpa only [prod_const] using (prod_one_add (f:=fun _ : ℕ => z) P).symm
  rw [←full,←split,unitaryCutPartition,unitaryCutPartition,mul_sum,sum_add_distrib]
  congr 1
  refine sum_congr rfl fun S hs => ?_
  have le := card_le_card (mem_powerset.mp (mem_filter.mp hs).1)
  change z^P.card*(z⁻¹)^S.card=z^(P.card-S.card)
  rw [show z^P.card=z^(P.card-S.card)*z^S.card by rw [←pow_add,Nat.sub_add_cancel le],
    inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hz),mul_one]

/-- At positive activity, the large-divisor probability equals the
small-divisor probability at reciprocal activity. -/
theorem unitary_cut_probability_reciprocity {k : ℕ} (hk : 1<k) {z : ℝ} (hz : 0<z) :
    unitaryCutProbability k z+unitaryCutProbability k z⁻¹=1 := by
  let r := k.primeFactors.card
  have dz : 1+z≠0 := (add_pos zero_lt_one hz).ne'
  have den := pow_ne_zero r dz
  have back : 1+z⁻¹=(1+z)/z := by field_simp [hz.ne']; exact add_comm _ _
  have repr : unitaryCutProbability k z⁻¹=z^r*unitaryCutPartition k z⁻¹/(1+z)^r := by
    rw [unitaryCutProbability,back,div_pow,div_div_eq_mul_div]
    ring
  rw [repr,unitaryCutProbability,←add_div,unitary_cut_partition_reciprocity hk hz.ne',div_self den]

/-- The two unitary divisor sides are equiprobable precisely at unit
activity. Below that value the small side has majority probability. -/
theorem unitary_cut_activity_half {k : ℕ} (hk : 1<k) {z : ℝ} (hz : 0<z) :
    (unitaryCutProbability k z=1/2 ↔ z=1) ∧
      (1/2<unitaryCutProbability k z ↔ z<1) := by
  have h := unitary_cut_probability_reciprocity hk (z:=(1:ℝ)) zero_lt_one
  rw [inv_one] at h
  have half : unitaryCutProbability k 1=1/2 := by linarith only [h]
  have one : (1:ℝ)∈Set.Ioi 0 := Set.mem_Ioi.mpr (zero_lt_one : (0:ℝ)<1)
  have anti := unitary_cut_probability_strictAnti hk
  rcases lt_trichotomy z 1 with low|rfl|high
  · have gt := anti (show z∈Set.Ioi 0 from hz) one low
    rw [half] at gt
    exact ⟨⟨fun eq => False.elim (gt.ne' eq),fun eq => False.elim (low.ne eq)⟩,⟨fun _ => low,fun _ => gt⟩⟩
  · simp [half]
  · have lt := anti one (show z∈Set.Ioi 0 from hz) high
    rw [half] at lt
    exact ⟨⟨fun eq => False.elim (lt.ne eq),fun eq => False.elim (high.ne' eq)⟩,
      ⟨fun h => False.elim (lt.not_gt h),fun h => False.elim (high.not_gt h)⟩⟩

#print axioms unitary_cut_reflected_rank_sum
#print axioms unitary_cut_partition_reciprocity
#print axioms unitary_cut_probability_reciprocity
#print axioms unitary_cut_activity_half
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
