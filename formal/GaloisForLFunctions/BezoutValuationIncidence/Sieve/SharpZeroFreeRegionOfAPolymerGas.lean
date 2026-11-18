import GaloisForLFunctions.HTGeometry.EulerianCrossingPolymerFreeEnergyLaw
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Complex.Basic

/-!
# The exact zero-free polydisc test for a finite polymer gas

The deletion identity behind Trybushnyi's Proposition 3.1 compares every
complex partition with the partition at the all-negative vertex of the
polydisc. Positivity at that vertex on every induced subgraph is necessary
and sufficient. If positivity fails, changing one coordinate of a minimal
bad subgraph already produces a real zero.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas

variable {ι R : Type*} [DecidableEq ι] [CommRing R] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- Weighted independent-set sum over a finite vertex set. -/
def partition (S : Finset ι) (w : ι → R) : R :=
  ∑ U ∈ S.powerset, if G.IsIndepSet (U : Set ι) then ∏ i ∈ U, w i else 0

theorem real_partition (S : Finset ι) (w : ι → ℝ) :
    partition G S w = HTGeometry.compatiblePolymerPartition S
      (fun U => G.IsIndepSet (U : Set ι)) w := by
  simp only [partition,HTGeometry.compatiblePolymerPartition,sum_filter]

@[simp] theorem partition_empty (w : ι → R) : partition G ∅ w=1 := by
  simp [partition,SimpleGraph.isIndepSet_iff]

theorem partition_congr (S : Finset ι) (w v : ι → R) (h : ∀ i ∈ S, w i=v i) :
    partition G S w=partition G S v := by
  apply sum_congr rfl
  intro U hU
  split <;> rename_i hI
  · exact prod_congr rfl fun i hi => h i (mem_powerset.mp hU hi)
  · rfl

/-- Keeping just the previously inserted vertices compatible with i. -/
def compatible (i : ι) (S : Finset ι) := S.filter (fun j => ¬ G.Adj i j)

/-- Deleting an inserted vertex or retaining it and deleting its neighbors. -/
theorem partition_insert (i : ι) (S : Finset ι) (hi : i ∉ S) (w : ι → R) :
    partition G (insert i S) w = partition G S w + w i*partition G (compatible G i S) w := by
  classical
  have hp : (compatible G i S).powerset =
      S.powerset.filter (fun U => ∀ j ∈ U, ¬ G.Adj i j) := by
    ext U
    simp only [mem_powerset,mem_filter,compatible,subset_iff]
    exact ⟨fun h => ⟨fun j hj => (h hj).1,fun j hj => (h hj).2⟩,
      fun ⟨h₁,h₂⟩ j hj => ⟨h₁ hj,h₂ j hj⟩⟩
  rw [partition,sum_powerset_insert hi]
  congr 1
  rw [partition,hp,sum_filter,mul_sum]
  apply sum_congr rfl
  intro U hU
  have hiU := notMem_of_mem_powerset_of_notMem hU hi
  have hI : G.IsIndepSet (↑(insert i U) : Set ι) ↔
      G.IsIndepSet (U : Set ι) ∧ ∀ j ∈ U, ¬G.Adj i j := by
    simp only [coe_insert,SimpleGraph.isIndepSet_iff]
    letI : Std.Symm (fun a b => ¬ G.Adj a b) := ⟨fun _ _ hn h => hn h.symm⟩
    exact Set.pairwise_insert_of_symm_of_notMem hiU
  by_cases h₂ : ∀ j ∈ U, ¬G.Adj i j
  · rw [if_pos h₂]
    by_cases h₁ : G.IsIndepSet (U : Set ι)
    · rw [if_pos (hI.2 ⟨h₁,h₂⟩),if_pos h₁,prod_insert hiU]
    · rw [if_neg (fun h => h₁ (hI.1 h).1),if_neg h₁,mul_zero]
  · rw [if_neg h₂,if_neg (fun h => h₂ (hI.1 h).2),mul_zero]

/-- Real partition at all negative activity bounds. -/
def negative (p : ι → NNReal) (S : Finset ι) := partition G S (fun i => -(p i : ℝ))

/-- The normalized magnitude can only increase when vertices are added. This
simultaneously controls all ratios after deleting an arbitrary vertex set. -/
theorem normalized_mono (p : ι → NNReal) (P : Finset ι)
    (hp : ∀ S ⊆ P, 0 < negative G p S) (w : ι → ℂ) (hw : ∀ i ∈ P, ‖w i‖ ≤ (p i : ℝ))
    (S T : Finset ι) (hS : S ⊆ P) (hT : T ⊆ S) :
    ‖partition G T w‖/negative G p T ≤ ‖partition G S w‖/negative G p S := by
  induction S using Finset.strongInductionOn generalizing T with
  | _ S ih =>
    by_cases he : S ⊆ T
    · rw [Subset.antisymm hT he]
    obtain ⟨i,hi,hit⟩ := not_subset.mp he
    let Q := S.erase i
    let C := compatible G i Q
    have hQ : Q ⊂ S := erase_ssubset hi
    have hQP := hQ.subset.trans hS
    have hC : C ⊆ Q := filter_subset _ _
    have hCQ := ih Q hQ C hQP hC
    have hTQ : T ⊆ Q := subset_erase.mpr ⟨hT,hit⟩
    refine (ih Q hQ T hQP hTQ).trans ?_
    have eS : insert i Q=S := insert_erase hi
    have e (a : ι → ℂ) : partition G S a=partition G Q a+a i*partition G C a := by
      simpa only [eS] using partition_insert G i Q (notMem_erase _ _) a
    have en : negative G p S=negative G p Q-(p i : ℝ)*negative G p C := by
      simpa only [negative,eS,neg_mul,← sub_eq_add_neg] using
        partition_insert G i Q (notMem_erase _ _) (fun j => -(p j : ℝ))
    have hpQ := hp Q hQP
    have hpC := hp C (hC.trans hQP)
    rw [div_le_div_iff₀ hpC hpQ] at hCQ
    have hcost := mul_le_mul_of_nonneg_left hCQ (p i).property
    have hdiff : ‖partition G Q w‖-(p i : ℝ)*‖partition G C w‖ ≤ ‖partition G S w‖ := by
      have htri := norm_sub_le (partition G S w) (w i*partition G C w)
      have he : partition G S w-w i*partition G C w=partition G Q w := by
        rw [e w,add_sub_cancel_right]
      rw [he,norm_mul] at htri
      have hbound := mul_le_mul_of_nonneg_right (hw i (hS hi)) (norm_nonneg (partition G C w))
      linarith only [htri,hbound]
    rw [div_le_div_iff₀ hpQ (hp S hS),en]
    have hh := mul_le_mul_of_nonneg_right hdiff hpQ.le
    apply le_trans _ hh
    rw [mul_sub,sub_mul]
    apply sub_le_sub_left
    calc
      ((p i : ℝ)*‖partition G C w‖)*negative G p Q =
          (p i : ℝ)*(‖partition G C w‖*negative G p Q) := mul_assoc _ _ _
      _ ≤ _ := hcost
      _ = ‖partition G Q w‖*((p i : ℝ)*negative G p C) := mul_left_comm _ _ _

/-- The negative corner is an attained absolute lower bound throughout the polydisc. -/
theorem corner_minimum (p : ι → NNReal) (P : Finset ι)
    (hp : ∀ S ⊆ P, 0 < negative G p S) (w : ι → ℂ) (hw : ∀ i ∈ P, ‖w i‖ ≤ (p i : ℝ)) :
    negative G p P ≤ ‖partition G P w‖ := by
  have h := normalized_mono G p P hp w hw P ∅ Subset.rfl (empty_subset _)
  simp only [show negative G p ∅ = 1 by simp [negative],partition_empty,norm_one,div_one] at h
  simpa only [one_mul] using (le_div_iff₀ (hp P Subset.rfl)).1 h

private theorem cast_partition (S : Finset ι) (w : ι → ℝ) :
    partition G S (fun i => (w i : ℂ)) = ((partition G S w : ℝ) : ℂ) := by
  simp only [partition,Complex.ofReal_sum,Complex.ofReal_prod,apply_ite Complex.ofReal,Complex.ofReal_zero]

/-- A minimal bad set has an exact real zero obtained by changing only one
activity; every other activity may remain at its negative endpoint. -/
theorem one_coordinate_zero (p : ι → NNReal) (S : Finset ι) (hS : negative G p S ≤ 0)
    (hproper : ∀ T ⊂ S, 0 < negative G p T) (i : ι) (hi : i ∈ S) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p i : ℝ) ∧
      partition G S (Function.update (fun j => -(p j : ℝ)) i (-r))=0 := by
  let Q := S.erase i
  let C := compatible G i Q
  let w (j : ι) := -(p j : ℝ)
  have hQ : Q ⊂ S := erase_ssubset hi
  have hC : C ⊆ Q := filter_subset _ _
  have qpos := hproper Q hQ
  have cpos := hproper C (hC.trans_ssubset hQ)
  have hiQ : i ∉ Q := notMem_erase _ _
  have hiC : i ∉ C := fun hc => hiQ (hC hc)
  have en := partition_insert G i Q hiQ w
  rw [show insert i Q=S from insert_erase hi] at en
  change negative G p S=negative G p Q+ (-(p i : ℝ))*negative G p C at en
  let r := negative G p Q / negative G p C
  refine ⟨r,(div_pos qpos cpos).le,(div_le_iff₀ cpos).2 (by linarith only [en,hS]),?_⟩
  have unchanged (U : Finset ι) (hu : i ∉ U) :
      partition G U (Function.update w i (-r))=negative G p U :=
    partition_congr G U _ w fun j hj => Function.update_of_ne (fun (h : j=i) => hu (h ▸ hj)) _ _
  have h := partition_insert G i Q hiQ (Function.update w i (-r))
  rw [show insert i Q=S from insert_erase hi,unchanged Q hiQ,unchanged C hiC,Function.update_self] at h
  exact h.trans (by dsimp only [r]; field_simp; ring)

theorem zero_free_iff (p : ι → NNReal) (P : Finset ι) :
    (∀ S ⊆ P, ∀ w : ι → ℂ, (∀ i ∈ S, ‖w i‖ ≤ (p i : ℝ)) → partition G S w ≠ 0) ↔
      ∀ S ⊆ P, 0 < negative G p S := by
  constructor
  · intro H S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro hSP
      by_contra! h
      have hn : S.Nonempty := nonempty_iff_ne_empty.mpr fun he => by norm_num [he,negative] at h
      obtain ⟨i,hi⟩ := hn
      obtain ⟨r,hr,hb,hzero⟩ := one_coordinate_zero G p S h (fun T ht => ih T ht (ht.subset.trans hSP)) i hi
      let w := Function.update (fun j => -(p j : ℝ)) i (-r)
      have hz := H S hSP (fun j => (w j : ℂ)) (fun j _ => by
        by_cases hj : j=i
        · subst j
          simpa [w,abs_of_nonneg hr] using hb
        · simp [w,Function.update_of_ne hj])
      exact hz ((cast_partition G S w).trans (by rw [show partition G S w=0 from hzero]; simp))
  · intro H S hs w hw
    have h := corner_minimum G p S (fun U hu => H U (hu.trans hs)) w hw
    exact norm_ne_zero_iff.mp ((H S hs).trans_le h).ne'

/-- Setting excluded activities to zero realizes an induced gas inside the full gas. -/
theorem restrict_activities (P S : Finset ι) (hs : S ⊆ P) (w : ι → R) :
    partition G P (fun i => if i ∈ S then w i else 0)=partition G S w := by
  classical
  have he : S.powerset=P.powerset.filter (fun U => U ⊆ S) := by
    ext U
    simp only [mem_filter,mem_powerset]
    exact ⟨fun h => ⟨h.trans hs,h⟩,And.right⟩
  simp only [partition,he,sum_filter]
  apply sum_congr rfl
  intro U _
  by_cases hu : U ⊆ S
  · simp only [if_pos hu]
    split
    · exact prod_congr rfl fun i hi => if_pos (hu hi)
    · rfl
  · obtain ⟨i,hi,hin⟩ := not_subset.mp hu
    have hz : (∏ i ∈ U, if i ∈ S then w i else 0)=0 :=
      prod_eq_zero hi (if_neg hin)
    simp [hu,hz]

/-- Zero-freeness of the single full partition on its closed polydisc is equivalent
to strict positivity of the finitely many induced negative-corner values. -/
theorem full_polydisc_iff (p : ι → NNReal) (P : Finset ι) :
    (∀ w : ι → ℂ, (∀ i ∈ P, ‖w i‖ ≤ (p i : ℝ)) → partition G P w ≠ 0) ↔
      ∀ S ⊆ P, 0 < negative G p S := by
  rw [← zero_free_iff]
  constructor
  · intro h S hs w hw
    have hz := h (fun i => if i ∈ S then w i else 0) (fun i _ => by
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using hw i hi
      · simp [hi])
    rwa [restrict_activities G P S hs] at hz
  · exact fun H => H P Subset.rfl

end GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas

#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.real_partition
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.partition_congr
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.partition_insert
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.normalized_mono
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.corner_minimum
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.one_coordinate_zero
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.zero_free_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.restrict_activities
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.full_polydisc_iff
