import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RankDefectsAtTheUnitaryMidpoint
import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-!
# The one-sided range of the odd unitary midpoint

On a support of size 2r+1 the overweight low-rank subsets form an
intersecting upset up to rank r. Their layer sizes are nondecreasing
by double counting inclusions. Their alternating sum therefore has the
central sign and is at most the final layer. Erdős–Ko–Rado bounds this
layer by C(2r,r−1). The two signed extremes are generally asymmetric.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

/-- The overweight subsets of exactly one cardinality. -/
def unitaryDefectLayer (k j : ℕ) :=
  (k.primeFactors.powersetCard j).filter fun S => S ∉ smallUnitarySubsets k

private theorem mem_layer {k j : ℕ} {S : Finset ℕ} : S ∈ unitaryDefectLayer k j ↔
    S ⊆ k.primeFactors ∧ S.card=j ∧ primePowerSubset k (k.primeFactors \ S) < primePowerSubset k S := by
  simp only [unitaryDefectLayer,mem_filter,mem_powersetCard,smallUnitarySubsets,mem_powerset,
    not_and,not_le]
  tauto

private theorem block_mono {k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hT : T ⊆ k.primeFactors) :
    primePowerSubset k S ≤ primePowerSubset k T :=
  Finset.prod_le_prod_of_subset_of_one_le h (fun _ _ => Nat.zero_le _)
    (fun p hp _ => pow_pos (Nat.prime_of_mem_primeFactors (hT hp)).pos _)

private theorem overweight_mono {k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hT : T ⊆ k.primeFactors)
    (hS : primePowerSubset k (k.primeFactors \ S) < primePowerSubset k S) :
    primePowerSubset k (k.primeFactors \ T) < primePowerSubset k T :=
  (block_mono (sdiff_subset_sdiff_right k.primeFactors h) sdiff_subset).trans_lt (hS.trans_le (block_mono h hT))

/-- Each lower-rank overweight subset extends in every unused prime. -/
theorem unitaryDefectLayer_normalized_growth (k j : ℕ) :
    (unitaryDefectLayer k j).card*(k.primeFactors.card-j) ≤ (unitaryDefectLayer k (j+1)).card*(j+1) := by
  classical
  apply card_mul_le_card_mul (· ⊆ ·)
  · intro S hS
    obtain ⟨hs,hcard,hheavy⟩ := mem_layer.mp hS
    have hinj : Set.InjOn (fun a => insert a S) (k.primeFactors \ S) :=
      (insert_inj_on S).mono fun a ha => (mem_sdiff.mp ha).2
    rw [show k.primeFactors.card-j = (k.primeFactors \ S).card by rw [card_sdiff_of_subset hs,hcard],
      ←card_image_of_injOn hinj]
    apply card_le_card
    rintro _ h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    obtain ⟨hp,hn⟩ := mem_sdiff.mp ha
    have hT := insert_subset hp hs
    exact mem_bipartiteAbove.mpr ⟨mem_layer.mpr ⟨hT,by rw [card_insert_of_notMem hn,hcard],
      overweight_mono (subset_insert ..) hT hheavy⟩,subset_insert ..⟩
  · intro T hT
    obtain ⟨_,hcard,_⟩ := mem_layer.mp hT
    conv_rhs => rw [←hcard,←card_image_of_injOn T.erase_injOn]
    apply card_le_card
    intro S hS
    obtain ⟨hs,hsub⟩ := mem_bipartiteBelow.mp hS
    have hc := (mem_layer.mp hs).2.1
    obtain ⟨a,ha,he⟩ := exists_eq_insert_iff.mpr ⟨hsub,by omega⟩
    apply mem_image.mpr
    exact ⟨a,he ▸ mem_insert_self a S,by rw [←he,erase_insert ha]⟩

private theorem layer_mono {k r j : ℕ} (hr : k.primeFactors.card=2*r+1) (hj : j < r) :
    (unitaryDefectLayer k j).card ≤ (unitaryDefectLayer k (j+1)).card := by
  have hg := unitaryDefectLayer_normalized_growth k j
  exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ (show j+1 ≤ k.primeFactors.card-j by omega)).trans hg)
    (Nat.succ_pos j)

private theorem layer_intersect {k j : ℕ} {S T : Finset ℕ} (hs : S ∈ unitaryDefectLayer k j)
    (ht : T ∈ unitaryDefectLayer k j) : ¬Disjoint S T := by
  obtain ⟨hS,_,hSH⟩ := mem_layer.mp hs
  obtain ⟨hT,_,hTH⟩ := mem_layer.mp ht
  intro hd
  have hs' : S ⊆ k.primeFactors \ T :=
    fun a ha => mem_sdiff.mpr ⟨hS ha,Finset.disjoint_left.mp hd ha⟩
  have ht' : T ⊆ k.primeFactors \ S :=
    fun a ha => mem_sdiff.mpr ⟨hT ha,Finset.disjoint_left.mp hd.symm ha⟩
  exact ((hSH.trans_le (block_mono hs' sdiff_subset)).trans
    (hTH.trans_le (block_mono ht' sdiff_subset))).false

/-- Erdős–Ko–Rado on a prescribed finite ground set of primes. -/
theorem unitaryDefectLayer_erdos_ko_rado {k j : ℕ} (hj : j ≤ k.primeFactors.card/2) :
    (unitaryDefectLayer k j).card ≤ (k.primeFactors.card-1).choose (j-1) := by
  classical
  let P := k.primeFactors
  let F := unitaryDefectLayer k j
  let e := (P.orderIsoOfFin rfl).symm.toEquiv.toEmbedding
  let lift (S : Finset ℕ) := (S.subtype (· ∈ P)).map e
  have hground (S : Finset ℕ) (hs : S ∈ F) : S ⊆ P := (mem_layer.mp hs).1
  have hback (S : Finset ℕ) (hs : S ∈ F) :
      (S.subtype (· ∈ P)).map (Function.Embedding.subtype (· ∈ P)) = S :=
    subtype_map_of_mem fun _ hi => hground S hs hi
  have hinj : Set.InjOn lift (F : Set (Finset ℕ)) := by
    intro S hS T hT h
    have hh := Finset.map_injective e h
    rw [←hback S hS,hh,hback T hT]
  let A := F.image lift
  have hsize : (A : Set (Finset (Fin P.card))).Sized j := by
    intro T hT
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
    change ((S.subtype (· ∈ P)).map e).card=j
    rw [card_map,←card_map (Function.Embedding.subtype (· ∈ P)),hback S hS,(mem_layer.mp hS).2.1]
  have hI : (A : Set (Finset (Fin P.card))).Intersecting := by
    intro S hS T hT hd
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hS
    obtain ⟨V,hV,rfl⟩ := mem_image.mp hT
    apply layer_intersect hU hV
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    let a : P := ⟨p,hground U hU hp⟩
    have h₁ : e a ∈ lift U := mem_map.mpr ⟨a,by simpa [a] using hp,rfl⟩
    have h₂ : e a ∈ lift V := mem_map.mpr ⟨a,by simpa [a] using hp',rfl⟩
    exact Finset.disjoint_left.mp hd h₁ h₂
  simpa only [A,card_image_of_injOn hinj] using erdos_ko_rado hI hsize hj

/-- The signed sum of the low-rank defects, oriented to the middle rank. -/
def orientedDefectCount (k r : ℕ) : ℤ :=
  (-1 : ℤ)^r * ∑ S ∈ unitaryRankDefects k r, (-1 : ℤ)^S.card

private theorem rank_successor (k r : ℕ) :
    unitaryRankDefects k (r+1) = unitaryRankDefects k r ∪ unitaryDefectLayer k (r+1) := by
  ext S
  simp only [unitaryRankDefects,unitaryDefectLayer,mem_filter,mem_union,mem_powerset,mem_powersetCard]
  by_cases h : S ⊆ k.primeFactors <;> by_cases h' : S ∈ smallUnitarySubsets k <;> simp [h,h'] <;> omega

private theorem oriented_step (k r : ℕ) :
    orientedDefectCount k (r+1) = (unitaryDefectLayer k (r+1)).card-orientedDefectCount k r := by
  have hd : Disjoint (unitaryRankDefects k r) (unitaryDefectLayer k (r+1)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    have h := (mem_filter.mp (mem_filter.mp hS).1).2
    have h' := (mem_layer.mp hT).2.1
    omega
  have he : ∑ S ∈ unitaryDefectLayer k (r+1), (-1:ℤ)^S.card =
      (unitaryDefectLayer k (r+1)).card * (-1:ℤ)^(r+1) := by
    calc _ = ∑ _S ∈ unitaryDefectLayer k (r+1), (-1:ℤ)^(r+1) :=
              sum_congr rfl fun S hS => by rw [(mem_layer.mp hS).2.1]
         _ = _ := by simp
  unfold orientedDefectCount
  rw [rank_successor,sum_union hd,he,mul_add,mul_left_comm,←mul_pow]
  norm_num [pow_succ]

/-- Alternating cancellation leaves a nonnegative integer at most the top defect layer. -/
theorem orientedDefectCount_bounds {k r : ℕ} (hr : k.primeFactors.card=2*r+1) :
    0 ≤ orientedDefectCount k r ∧ orientedDefectCount k r ≤ (unitaryDefectLayer k r).card := by
  suffices h : ∀ j ≤ r, 0 ≤ orientedDefectCount k j ∧ orientedDefectCount k j ≤ (unitaryDefectLayer k j).card
    from h r le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    have he : unitaryRankDefects k 0 = unitaryDefectLayer k 0 := by
      ext S
      simp [unitaryRankDefects,unitaryDefectLayer]
    have hs : ∑ S ∈ unitaryDefectLayer k 0, (-1:ℤ)^S.card = (unitaryDefectLayer k 0).card := by
      calc _ = ∑ _S ∈ unitaryDefectLayer k 0, (1:ℤ) :=
               sum_congr rfl fun S hS => by rw [(mem_layer.mp hS).2.1,pow_zero]
           _ = _ := by simp
    simp [orientedDefectCount,he,hs]
  | succ j ih =>
    intro hj
    obtain ⟨hlo,hhi⟩ := ih (by omega)
    have hcard : ((unitaryDefectLayer k j).card : ℤ) ≤ (unitaryDefectLayer k (j+1)).card := by
      exact_mod_cast layer_mono hr (by omega : j < r)
    rw [oriented_step]
    omega

/-- At every odd rank, the midpoint lies on a finite arithmetic progression.
The number of downward steps from the central extremum is at most C(2r,r−1). -/
theorem odd_unitary_midpoint_range_bound {k r : ℕ} (hr : k.primeFactors.card=2*r+1) :
    ∃ j : ℕ, j ≤ (2*r).choose (r-1) ∧
      unitaryHalfWeight k = (-1:ℤ)^r * (((2*r).choose r:ℤ)-2*j) := by
  obtain ⟨h₀,h₁⟩ := orientedDefectCount_bounds hr
  have h₂ := unitaryDefectLayer_erdos_ko_rado (show r ≤ k.primeFactors.card/2 by omega)
  rw [hr, Nat.add_sub_cancel] at h₂
  refine ⟨(orientedDefectCount k r).toNat,?_,?_⟩
  · omega
  · have hw := unitaryHalfWeight_rank_formula k
    dsimp only at hw
    rw [hr,if_neg (by omega),if_neg (by simp),show (2*r+1)/2=r by omega] at hw
    rw [Int.toNat_of_nonneg h₀,orientedDefectCount,hw,mul_sub]
    have hsg : (-1:ℤ)^r * (-1)^r = 1 := by rw [←mul_pow]; norm_num
    linear_combination (2*∑ S ∈ unitaryRankDefects k r, (-1:ℤ)^S.card)*hsg

#print axioms unitaryDefectLayer_erdos_ko_rado
#print axioms orientedDefectCount_bounds
#print axioms odd_unitary_midpoint_range_bound

end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
