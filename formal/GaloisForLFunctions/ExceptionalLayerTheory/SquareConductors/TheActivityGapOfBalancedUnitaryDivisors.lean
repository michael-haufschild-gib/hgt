import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ReciprocalActivitiesOnTheTwoUnitaryDivisorSides
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOneSidedExtremaOfTheOddUnitaryMidpoint

/-!
# The biased unitary cut compared with a dominant prime-power block

Below unit activity, moving a configuration from rank r−j to rank j
gains z^j−z^(r−j). Complementation removes the symmetric part of the
price. Erdős–Ko–Rado bounds the number of overweight configurations at
each low rank. Every remaining coefficient of the difference from a full
face is nonnegative. If all single blocks are small, the rank-one
coefficient is exactly one, and a one-exchange cut pays only this term.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The small and overweight configurations partition each rank. -/
theorem unitary_rank_card_partition (k j : ℕ) :
    smallUnitaryRankCount k j+(unitaryDefectLayer k j).card=k.primeFactors.card.choose j := by
  let S := smallUnitarySubsets k
  have filter_eq : (k.primeFactors.powersetCard j).filter (·∈S)=S.filter (fun T => T.card=j) := by
    ext T
    simp only [mem_filter,mem_powersetCard]
    have sub (h : T∈S) : T⊆k.primeFactors := mem_powerset.mp (mem_filter.mp h).1
    tauto
  have split := sum_filter_add_sum_filter_not (k.primeFactors.powersetCard j) (·∈S) (fun _ => (1:ℕ))
  rw [filter_eq] at split
  simpa only [smallUnitaryRankCount,unitaryDefectLayer,S,sum_const,nsmul_eq_mul,mul_one,card_powersetCard] using split

/-- At every rank through the middle, the smaller side has at least
the rank mass of a full face. -/
theorem unitary_cut_low_rank_dominates_face {k j : ℕ} (hk : 1<k) (hj : j≤k.primeFactors.card/2) :
    (k.primeFactors.card-1).choose j≤smallUnitaryRankCount k j := by
  cases j with
  | zero =>
    have small : ∅∈smallUnitarySubsets k := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩
      rw [unitarySubset_small_iff_square (by omega) (empty_subset _)]
      simpa only [primePowerSubset,prod_empty,one_pow] using hk.le
    simpa only [Nat.choose_zero_right] using (show 0<smallUnitaryRankCount k 0 from
      card_pos.mpr ⟨∅,mem_filter.mpr ⟨small,card_empty⟩⟩)
  | succ j =>
    have split := unitary_rank_card_partition k (j+1)
    have cap := unitaryDefectLayer_erdos_ko_rado hj
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr (Nat.nonempty_primeFactors.mpr hk)).ne'
    rw [hm,Nat.choose_succ_succ] at split
    rw [hm,Nat.succ_sub_one,Nat.succ_sub_one] at cap
    rw [hm,Nat.succ_sub_one]
    omega

private theorem sum_by_rank (F : Finset (Finset ℕ)) (r : ℕ) (le : ∀ S∈F, S.card≤r) (w : ℕ → ℝ) :
    (∑ S ∈ F,w S.card)=∑ j ∈ range (r+1),(((F.filter (fun S => S.card=j)).card:ℝ)*w j) := by
  calc _ = ∑ S ∈ F,∑ j ∈ range (r+1), if S.card=j then w j else 0 := by
            refine sum_congr rfl fun S hs => ?_
            simp [mem_range.mpr (Nat.lt_succ_of_le (le S hs))]
       _ = _ := by
            rw [sum_comm]
            refine sum_congr rfl fun j _ => ?_
            rw [←sum_filter,sum_const,nsmul_eq_mul]

/-- Gain from selecting the smaller rank of a complementary pair. The gain
vanishes at and above half the number of blocks. -/
def unitaryRankActivityGain (r j : ℕ) (z : ℝ) := z^j-z^(max j (r-j))

/-- Exact difference from a full face for any rank price. The part
invariant under complementary ranks cancels on the two families. -/
theorem unitary_cut_rank_price_gap {k p : ℕ} (hk : 1<k) (hp : p∈k.primeFactors) (w : ℕ → ℝ) :
    let r := k.primeFactors.card
    (∑ S ∈ smallUnitarySubsets k,w S.card)-(∑ S ∈ (k.primeFactors.erase p).powerset,w S.card)=
      ∑ j ∈ range (r+1), ((smallUnitaryRankCount k j:ℝ)-((r-1).choose j:ℝ))*(w j-w (max j (r-j))) := by
  intro r
  let P := k.primeFactors
  let F := smallUnitarySubsets k
  let B := P.erase p
  let A := B.powerset
  have subF {S : Finset ℕ} (h : S∈F) : S⊆P := mem_powerset.mp (mem_filter.mp h).1
  have subA {S : Finset ℕ} (h : S∈A) : S⊆P := (mem_powerset.mp h).trans (erase_subset p P)
  have face {S : Finset ℕ} (h : S⊆P) : S∈A ↔ p∉S := by
    change S∈(P.erase p).powerset ↔ _
    rw [mem_powerset]
    exact ⟨fun sub hit => notMem_erase p P (sub hit),
      fun no i hi => mem_erase.mpr ⟨fun eq => no (eq ▸ hi),h hi⟩⟩
  let u (j : ℕ) := w (max j (r-j))
  have sym {j : ℕ} (hj : j≤r) : u (r-j)=u j := by
    dsimp only [u]
    rw [show r-(r-j)=j by omega,max_comm]
  have sym_price (T : Finset (Finset ℕ)) (sub : ∀ {S}, S∈T → S⊆P)
      (flip : ∀ {S}, S⊆P → (P \ S∈T ↔ S∉T)) :
      (∑ S ∈ T,u S.card)+(∑ S ∈ T,u S.card)=∑ S ∈ P.powerset,u S.card := by
    have h := reflected_rank_sum_of_complement_pairing P T sub flip u
    rw [sum_add_distrib] at h
    have eq : (∑ S ∈ T,u (P.card-S.card))=∑ S ∈ T,u S.card :=
      sum_congr rfl fun S hs => sym (card_le_card (sub hs))
    rwa [eq] at h
  have aflip {S : Finset ℕ} (hs : S⊆P) : P \ S∈A ↔ S∉A := by
    rw [face sdiff_subset,face hs,mem_sdiff]
    simp only [hp,true_and,not_not]
  have small := sym_price F (fun h => subF h) (fun h => unitary_complement_mem_small_iff hk h)
  have other := sym_price A (fun h => subA h) (fun h => aflip h)
  have cancel : (∑ S ∈ F,u S.card)=∑ S ∈ A,u S.card := by linarith only [small,other]
  have gain (T : Finset (Finset ℕ)) : (∑ S ∈ T,(w S.card-u S.card))=
      (∑ S ∈ T,w S.card)-∑ S ∈ T,u S.card := sum_sub_distrib
  have ac : B.card=r-1 := card_erase_of_mem hp
  have count (j : ℕ) : (A.filter (fun S => S.card=j)).card=(r-1).choose j := by
    have eq : A.filter (fun S => S.card=j)=B.powersetCard j := by
      ext S
      simp only [A,mem_filter,mem_powerset,mem_powersetCard]
    rw [eq,card_powersetCard,ac]
  have expand (T : Finset (Finset ℕ)) (le : ∀ S∈T,S.card≤r) := sum_by_rank T r le (fun j => w j-u j)
  have lhs : (∑ S ∈ F,w S.card)-(∑ S ∈ A,w S.card)=
      (∑ S ∈ F,(w S.card-u S.card))-∑ S ∈ A,(w S.card-u S.card) := by
    rw [gain,gain,cancel]
    ring
  rw [lhs,expand F (fun _ hs => card_le_card (subF hs)),expand A (fun _ hs => card_le_card (subA hs)),←sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [count,sub_mul]
  rfl

/-- Exact rank expansion of the activity excess over a full face,
before dividing by the total partition function. -/
theorem unitary_cut_activity_gap_expansion {k : ℕ} (hk : 1<k) (z : ℝ) :
    let r := k.primeFactors.card
    unitaryCutPartition k z-(1+z)^(r-1)=
      ∑ j ∈ range (r+1), ((smallUnitaryRankCount k j:ℝ)-((r-1).choose j:ℝ))*unitaryRankActivityGain r j z := by
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hk
  have norm : (∑ S ∈ (k.primeFactors.erase p).powerset,z^S.card)=(1+z)^(k.primeFactors.card-1) := by
    simpa only [prod_const,card_erase_of_mem hp] using (prod_one_add (f:=fun _ : ℕ => z) (k.primeFactors.erase p)).symm
  simpa only [unitaryCutPartition,unitaryRankActivityGain,←norm] using unitary_cut_rank_price_gap hk hp (fun j => z^j)

private theorem rank_price_paid {k j : ℕ} (hk : 1<k) {w : ℕ → ℝ} (anti : Antitone w) :
    let r := k.primeFactors.card
    0≤((smallUnitaryRankCount k j:ℝ)-((r-1).choose j:ℝ))*(w j-w (max j (r-j))) := by
  intro r
  by_cases low : j≤r/2
  · exact mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (unitary_cut_low_rank_dominates_face hk low)))
      (sub_nonneg.mpr (anti (le_max_left j (r-j))))
  · have hi : r-j≤j := by omega
    simp only [max_eq_left hi,sub_self,mul_zero,le_refl]

/-- At subunit activity every arithmetic cut has at least the smaller-side
probability of a conductor with one prime-power block above its square root. -/
theorem unitary_cut_probability_dominates_face {k : ℕ} (hk : 1<k) {z : ℝ} (hz : 0≤z) (top : z≤1) :
    1/(1+z)≤unitaryCutProbability k z := by
  have positive : 0<1+z := add_pos_of_pos_of_nonneg zero_lt_one hz
  let r := k.primeFactors.card
  have rank : r-1+1=r := Nat.sub_add_cancel (card_pos.mpr (Nat.nonempty_primeFactors.mpr hk))
  have expand := unitary_cut_activity_gap_expansion hk z
  have anti : Antitone (fun j : ℕ => z^j) := fun _ _ => pow_le_pow_of_le_one hz top
  have no_loss := sum_nonneg (s:=range (r+1)) (fun j _ => rank_price_paid (j:=j) hk anti)
  have bound : (1+z)^(r-1)≤unitaryCutPartition k z := sub_nonneg.mp (expand.trans_ge no_loss)
  change 1/(1+z) ≤ unitaryCutPartition k z/(1+z)^r
  apply (div_le_div_iff₀ positive (pow_pos positive r)).mpr
  rw [one_mul,←rank,pow_succ]
  exact mul_le_mul_of_nonneg_right bound positive.le

private theorem small_through_singletons {k : ℕ} (hk : 1<k)
    (bal : ∀ p∈k.primeFactors,(p^k.factorization p)^2≤k) {S : Finset ℕ}
    (sub : S⊆k.primeFactors) (h : S.card≤1) : S∈smallUnitarySubsets k := by
  refine mem_filter.mpr ⟨mem_powerset.mpr sub,(unitarySubset_small_iff_square (by omega) sub).mpr ?_⟩
  rcases S.eq_empty_or_nonempty with rfl|inh
  · simpa only [primePowerSubset,prod_empty,one_pow] using hk.le
  · have hc := card_pos.mpr inh
    obtain ⟨p,rfl⟩ := card_eq_one.mp (show S.card=1 by omega)
    simpa only [primePowerSubset,prod_singleton] using bal p (sub (mem_singleton_self p))

/-- A support with no block above the square root contains at least three primes. -/
theorem three_le_card_balanced_unitary_support {k : ℕ} (hk : 1<k)
    (bal : ∀ p∈k.primeFactors,(p^k.factorization p)^2≤k) : 3≤k.primeFactors.card := by
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hk
  have sub := singleton_subset_iff.mpr hp
  have one := small_through_singletons hk bal sub (by rw [card_singleton])
  by_contra! small
  have lo : (k.primeFactors \ {p}).card≤1 := by rw [card_sdiff_of_subset sub,card_singleton]; omega
  exact (unitary_complement_mem_small_iff hk sub).mp (small_through_singletons hk bal sdiff_subset lo) one

/-- Every decreasing rank observable gains at least its rank-one
versus rank-(r−1) price difference when all single blocks are small. -/
theorem balanced_unitary_rank_price_gap {k p : ℕ} (hk : 1<k) (hp : p∈k.primeFactors)
    (bal : ∀ q∈k.primeFactors,(q^k.factorization q)^2≤k) {w : ℕ → ℝ} (anti : Antitone w) :
    let r := k.primeFactors.card
    (∑ S ∈ (k.primeFactors.erase p).powerset,w S.card)+(w 1-w (r-1))≤∑ S ∈ smallUnitarySubsets k,w S.card := by
  intro r
  have three : 3≤r := three_le_card_balanced_unitary_support hk bal
  have eq : (smallUnitarySubsets k).filter (fun S => S.card=1)=k.primeFactors.powersetCard 1 := by
    ext S
    rw [mem_filter,mem_powersetCard]
    exact ⟨fun h => ⟨mem_powerset.mp (mem_filter.mp h.1).1,h.2⟩,
      fun h => ⟨small_through_singletons hk bal h.1 h.2.le,h.2⟩⟩
  have count : smallUnitaryRankCount k 1=r := by
    rw [smallUnitaryRankCount,eq,card_powersetCard,Nat.choose_one_right]
  let d (j : ℕ) := ((smallUnitaryRankCount k j:ℝ)-((r-1).choose j:ℝ))*(w j-w (max j (r-j)))
  have bit : d 1=w 1-w (r-1) := by
    dsimp only [d]
    rw [count,Nat.choose_one_right,Nat.cast_sub (by omega : 1≤r),Nat.cast_one,
      max_eq_right (by omega : 1≤r-1)]
    ring
  have included : d 1≤∑ j ∈ range (r+1),d j :=
    single_le_sum (fun j _ => rank_price_paid (j:=j) hk anti) (mem_range.mpr (by omega))
  rw [bit] at included
  have total : (∑ S ∈ smallUnitarySubsets k,w S.card)-(∑ S ∈ (k.primeFactors.erase p).powerset,w S.card)=
      ∑ j ∈ range (r+1),d j := unitary_cut_rank_price_gap hk hp w
  linarith only [included,total]

/-- The rank-one term forces an explicit gain at every subunit
activity. The one-exchange activity law attains this bound. -/
theorem balanced_unitary_activity_gap {k : ℕ} (hk : 1<k)
    (bal : ∀ p∈k.primeFactors,(p^k.factorization p)^2≤k) {z : ℝ} (hz : 0≤z) (top : z≤1) :
    let r := k.primeFactors.card
    (1+z)^(r-1)+(z-z^(r-1))≤unitaryCutPartition k z := by
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hk
  have norm : (∑ S ∈ (k.primeFactors.erase p).powerset,z^S.card)=(1+z)^(k.primeFactors.card-1) := by
    simpa only [prod_const,card_erase_of_mem hp] using (prod_one_add (f:=fun _ : ℕ => z) (k.primeFactors.erase p)).symm
  simpa only [pow_one,unitaryCutPartition,norm] using
    balanced_unitary_rank_price_gap hk hp bal (w:=fun j => z^j) (fun _ _ => pow_le_pow_of_le_one hz top)

/-- Equality with a single-block probability at any interior subunit
activity detects a prime-power block above the square root. -/
theorem unitary_cut_face_equality_iff {k : ℕ} (hk : 1<k) {z : ℝ} (hz : 0<z) (top : z<1) :
    unitaryCutProbability k z=1/(1+z) ↔ ∃ p∈k.primeFactors,k<(p^k.factorization p)^2 := by
  let r := k.primeFactors.card
  have qp : 0<1+z := add_pos zero_lt_one hz
  have rank : r-1+1=r := Nat.sub_add_cancel (card_pos.mpr (Nat.nonempty_primeFactors.mpr hk))
  have cross : unitaryCutProbability k z=1/(1+z) ↔ unitaryCutPartition k z=(1+z)^(r-1) := by
    change unitaryCutPartition k z/(1+z)^r=_ ↔ _
    rw [div_eq_div_iff (pow_ne_zero r qp.ne') qp.ne',one_mul,
      show (1+z)^r=(1+z)^(r-1)*(1+z) by rw [←pow_succ,rank]]
    exact mul_left_inj' qp.ne'
  rw [cross]
  constructor
  · intro eq
    by_contra! absent
    have three : 3≤r := three_le_card_balanced_unitary_support hk absent
    have strict : z^(r-1)<z := by
      have limit := pow_lt_one₀ hz.le top (by omega : r-2≠0)
      rw [show r-1=(r-2)+1 by omega,pow_succ]
      simpa only [one_mul] using mul_lt_mul_of_pos_right limit hz
    have price := balanced_unitary_activity_gap hk absent hz.le top.le
    change (1+z)^(r-1)+(z-z^(r-1))≤unitaryCutPartition k z at price
    linarith only [eq,price,strict]
  · rintro ⟨p,hp,big⟩
    rw [unitaryCutPartition,small_unitary_subsets_of_dominant hk hp big]
    simpa only [prod_const,card_erase_of_mem hp] using
      (prod_one_add (f:=fun _ : ℕ => z) (k.primeFactors.erase p)).symm

#print axioms balanced_unitary_activity_gap
#print axioms balanced_unitary_rank_price_gap
#print axioms unitary_cut_face_equality_iff
#print axioms unitary_cut_low_rank_dominates_face
#print axioms unitary_cut_rank_price_gap
#print axioms unitary_cut_activity_gap_expansion
#print axioms unitary_cut_probability_dominates_face
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
