import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoPrimeBatches
import GaloisForLFunctions.RHTower.MobiusDivisorSuccessorAverageObstruction

/-!
# Inherited prime-two cost outside the retained pair

The full cost of inserting two includes all external paired fibres.
A child supported in the head/two plane removes its own signed covariance
from this external cost. The receiving pair retains the remaining terms.
-/
noncomputable section
open Finset
namespace RHTower

/-- Complete cost of inserting two, with only the empty/two receiving product removed. -/
def mobiusDivisorExternalTwoCost (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorSelectionEnergy M (insert 2 P)-mobiusDivisorSelectionEnergy M P-
    2*mobiusDivisorSelectionFibre M P ∅*mobiusDivisorSelectionFibre M P {2}

/-- The inherited cost contains every nonempty pair of labels differing by two. -/
theorem mobiusDivisorExternalTwoCost_eq_sum (M : ℕ) (P : Finset ℕ)
    (hM : 2<M) (hP : 2∉P) :
    mobiusDivisorExternalTwoCost M P =
      2*∑ R∈(((mobiusDivisorSelectionPrimes M).erase 2).powerset.erase ∅),
        mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert 2 R) := by
  have h := mobiusDivisorSelectionEnergy_insert_cross Nat.prime_two M P hM hP
  have hs := sum_erase_add (s:=((mobiusDivisorSelectionPrimes M).erase 2).powerset)
    (f:=fun R => mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert 2 R))
    (a:=∅) (by simp)
  simp only [insert_empty_eq] at hs
  unfold mobiusDivisorExternalTwoCost
  linarith only [h,hs]

private lemma clipped_insert_two_head (M p : ℕ) (P : Finset ℕ) :
    mobiusDivisorInterpolatedFibre M p (insert 2 P) ∅ =
      mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2} := by
  simp only [mobiusDivisorInterpolatedFibre,mobiusDivisorSelectionFibre_insert,
    notMem_empty,if_false,insert_empty_eq]
  ring

private lemma clipped_insert_two_zero (M p : ℕ) (P : Finset ℕ) :
    mobiusDivisorInterpolatedFibre M p (insert 2 P) {2}=0 := by
  simp [mobiusDivisorInterpolatedFibre,mobiusDivisorSelectionFibre_insert]

/-- A two-coordinate child removes its entire signed covariance from the external inherited cost. -/
theorem mobiusDivisorExternalTwoCost_insert (M : ℕ) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hpM : p<M) (hpP : p∉P) (hp2 : p≠2) (hM : 2<M)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P) :
    mobiusDivisorExternalTwoCost M (insert p P) =
      mobiusDivisorExternalTwoCost M P-
        2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
  have h := mobiusDivisorSelectionEnergy_insert_two_remaining M P hp hpM hpP hp2 hM hcore
  have h' := mobiusDivisorSelectionEnergy_insert_two_remaining M (insert 2 P) hp hpM
    (by simp [hp2,hpP]) hp2 hM (hcore.trans (subset_insert 2 P))
  rw [Finset.insert_comm p 2 P,clipped_insert_two_head,clipped_insert_two_zero] at h'
  simp only [mobiusDivisorSelectionFibre_insert,notMem_empty,if_false,insert_empty_eq,
    mem_singleton,if_true,mul_zero,add_zero] at h'
  unfold mobiusDivisorExternalTwoCost
  rw [mobiusDivisorSelectionFibre_insert_interpolation hp M P ∅ hpP (by simp),
    mobiusDivisorSelectionFibre_insert_interpolation hp M P {2} hpP (by simpa using hp2)]
  have hs := congrArg (fun x : ℝ => x*mobiusDivisorInterpolatedFibre M p P ∅*
    mobiusDivisorInterpolatedFibre M p P {2}) (Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p))
  nlinarith only [h,h',hs]

private lemma clipped_union_inactive (M p : ℕ) (P L R : Finset ℕ)
    (hL : ∀ q∈L,M/p+1≤q) :
    mobiusDivisorInterpolatedFibre M p (P∪L) R=mobiusDivisorInterpolatedFibre M p P R := by
  rw [mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_union_inactive (M/p) P L R
      (fun q hq => by have := hL q hq; omega),
    mobiusDivisorSelectionFibre_union_inactive (M/p+1) P L R hL]
  rfl

/-- Complete inherited cost for a block of mutually child-inactive source primes. -/
theorem mobiusDivisorExternalTwoCost_union (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q) :
    mobiusDivisorExternalTwoCost M (P∪L)=mobiusDivisorExternalTwoCost M P-
      ∑ p∈L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    obtain ⟨hp,hpM,hpP,hp2⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q∈L,q.Prime ∧ q<M ∧ q∉P ∧ q≠2 :=
      fun q hq => hL q (mem_insert_of_mem hq)
    have hc' : ∀ q∈L,mobiusDivisorSelectionPrimes (M/q+1)\{2}⊆P :=
      fun q hq => hcore q (mem_insert_of_mem hq)
    have hd' : ∀ q∈L,∀ r∈L,q≠r → M/q+1≤r :=
      fun q hq r hr hqr => hchild q (mem_insert_of_mem hq) r (mem_insert_of_mem hr) hqr
    have hinactive : ∀ q∈L,M/p+1≤q := fun q hq =>
      hchild p (mem_insert_self p L) q (mem_insert_of_mem hq)
        (fun he => hpL (he.symm ▸ hq))
    rw [union_insert,mobiusDivisorExternalTwoCost_insert M (P∪L) hp hpM
      (by simp [hpP,hpL]) hp2 hM ((hcore p (mem_insert_self p L)).trans subset_union_left),
      clipped_union_inactive M p P L ∅ hinactive,
      clipped_union_inactive M p P L {2} hinactive,
      ih hL' hc' hd',sum_insert hpL]
    ring

/-- Both receiving coordinates retain their complete block displacement. -/
theorem mobiusDivisorSelectionFibre_union_two_child_inactive
    (M : ℕ) (P L R : Finset ℕ)
    (hL : ∀ p∈L,p.Prime ∧ p∉P ∧ p∉R)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q) :
    mobiusDivisorSelectionFibre M (P∪L) R=mobiusDivisorSelectionFibre M P R-
      ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    obtain ⟨hp,hpP,hpR⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q∈L,q.Prime ∧ q∉P ∧ q∉R :=
      fun q hq => hL q (mem_insert_of_mem hq)
    have hd' : ∀ q∈L,∀ r∈L,q≠r → M/q+1≤r :=
      fun q hq r hr hqr => hchild q (mem_insert_of_mem hq) r (mem_insert_of_mem hr) hqr
    have hinactive : ∀ q∈L,M/p+1≤q := fun q hq =>
      hchild p (mem_insert_self p L) q (mem_insert_of_mem hq)
        (fun he => hpL (he.symm ▸ hq))
    rw [union_insert,mobiusDivisorSelectionFibre_insert_interpolation hp M (P∪L) R
      (by simp [hpP,hpL]) hpR,clipped_union_inactive M p P L R hinactive,
      ih hL' hd',sum_insert hpL]
    ring

/-- Current energy keeps the complete receiving displacement and consumes every copied source square. -/
theorem mobiusDivisorSelectionEnergy_union_two_child_inactive
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q) :
    mobiusDivisorSelectionEnergy M (P∪L)=mobiusDivisorSelectionEnergy M P-
      2*mobiusDivisorSelectionFibre M P ∅*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)-
      2*mobiusDivisorSelectionFibre M P {2}*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})+
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)-
      ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    obtain ⟨hp,hpM,hpP,hp2⟩ := hL p (mem_insert_self p L)
    have hL' : ∀ q∈L,q.Prime ∧ q<M ∧ q∉P ∧ q≠2 :=
      fun q hq => hL q (mem_insert_of_mem hq)
    have hc' : ∀ q∈L,mobiusDivisorSelectionPrimes (M/q+1)\{2}⊆P :=
      fun q hq => hcore q (mem_insert_of_mem hq)
    have hd' : ∀ q∈L,∀ r∈L,q≠r → M/q+1≤r :=
      fun q hq r hr hqr => hchild q (mem_insert_of_mem hq) r (mem_insert_of_mem hr) hqr
    have hinactive : ∀ q∈L,M/p+1≤q := fun q hq =>
      hchild p (mem_insert_self p L) q (mem_insert_of_mem hq)
        (fun he => hpL (he.symm ▸ hq))
    have hs := mobiusDivisorSelectionEnergy_insert_two_remaining M (P∪L) hp hpM
      (by simp [hpP,hpL]) hp2 hM ((hcore p (mem_insert_self p L)).trans subset_union_left)
    rw [clipped_union_inactive M p P L ∅ hinactive,
      clipped_union_inactive M p P L {2} hinactive] at hs
    have h0 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
      (fun q hq => ⟨(hL' q hq).1,(hL' q hq).2.2.1,by simp⟩) hd'
    have h2 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
      (fun q hq => ⟨(hL' q hq).1,(hL' q hq).2.2.1,by simpa using (hL' q hq).2.2.2⟩) hd'
    rw [h0,h2,ih hL' hc' hd'] at hs
    rw [union_insert,sum_insert hpL,sum_insert hpL,sum_insert hpL]
    have hr := congrArg (fun x : ℝ => x*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
      (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)))
        (Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p))
    nlinarith only [hs,hr]

/-- The full prime-two cost retains the complete receiving error of an unbalanced block. -/
theorem mobiusDivisorSelectionEnergy_two_block_transport
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q) :
    mobiusDivisorSelectionEnergy M (insert 2 (P∪L))-mobiusDivisorSelectionEnergy M (P∪L)=
      mobiusDivisorSelectionEnergy M (insert 2 P)-mobiusDivisorSelectionEnergy M P-
        2*mobiusDivisorSelectionFibre M P ∅*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})-
        2*mobiusDivisorSelectionFibre M P {2}*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)+
        2*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)*
          (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})-
        ∑ p∈L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
  have h0 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simp⟩) hchild
  have h2 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simpa using (hL p hp).2.2.2⟩) hchild
  have hd := mobiusDivisorExternalTwoCost_union M P L hM hL hcore hchild
  unfold mobiusDivisorExternalTwoCost at hd
  rw [h0,h2] at hd
  nlinarith only [hd]

/-- A balanced actual block changes the full cost of inserting two by minus its signed covariance. -/
theorem mobiusDivisorSelectionEnergy_balanced_two_block
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q)
    (hbalance0 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=0)
    (hbalance2 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=0) :
    mobiusDivisorSelectionEnergy M (insert 2 (P∪L))-mobiusDivisorSelectionEnergy M (P∪L)=
      mobiusDivisorSelectionEnergy M (insert 2 P)-mobiusDivisorSelectionEnergy M P-
        ∑ p∈L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
  have h0 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simp⟩) hchild
  have h2 := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
    (fun p hp => ⟨(hL p hp).1,(hL p hp).2.2.1,by simpa using (hL p hp).2.2.2⟩) hchild
  rw [hbalance0,sub_zero] at h0
  rw [hbalance2,sub_zero] at h2
  have hd := mobiusDivisorExternalTwoCost_union M P L hM hL hcore hchild
  unfold mobiusDivisorExternalTwoCost at hd
  rw [h0,h2] at hd
  linarith only [hd]

/-- A balanced block contracts both actual energies, with their exact consumed source-square reserves. -/
theorem mobiusDivisorSelectionEnergy_balanced_two_reserves
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q)
    (hbalance0 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=0)
    (hbalance2 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=0) :
    mobiusDivisorSelectionEnergy M (P∪L)=mobiusDivisorSelectionEnergy M P-
      ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) ∧
    mobiusDivisorSelectionEnergy M (insert 2 (P∪L))=mobiusDivisorSelectionEnergy M (insert 2 P)-
      ∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ) := by
  have h0 := mobiusDivisorSelectionEnergy_union_two_child_inactive M P L hM hL hcore hchild
  simp only [hbalance0,hbalance2,mul_zero,sub_zero,zero_pow (by omega : 2≠0),add_zero] at h0
  refine ⟨h0,?_⟩
  have h2 := mobiusDivisorSelectionEnergy_balanced_two_block M P L hM hL hcore hchild hbalance0 hbalance2
  have he : (∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ))=
      (∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)))+
      ∑ p∈L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  rw [he]
  linarith only [h0,h2]

private lemma balanced_other_successor
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q)
    (hbalance0 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=0)
    (hbalance2 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=0)
    {q : ℕ} (hq : q.Prime) (hqP : q∉P) (hqL : q∉L) (hq2 : q≠2) :
    mobiusDivisorSelectionEnergy M (insert q (P∪L))=
      mobiusDivisorSelectionEnergy M (insert q P)-
        ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
          (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by
  have hinactive (p : ℕ) (hp : p∈L) : M/p+1≤q := by
    by_contra hn
    apply hqP
    apply hcore p hp
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hq⟩,by simpa using hq2⟩
  have hi (p : ℕ) (hp : p∈L) (R : Finset ℕ) :
      mobiusDivisorInterpolatedFibre M p (insert q P) R=mobiusDivisorInterpolatedFibre M p P R := by
    rw [show insert q P=P∪{q} by simp]
    apply clipped_union_inactive
    intro r hr
    have he : r=q := mem_singleton.mp hr
    subst r
    exact hinactive p hp
  have hL' : ∀ p∈L,p.Prime ∧ p<M ∧ p∉insert q P ∧ p≠2 := by
    intro p hp
    obtain ⟨hpprime,hpM,hpP,hp2⟩ := hL p hp
    refine ⟨hpprime,hpM,?_,hp2⟩
    simp only [mem_insert,not_or]
    exact ⟨fun he => hqL (he ▸ hp),hpP⟩
  have hc' : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆insert q P :=
    fun p hp => (hcore p hp).trans (subset_insert q P)
  have hsum (R : Finset ℕ) :
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p (insert q P) R)=
        ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R := by
    apply sum_congr rfl
    intro p hp
    rw [hi p hp R]
  have he := (mobiusDivisorSelectionEnergy_balanced_two_reserves M (insert q P) L hM hL' hc'
    hchild (by rw [hsum,hbalance0]) (by rw [hsum,hbalance2])).1
  have hsquares : (∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p (insert q P) ∅)^(2 : ℕ)+
      (mobiusDivisorInterpolatedFibre M p (insert q P) {2})^(2 : ℕ)))=
      ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
        (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by
    apply sum_congr rfl
    intro p hp
    rw [hi p hp ∅,hi p hp {2}]
  rw [hsquares,insert_union] at he
  exact he

/-- A balanced actual two-coordinate block contracts the full successor envelope by its smaller square reserve. -/
theorem mobiusDivisorSuccessorEnvelope_balanced_two_block_reserve
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q)
    (hbalance0 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=0)
    (hbalance2 : (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=0) :
    mobiusDivisorSuccessorEnvelope M (P∪L)+
      min (∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
        (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)))
        (∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+
          mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) ≤ mobiusDivisorSuccessorEnvelope M P := by
  let R := ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
    (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ))
  let T := ∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+
    mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)
  have hbase := (mobiusDivisorSuccessorEnvelope_le_iff M P _).mp le_rfl
  obtain ⟨h0,h2⟩ := mobiusDivisorSelectionEnergy_balanced_two_reserves M P L hM hL hcore hchild hbalance0 hbalance2
  change mobiusDivisorSelectionEnergy M (P∪L)=mobiusDivisorSelectionEnergy M P-R at h0
  change mobiusDivisorSelectionEnergy M (insert 2 (P∪L))=mobiusDivisorSelectionEnergy M (insert 2 P)-T at h2
  have he : mobiusDivisorSuccessorEnvelope M (P∪L) ≤ mobiusDivisorSuccessorEnvelope M P-min R T := by
    rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨by linarith only [h0,hbase.1,min_le_left R T],?_⟩
    intro q hq
    obtain ⟨hqactive,hqnot⟩ := mem_sdiff.mp hq
    have hqP : q∉P := fun h => hqnot (mem_union_left L h)
    have hqL : q∉L := fun h => hqnot (mem_union_right P h)
    have hqbase := hbase.2 q (mem_sdiff.mpr ⟨hqactive,hqP⟩)
    by_cases hq2 : q=2
    · subst q
      linarith only [h2,hqbase,min_le_right R T]
    · have hqprime := (mem_filter.mp hqactive).2
      have hs := balanced_other_successor M P L hM hL hcore hchild hbalance0 hbalance2
        hqprime hqP hqL hq2
      change mobiusDivisorSelectionEnergy M (insert q (P∪L))=
        mobiusDivisorSelectionEnergy M (insert q P)-R at hs
      linarith only [hs,hqbase,min_le_left R T]
  change mobiusDivisorSuccessorEnvelope M (P∪L)+min R T ≤ mobiusDivisorSuccessorEnvelope M P
  linarith only [he]
end RHTower
