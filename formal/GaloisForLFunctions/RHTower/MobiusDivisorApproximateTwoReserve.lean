import GaloisForLFunctions.RHTower.MobiusDivisorInheritedTwoCost

/-!
# Full successor reserve with an actual receiving error

No exact balance is assumed. Every remaining successor retains its receiving
displacement; its complete parent energy bounds that error without a factor
depending on the number of processed primes.
-/
noncomputable section
open Finset
namespace RHTower

private lemma fibre_bound (M : ℕ) (P R : Finset ℕ) (E : ℝ)
    (hE : mobiusDivisorSelectionEnergy M P≤E) :
    |mobiusDivisorSelectionFibre M P R|≤Real.sqrt E := by
  have h := sum_mobiusDivisorSelectionFibre_sq_le_energy M P {R}
  simp only [sum_singleton] at h
  exact Real.abs_le_sqrt (h.trans hE)

private lemma receiving_error (a b x y E : ℝ)
    (ha : |a|≤Real.sqrt E) (hb : |b|≤Real.sqrt E) :
    -2*a*x-2*b*y+x^(2 : ℕ)+y^(2 : ℕ) ≤ 2*Real.sqrt E*(|x|+|y|)+(|x|+|y|)^(2 : ℕ) := by
  have bound (a x : ℝ) (ha : |a|≤Real.sqrt E) : -a*x≤Real.sqrt E*|x| := by
    calc
      -a*x=-(a*x) := by ring
      _≤|a*x| := neg_le_abs _
      _=|a| * |x| := abs_mul _ _
      _≤Real.sqrt E*|x| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hxy := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  nlinarith only [bound a x ha,bound b y hb,hxy,sq_abs x,sq_abs y]

private lemma receiving_merged_error (a x y E : ℝ) (ha : |a|≤Real.sqrt E) :
    -2*a*(x+y)+(x+y)^(2 : ℕ) ≤ 2*Real.sqrt E*(|x|+|y|)+(|x|+|y|)^(2 : ℕ) := by
  have hab : -a*(x+y)≤Real.sqrt E*(|x|+|y|) := by
    calc
      -a*(x+y)=-(a*(x+y)) := by ring
      _≤|a*(x+y)| := neg_le_abs _
      _=|a| * |x+y| := abs_mul _ _
      _≤Real.sqrt E*|x+y| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _≤Real.sqrt E*(|x|+|y|) := mul_le_mul_of_nonneg_left (abs_add_le x y) (Real.sqrt_nonneg E)
  have hs := mul_le_mul (abs_add_le x y) (abs_add_le x y) (abs_nonneg (x+y))
    (add_nonneg (abs_nonneg x) (abs_nonneg y))
  nlinarith only [hab,hs,sq_abs (x+y)]

private lemma other_profile (M : ℕ) (P : Finset ℕ) (p q : ℕ)
    (hcore : mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hq : q.Prime) (hqP : q∉P) (hq2 : q≠2) (R : Finset ℕ) :
    mobiusDivisorInterpolatedFibre M p (insert q P) R=mobiusDivisorInterpolatedFibre M p P R := by
  have hinactive : M/p+1≤q := by
    by_contra hn
    apply hqP
    apply hcore
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hq⟩,by simpa using hq2⟩
  rw [show insert q P=P∪{q} by simp,mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_union_inactive (M/p) P {q} R (by
      intro r hr; have he := mem_singleton.mp hr; subst r; omega),
    mobiusDivisorSelectionFibre_union_inactive (M/p+1) P {q} R (by
      intro r hr; have he := mem_singleton.mp hr; subst r; exact hinactive)]
  rfl

private lemma other_energy (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q)
    {q : ℕ} (hq : q.Prime) (hqP : q∉P) (hqL : q∉L) (hq2 : q≠2) :
    mobiusDivisorSelectionEnergy M (insert q (P∪L))=mobiusDivisorSelectionEnergy M (insert q P)-
      2*mobiusDivisorSelectionFibre M (insert q P) ∅*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)-
      2*mobiusDivisorSelectionFibre M (insert q P) {2}*(∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})+
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)-
      ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by
  have hL' : ∀ p∈L,p.Prime ∧ p<M ∧ p∉insert q P ∧ p≠2 := by
    intro p hp
    obtain ⟨hpprime,hpM,hpP,hp2⟩ := hL p hp
    refine ⟨hpprime,hpM,?_,hp2⟩
    simp only [mem_insert,not_or]
    exact ⟨fun he => hqL (he ▸ hp),hpP⟩
  have hc' : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆insert q P :=
    fun p hp => (hcore p hp).trans (subset_insert q P)
  have hi (p : ℕ) (hp : p∈L) (R : Finset ℕ) := other_profile M P p q (hcore p hp) hq hqP hq2 R
  have hsum (R : Finset ℕ) :
      (∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p (insert q P) R)=
        ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R := by
    apply sum_congr rfl
    intro p hp
    rw [hi p hp R]
  have hsquares : (∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p (insert q P) ∅)^(2 : ℕ)+
      (mobiusDivisorInterpolatedFibre M p (insert q P) {2})^(2 : ℕ)))=
      ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+
        (mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)) := by
    apply sum_congr rfl
    intro p hp
    rw [hi p hp ∅,hi p hp {2}]
  have he := mobiusDivisorSelectionEnergy_union_two_child_inactive M (insert q P) L hM hL' hc' hchild
  rw [hsum ∅,hsum {2},hsquares,insert_union] at he
  exact he

/-- The full actual successor envelope retains a dimension-independent receiving error; no balance premise is required. -/
theorem mobiusDivisorSuccessorEnvelope_two_block_reserve_error
    (M : ℕ) (P L : Finset ℕ) (hM : 2<M)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ p≠2)
    (hcore : ∀ p∈L,mobiusDivisorSelectionPrimes (M/p+1)\{2}⊆P)
    (hchild : ∀ p∈L,∀ q∈L,p≠q → M/p+1≤q) :
    let X := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅
    let Y := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}
    let R := ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ))
    let T := ∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)
    mobiusDivisorSuccessorEnvelope M (P∪L)+min R T ≤ mobiusDivisorSuccessorEnvelope M P+
      2*Real.sqrt (mobiusDivisorSuccessorEnvelope M P)*(|X|+|Y|)+(|X|+|Y|)^(2 : ℕ) := by
  let X := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅
  let Y := ∑ p∈L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}
  let R := ∑ p∈L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^(2 : ℕ)+(mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ))
  let T := ∑ p∈L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^(2 : ℕ)
  let E := mobiusDivisorSuccessorEnvelope M P
  let a := mobiusDivisorSelectionFibre M P ∅
  let b := mobiusDivisorSelectionFibre M P {2}
  have hbase := (mobiusDivisorSuccessorEnvelope_le_iff M P E).mp le_rfl
  have h0 := mobiusDivisorSelectionEnergy_union_two_child_inactive M P L hM hL hcore hchild
  change mobiusDivisorSelectionEnergy M (P∪L)=mobiusDivisorSelectionEnergy M P-2*a*X-2*b*Y+X^(2 : ℕ)+Y^(2 : ℕ)-R at h0
  have hcost := mobiusDivisorSelectionEnergy_two_block_transport M P L hM hL hcore hchild
  have hsquares : T=R+∑ p∈L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
    dsimp only [T,R]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  change mobiusDivisorSelectionEnergy M (insert 2 (P∪L))-mobiusDivisorSelectionEnergy M (P∪L)=
    mobiusDivisorSelectionEnergy M (insert 2 P)-mobiusDivisorSelectionEnergy M P-2*a*Y-2*b*X+2*X*Y-_ at hcost
  have h2 : mobiusDivisorSelectionEnergy M (insert 2 (P∪L))=
      mobiusDivisorSelectionEnergy M (insert 2 P)-2*(a+b)*(X+Y)+(X+Y)^(2 : ℕ)-T := by
    nlinarith only [h0,hcost,hsquares]
  have he : mobiusDivisorSuccessorEnvelope M (P∪L) ≤ E+2*Real.sqrt E*(|X|+|Y|)+(|X|+|Y|)^(2 : ℕ)-min R T := by
    rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨?_,?_⟩
    · have hbnd := receiving_error a b X Y E (fibre_bound M P ∅ E hbase.1) (fibre_bound M P {2} E hbase.1)
      linarith only [h0,hbase.1,hbnd,min_le_left R T]
    · intro q hq
      obtain ⟨hqactive,hqnot⟩ := mem_sdiff.mp hq
      have hqP : q∉P := fun h => hqnot (mem_union_left L h)
      have hqL : q∉L := fun h => hqnot (mem_union_right P h)
      have hqbase := hbase.2 q (mem_sdiff.mpr ⟨hqactive,hqP⟩)
      by_cases hq2 : q=2
      · subst q
        have hab := fibre_bound M (insert 2 P) ∅ E hqbase
        simp only [mobiusDivisorSelectionFibre_insert,notMem_empty,if_false,insert_empty_eq] at hab
        have hbnd := receiving_merged_error (a+b) X Y E hab
        linarith only [h2,hqbase,hbnd,min_le_right R T]
      · have hs := other_energy M P L hM hL hcore hchild (mem_filter.mp hqactive).2 hqP hqL hq2
        change mobiusDivisorSelectionEnergy M (insert q (P∪L))=mobiusDivisorSelectionEnergy M (insert q P)-
          2*mobiusDivisorSelectionFibre M (insert q P) ∅*X-2*mobiusDivisorSelectionFibre M (insert q P) {2}*Y+X^(2 : ℕ)+Y^(2 : ℕ)-R at hs
        have hbnd := receiving_error _ _ X Y E (fibre_bound M (insert q P) ∅ E hqbase)
          (fibre_bound M (insert q P) {2} E hqbase)
        linarith only [hs,hqbase,hbnd,min_le_left R T]
  change mobiusDivisorSuccessorEnvelope M (P∪L)+min R T ≤ E+2*Real.sqrt E*(|X|+|Y|)+(|X|+|Y|)^(2 : ℕ)
  linarith only [he]
end RHTower
