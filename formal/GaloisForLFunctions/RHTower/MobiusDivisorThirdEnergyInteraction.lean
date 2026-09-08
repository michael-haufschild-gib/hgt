import GaloisForLFunctions.RHTower.MobiusDivisorSmallCoreInteractions

/-!
# Complete three-prime energy interactions and late-block transport

The third difference of the actual selection energy is an exact sum of
four complementary fibre products. Original source parity fixes its
nonpositive sign. Late-prime blocks retain this sign outside the joint
triple support, even after their scalar head reverses sign.

For an arbitrary starting core, the full change through a late block is
twice its signed mass times the retained triple fibre. This includes
all joint overlaps and vanishes outside their support. At the original
core it gives the exact consumed-mass threshold for retaining the
negative third-order margin. No complete successor selection is assumed.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Complete third difference of the actual arithmetic selection energy. -/
def mobiusDivisorThirdEnergyDifference (M : ℕ) (P : Finset ℕ) (p q r : ℕ) : ℝ :=
  (mobiusDivisorSelectionEnergy M (insert q (insert p (insert r P)))-
    mobiusDivisorSelectionEnergy M (insert p (insert r P))-
    mobiusDivisorSelectionEnergy M (insert q (insert r P))+
    mobiusDivisorSelectionEnergy M (insert r P))-
  (mobiusDivisorSelectionEnergy M (insert q (insert p P))-
    mobiusDivisorSelectionEnergy M (insert p P)-
    mobiusDivisorSelectionEnergy M (insert q P)+
    mobiusDivisorSelectionEnergy M P)

/-- The complete third energy difference pairs every prime fibre with its
complementary fibre in the eight-coordinate source block. -/
theorem mobiusDivisorThirdEnergyDifference_eq (M : ℕ) (P : Finset ℕ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpM : p<M) (hqM : q<M) (hrM : r<M)
    (hpP : p∉P) (hqP : q∉P) (_hrP : r∉P)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    mobiusDivisorThirdEnergyDifference M P p q r =
      2*∑R∈((((mobiusDivisorSelectionPrimes M).erase q).erase p).erase r).powerset,
        (mobiusDivisorSelectionFibre M P R*
            mobiusDivisorSelectionFibre M P (insert p (insert q (insert r R)))+
          mobiusDivisorSelectionFibre M P (insert p R)*
            mobiusDivisorSelectionFibre M P (insert q (insert r R))+
          mobiusDivisorSelectionFibre M P (insert q R)*
            mobiusDivisorSelectionFibre M P (insert p (insert r R))+
          mobiusDivisorSelectionFibre M P (insert r R)*
            mobiusDivisorSelectionFibre M P (insert p (insert q R))) := by
  let U := ((mobiusDivisorSelectionPrimes M).erase q).erase p
  let T := (U.erase r).powerset
  have hrU : r∈U := by
    exact mem_erase.mpr ⟨hpr.symm,mem_erase.mpr ⟨hqr.symm,
      mem_filter.mpr ⟨mem_range.mpr hrM,hr⟩⟩⟩
  have hrR (R : Finset ℕ) (hR : R∈T) : r∉R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hsplit (f : Finset ℕ → ℝ) :
      (∑R∈U.powerset,f R)=∑R∈T,(f R+f (insert r R)) := by
    conv_lhs => rw [← insert_erase hrU]
    rw [sum_powerset_insert (notMem_erase r U),← sum_add_distrib]
  unfold mobiusDivisorThirdEnergyDifference
  rw [mobiusDivisorSelectionEnergy_mixed_eq M (insert r P) hp hq hpM hqM
      (by simp [hpr,hpP]) (by simp [hqr,hqP]) hpq,
    mobiusDivisorSelectionEnergy_mixed_eq M P hp hq hpM hqM hpP hqP hpq]
  change 2*(∑R∈U.powerset,_)-2*(∑R∈U.powerset,_)=_
  rw [hsplit,hsplit,← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro R hR
  simp only [mobiusDivisorSelectionFibre_insert,mem_insert,hrR R hR,
    hpr.symm,hqr.symm,false_or,true_or,if_false,if_true,mul_zero,add_zero]
  rw [Finset.insert_comm r q R,Finset.insert_comm r p R,
    Finset.insert_comm r p (insert q R),Finset.insert_comm r q R]
  ring

private lemma parity_product_nonpos (f : Finset ℕ → ℝ) (A B : Finset ℕ)
    (ha : 0≤(-1:ℝ)^A.card*f A) (hb : 0≤(-1:ℝ)^B.card*f B)
    (hodd : Odd (A.card+B.card)) : f A*f B≤0 := by
  have h := mul_nonneg ha hb
  have he : ((-1:ℝ)^A.card*f A)*((-1:ℝ)^B.card*f B)= -(f A*f B) := by
    calc
      _ = (-1:ℝ)^(A.card+B.card)*(f A*f B) := by rw [pow_add]; ring
      _ = _ := by rw [hodd.neg_one_pow]; ring
  rw [he] at h
  linarith only [h]

private lemma cross_three_nonpos (f : Finset ℕ → ℝ) (R : Finset ℕ) {p q r : ℕ}
    (hpR : p∉R) (hqR : q∉R) (hrR : r∉R)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (hparity : ∀V : Finset ℕ,V≠∅ → 0≤(-1:ℝ)^V.card*f V) :
    f (insert p R)*f (insert q (insert r R))+
      f (insert q R)*f (insert p (insert r R))+
      f (insert r R)*f (insert p (insert q R))≤0 := by
  have hc1 : (insert p R).card+(insert q (insert r R)).card=2*R.card+3 := by
    rw [card_insert_of_notMem hpR,card_insert_of_notMem (by simp [hqr,hqR]),
      card_insert_of_notMem hrR]
    omega
  have hc2 : (insert q R).card+(insert p (insert r R)).card=2*R.card+3 := by
    rw [card_insert_of_notMem hqR,card_insert_of_notMem (by simp [hpr,hpR]),
      card_insert_of_notMem hrR]
    omega
  have hc3 : (insert r R).card+(insert p (insert q R)).card=2*R.card+3 := by
    rw [card_insert_of_notMem hrR,card_insert_of_notMem (by simp [hpq,hpR]),
      card_insert_of_notMem hqR]
    omega
  have ho : Odd (2*R.card+3) := ⟨R.card+1,by omega⟩
  have h1 := parity_product_nonpos f (insert p R) (insert q (insert r R))
    (hparity _ (insert_nonempty _ _).ne_empty) (hparity _ (insert_nonempty _ _).ne_empty)
    (hc1.symm ▸ ho)
  have h2 := parity_product_nonpos f (insert q R) (insert p (insert r R))
    (hparity _ (insert_nonempty _ _).ne_empty) (hparity _ (insert_nonempty _ _).ne_empty)
    (hc2.symm ▸ ho)
  have h3 := parity_product_nonpos f (insert r R) (insert p (insert q R))
    (hparity _ (insert_nonempty _ _).ne_empty) (hparity _ (insert_nonempty _ _).ne_empty)
    (hc3.symm ▸ ho)
  linarith only [h1,h2,h3]

private lemma triple_zero (M : ℕ) (P R : Finset ℕ) {p q r : ℕ}
    (hpR : p∉R) (hqR : q∉R) (hrR : r∉R)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (hprime : ∀s∈R,s.Prime) (hprod : M≤p*q*r) :
    mobiusDivisorSelectionFibre M P (insert p (insert q (insert r R)))=0 := by
  apply mobiusDivisorSelectionFibre_eq_zero_of_le_product
  rw [prod_insert (by simp [hpq,hpr,hpR]),prod_insert (by simp [hqr,hqR]),prod_insert hrR]
  have hpos : 1≤∏s∈R,s := prod_pos (fun s hs => (hprime s hs).pos)
  calc
    M ≤ p*q*r := hprod
    _ = (p*q*r)*1 := by ring
    _ ≤ (p*q*r)*(∏s∈R,s) := Nat.mul_le_mul_left _ hpos
    _ = _ := by ring

/-- Every original three-prime mixed difference is nonpositive, retaining
all joint-product overlaps of the actual unsigned source. -/
theorem mobiusDivisorThirdEnergyDifference_empty_nonpos (M : ℕ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpM : p<M) (hqM : q<M) (hrM : r<M)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    mobiusDivisorThirdEnergyDifference M ∅ p q r≤0 := by
  rw [mobiusDivisorThirdEnergyDifference_eq M ∅ hp hq hr hpM hqM hrM
    (by simp) (by simp) (by simp) hpq hpr hqr]
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply sum_nonpos
  intro R hR
  have hrR : r∉R := fun h => (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hpR : p∉R := fun h => (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).1 rfl
  have hqR : q∉R := fun h =>
    (mem_erase.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).2).1 rfl
  have hc : R.card+(insert p (insert q (insert r R))).card=2*R.card+3 := by
    rw [card_insert_of_notMem (by simp [hpq,hpr,hpR]),
      card_insert_of_notMem (by simp [hqr,hqR]),card_insert_of_notMem hrR]
    omega
  have ho : Odd (2*R.card+3) := ⟨R.card+1,by omega⟩
  have h0 := parity_product_nonpos (mobiusDivisorSelectionFibre M ∅) R
    (insert p (insert q (insert r R)))
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M _)
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M _) (hc.symm ▸ ho)
  have hx := cross_three_nonpos (mobiusDivisorSelectionFibre M ∅) R hpR hqR hrR hpq hpr hqr
    (fun V _ => mobiusDivisorSelectionFibre_empty_parity_nonneg M V)
  linarith only [h0,hx]

/-- After any late-prime block, inactive joint triples have nonpositive
complete third difference even when the current head has reversed sign. -/
theorem mobiusDivisorThirdEnergyDifference_late_nonpos (M : ℕ) (P : Finset ℕ)
    (hP : ∀s∈P,s.Prime ∧ s<M ∧ M≤2*s) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpM : p<M) (hqM : q<M) (hrM : r<M)
    (hpP : p∉P) (hqP : q∉P) (hrP : r∉P)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (hprod : M≤p*q*r) :
    mobiusDivisorThirdEnergyDifference M P p q r≤0 := by
  rw [mobiusDivisorThirdEnergyDifference_eq M P hp hq hr hpM hqM hrM hpP hqP hrP hpq hpr hqr]
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply sum_nonpos
  intro R hR
  have hrR : r∉R := fun h => (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hpR : p∉R := fun h => (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).1 rfl
  have hqR : q∉R := fun h =>
    (mem_erase.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).2).1 rfl
  have hprime : ∀s∈R,s.Prime := by
    intro s hs
    exact (mem_filter.mp (mem_erase.mp (mem_erase.mp
      (mem_erase.mp (mem_powerset.mp hR hs)).2).2).2).2
  rw [triple_zero M P R hpR hqR hrR hpq hpr hqr hprime hprod,mul_zero,zero_add]
  exact cross_three_nonpos (mobiusDivisorSelectionFibre M P) R hpR hqR hrR hpq hpr hqr
    (mobiusDivisorSelectionFibre_late_parity_nonneg M P hP)

private lemma head_third (M : ℕ) (P : Finset ℕ) {p q r : ℕ}
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    (mobiusDivisorSelectionFibre M (insert q (insert p (insert r P))) ∅-
      mobiusDivisorSelectionFibre M (insert p (insert r P)) ∅-
      mobiusDivisorSelectionFibre M (insert q (insert r P)) ∅+
      mobiusDivisorSelectionFibre M (insert r P) ∅)-
    (mobiusDivisorSelectionFibre M (insert q (insert p P)) ∅-
      mobiusDivisorSelectionFibre M (insert p P) ∅-
      mobiusDivisorSelectionFibre M (insert q P) ∅+
      mobiusDivisorSelectionFibre M P ∅)=
      mobiusDivisorSelectionFibre M P (insert p (insert q {r})) := by
  simp only [mobiusDivisorSelectionFibre_insert,notMem_empty,if_false,insert_empty,
    mem_singleton,mem_insert,hpq,hpr.symm,hqr.symm,false_or]
  rw [Finset.insert_comm r p {q},show ({r,q}:Finset ℕ)={q,r} by ext x; simp [or_comm]]
  ring

/-- A complete late-prime block changes the third interaction exactly by
its signed mass times the original triple fibre. The processed core is
arbitrary and all triple overlaps are retained. -/
theorem mobiusDivisorThirdEnergyDifference_union_late_primes (M : ℕ) (P L : Finset ℕ)
    (hL : ∀s∈L,s.Prime ∧ s<M ∧ M≤2*s) (hfree : ∀s∈L,s∉P)
    {p q r : ℕ} (hpL : p∉L) (hqL : q∉L) (hrL : r∉L)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    mobiusDivisorThirdEnergyDifference M (P∪L) p q r =
      mobiusDivisorThirdEnergyDifference M P p q r+
      2*(∑s∈L,mobiusDivisorDilationChannel M s)*
        mobiusDivisorSelectionFibre M P (insert p (insert q {r})) := by
  let A := insert q (insert p (insert r P))
  have hLA : ∀s∈L,s∉A := by
    intro s hs
    simp only [A,mem_insert,not_or]
    exact ⟨(fun he => hqL (he ▸ hs)),(fun he => hpL (he ▸ hs)),
      (fun he => hrL (he ▸ hs)),hfree s hs⟩
  have htransport (C : Finset ℕ) (hC : C⊆A) :=
    mobiusDivisorSelectionEnergy_union_late_primes M C L hL
      (fun s hs hm => hLA s hs (hC hm))
  have hA : insert q (insert p (insert r P))⊆A := Subset.rfl
  have hprA : insert p (insert r P)⊆A := subset_insert _ _
  have hqrA : insert q (insert r P)⊆A := by
    intro s hs
    simp only [A,mem_insert] at hs ⊢
    tauto
  have hrA : insert r P⊆A := by
    intro s hs
    exact mem_insert_of_mem (mem_insert_of_mem hs)
  have hpqA : insert q (insert p P)⊆A := by
    intro s hs
    simp only [A,mem_insert] at hs ⊢
    tauto
  have hpA : insert p P⊆A := by
    intro s hs
    simp only [A,mem_insert] at hs ⊢
    tauto
  have hqA : insert q P⊆A := by
    intro s hs
    simp only [A,mem_insert] at hs ⊢
    tauto
  have hPA : P⊆A := by
    intro s hs
    exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem hs))
  unfold mobiusDivisorThirdEnergyDifference
  simp only [← insert_union]
  rw [htransport _ hA,htransport _ hprA,htransport _ hqrA,htransport _ hrA,
    htransport _ hpqA,htransport _ hpA,htransport _ hqA,htransport _ hPA]
  have hh := head_third M P hpq hpr hqr
  linear_combination 2*(∑s∈L,mobiusDivisorDilationChannel M s)*hh

/-- Once the joint triple lies outside the cutoff, arbitrary late-prime
blocks leave the whole third interaction unchanged, for every starting core. -/
theorem mobiusDivisorThirdEnergyDifference_union_late_eq_of_le_product
    (M : ℕ) (P L : Finset ℕ)
    (hL : ∀s∈L,s.Prime ∧ s<M ∧ M≤2*s) (hfree : ∀s∈L,s∉P)
    {p q r : ℕ} (hpL : p∉L) (hqL : q∉L) (hrL : r∉L)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) (hprod : M≤p*q*r) :
    mobiusDivisorThirdEnergyDifference M (P∪L) p q r =
      mobiusDivisorThirdEnergyDifference M P p q r := by
  rw [mobiusDivisorThirdEnergyDifference_union_late_primes M P L hL hfree
    hpL hqL hrL hpq hpr hqr]
  have hz := triple_zero M P ∅ (by simp) (by simp) (by simp)
    hpq hpr hqr (by simp) hprod
  simpa only [insert_empty,mul_zero,add_zero] using
    congrArg (fun t : ℝ => mobiusDivisorThirdEnergyDifference M P p q r+
      2*(∑s∈L,mobiusDivisorDilationChannel M s)*t) hz

/-- The complete third-interaction cost of an original late-prime block
is exactly twice its consumed unsigned mass times the literal joint
triple channel. This includes the active-overlap sector. -/
theorem mobiusDivisorThirdEnergyDifference_late_eq_unsigned
    (M : ℕ) (L : Finset ℕ) (hL : ∀s∈L,s.Prime ∧ s<M ∧ M≤2*s)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpL : p∉L) (hqL : q∉L) (hrL : r∉L)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    mobiusDivisorThirdEnergyDifference M L p q r =
      mobiusDivisorThirdEnergyDifference M ∅ p q r+
      2*(∑s∈L,divisorUnsignedDilationChannel M s)*
        divisorUnsignedDilationChannel M (p*q*r) := by
  have hsign : mobiusDivisorSelectionFibre M ∅ (insert p (insert q {r}))=
      -divisorUnsignedDilationChannel M (p*q*r) := by
    have hprime : ∀s∈(insert p (insert q {r}) : Finset ℕ),Nat.Prime s := by
      intro s hs
      simp only [mem_insert,mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact hp
      · exact hq
      · exact hr
    have h := mobiusDivisorOrientedFibre_empty_eq_unsigned_product _ hprime M
    have hc : (insert p (insert q {r}) : Finset ℕ).card=3 := by
      rw [card_insert_of_notMem (by simp [hpq,hpr]),card_insert_of_notMem (by simp [hqr])]
      simp
    have hd : (∏s∈(insert p (insert q {r}) : Finset ℕ),s)=p*q*r := by
      rw [prod_insert (by simp [hpq,hpr]),prod_insert (by simp [hqr]),prod_singleton]
      ring
    unfold mobiusDivisorOrientedFibre at h
    rw [hc,hd] at h
    norm_num at h
    linarith only [h]
  have hsum : (∑s∈L,mobiusDivisorDilationChannel M s)=
      -(∑s∈L,divisorUnsignedDilationChannel M s) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro s hs
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime (hL s hs).1]
    simp
  have h := mobiusDivisorThirdEnergyDifference_union_late_primes M ∅ L hL
    (by simp) hpL hqL hrL hpq hpr hqr
  rw [empty_union,hsum,hsign] at h
  convert! h using 1; ring

/-- The original negative third-order margin pays precisely the late
mass times the joint triple channel; no head-sign estimate replaces it. -/
theorem mobiusDivisorThirdEnergyDifference_late_nonpos_iff
    (M : ℕ) (L : Finset ℕ) (hL : ∀s∈L,s.Prime ∧ s<M ∧ M≤2*s)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpL : p∉L) (hqL : q∉L) (hrL : r∉L)
    (hpq : p≠q) (hpr : p≠r) (hqr : q≠r) :
    mobiusDivisorThirdEnergyDifference M L p q r≤0 ↔
      2*(∑s∈L,divisorUnsignedDilationChannel M s)*
        divisorUnsignedDilationChannel M (p*q*r)≤
          -mobiusDivisorThirdEnergyDifference M ∅ p q r := by
  rw [mobiusDivisorThirdEnergyDifference_late_eq_unsigned M L hL hp hq hr
    hpL hqL hrL hpq hpr hqr]
  constructor <;> intro h <;> linarith only [h]

end RHTower
