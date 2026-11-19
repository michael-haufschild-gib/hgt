import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedCrossingsBetweenTwoWalls
import GaloisForLFunctions.RestrictedFactorizationCalculus.LogarithmicSavingsForRestrictedExchanges

/-!
# Perfect completion at every sharp cutoff

A fixed squarefree nonunit can acquire a fresh partner beyond any threshold.
If that partner already belongs to a pair, its previous partner becomes
free. The new pair closes no later than the displaced pair. Iterating in
increasing order gives a perfect matching with no increase in any unpaid
prefix and arbitrarily sparse changes of old moving vertices.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Every squarefree nonunit has legal partners above every finite cutoff. -/
theorem arbitrarily_large_restricted_partner {n : ℕ} (hs : Squarefree n) (hn : 1<n) (T : ℕ) :
    ∃ y : ℕ,T<y ∧ GlobalDyadicOneTwoRel n y := by
  let p := n.minFac
  let c := n/p
  have hp : p.Prime := Nat.minFac_prime hn.ne'
  have hcp : c*p=n := Nat.div_mul_cancel (Nat.minFac_dvd _)
  have hsqcp : Squarefree (c*p) := (congrArg Squarefree hcp).mpr hs
  obtain ⟨hcop,hcs,_⟩ := Nat.squarefree_mul_iff.mp hsqcp
  have hc := Nat.pos_of_ne_zero hcs.ne_zero
  obtain ⟨q,hq,hqp⟩ := Nat.exists_infinite_primes (max n T+1)
  obtain ⟨r,hr,hrp⟩ := Nat.exists_infinite_primes (c*q+1)
  have hqT : T<q := (le_max_right ..).trans_lt (Nat.lt_of_succ_le hq)
  have hqc : c<q := (Nat.div_le_self n p).trans_lt ((le_max_left ..).trans_lt (Nat.lt_of_succ_le hq))
  have hcq : 0<c*q := Nat.mul_pos hc hqp.pos
  have hqr : q<r := (Nat.le_mul_of_pos_left _ hc).trans_lt (Nat.lt_of_succ_le hr)
  have copr {u v : ℕ} (hu : 0<u) (hv : v.Prime) (h : u<v) : u.Coprime v :=
    (hv.coprime_iff_not_dvd.2 (fun d => h.not_ge (Nat.le_of_dvd hu d))).symm
  have h1 := copr hc hqp hqc
  have h2 := copr hcq hrp (Nat.lt_of_succ_le hr)
  have hscq := Nat.squarefree_mul_iff.mpr ⟨h1,hcs,Irreducible.squarefree hqp⟩
  have hscqr := Nat.squarefree_mul_iff.mpr ⟨h2,hscq,Irreducible.squarefree hrp⟩
  refine ⟨c*q*r,hqT.trans_le ((Nat.le_mul_of_pos_left _ hc).trans (Nat.le_mul_of_pos_right _ hrp.pos)),
    hs,hscqr,?_,c,p,q,r,hp,hqp,hrp,hqr,Or.inl ⟨hcp.symm,Nat.mul_assoc ..⟩⟩
  calc μ n = μ (c*p) := congrArg (fun i => μ i) hcp.symm
       _ = -μ (c*q*r) := by
         rw [isMultiplicative_moebius.map_mul_of_coprime hcop,isMultiplicative_moebius.map_mul_of_coprime h2,
           isMultiplicative_moebius.map_mul_of_coprime h1,moebius_apply_prime hp,moebius_apply_prime hqp,moebius_apply_prime hrp]
         ring

private structure WholeMatching where
  move : ℕ → ℕ
  back : Function.Involutive move
  allowed : ∀ n,move n=n ∨ GlobalDyadicOneTwoRel n (move n)

private def reroute (F : ℕ → ℕ) (k y n : ℕ) :=
  if n=k then y else if n=y then k else if n=F y then n else F n

private theorem reroute_law (F : WholeMatching) {k y : ℕ} (hk : F.move k=k)
    (hky : k<y) (edge : GlobalDyadicOneTwoRel k y) (n : ℕ) :
    let G := reroute F.move k y
    G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) := by
  let G := reroute F.move k y
  have atK : G k=y := if_pos rfl
  have atY : G y=k := by simp [G,reroute,hky.ne']
  change G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))
  by_cases h : n=k
  · subst n; rw [atK,atY]; exact ⟨rfl,Or.inr edge⟩
  by_cases h' : n=y
  · subst n; rw [atY,atK]; exact ⟨rfl,Or.inr edge.symm⟩
  by_cases h'' : n=F.move y
  · have hn : G n=n := by simp only [G,reroute,if_neg h,if_neg h',if_pos h'']
    exact ⟨(congrArg G hn).trans hn,Or.inl hn⟩
  have hn : G n=F.move n := by simp only [G,reroute,if_neg h,if_neg h',if_neg h'']
  have b1 : F.move n ≠ k := fun e => h ((F.back n).symm.trans ((congrArg F.move e).trans hk))
  have b2 : F.move n ≠ y := fun e => h'' ((F.back n).symm.trans (congrArg F.move e))
  have b3 : F.move n ≠ F.move y := fun e => h' (F.back.injective e)
  rw [hn]
  exact ⟨by simp only [G,reroute,if_neg b1,if_neg b2,if_neg b3,F.back n],F.allowed n⟩

private theorem reroute_unpaid (F : WholeMatching) {k y : ℕ} (hk : F.move k=k) (hks : Squarefree k)
    (hky : k<y) (X : ℕ) : (prefixUnpaid (reroute F.move k y) X).card ≤ (prefixUnpaid F.move X).card := by
  let G := reroute F.move k y
  have atK : G k=y := if_pos rfl
  have atY : G y=k := by simp [G,reroute,hky.ne']
  have keep {n : ℕ} (hn : n ∈ prefixUnpaid G X) (hnz : n ≠ F.move y) (hy : n ≠ y) :
      n ∈ prefixUnpaid F.move X := by
    obtain ⟨hs,hu⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hs,?_⟩
    by_cases he : n=k
    · subst n; exact Or.inl hk
    · have heq : G n=F.move n := by simp only [G,reroute,if_neg he,if_neg hy,if_neg hnz]
      rwa [heq] at hu
  by_cases hx : X<y
  · apply card_le_card
    intro n hn
    obtain ⟨hs,hu⟩ := mem_filter.mp hn
    have hnx := (mem_Icc.mp (mem_filter.mp hs).1).2
    by_cases z : n=F.move y
    · exact mem_filter.mpr ⟨hs,Or.inr (by rw [z,F.back]; exact hx)⟩
    · exact keep hn z (hnx.trans_lt hx).ne
  have hcap := le_of_not_gt hx
  have away (n : ℕ) (hn : n ∈ prefixUnpaid G X) : n ≠ k ∧ n ≠ y := by
    have hu := (mem_filter.mp hn).2
    constructor
    · rintro rfl; rw [atK] at hu; omega
    · rintro rfl; rw [atY] at hu; omega
  let f := fun n : ℕ => if n=F.move y then k else n
  apply card_le_card_of_injOn f
  · intro n hn
    by_cases z : n=F.move y
    · rw [show f n=k from if_pos z]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hks.ne_zero,hky.le.trans hcap⟩,hks⟩,Or.inl hk⟩
    · rw [show f n=n from if_neg z]
      exact keep hn z (away n hn).2
  · intro n hn m hm he
    have an := (away n hn).1
    have am := (away m hm).1
    dsimp only [f] at he
    split_ifs at he <;> omega

private structure RepairSpec (F G : WholeMatching) (k b : ℕ) (E : Finset ℕ) : Prop where
  cost : E.card ≤ 2
  far : ∀ n ∈ E,max k b<n
  stable : ∀ n,n ∉ E → (n ≠ k ∨ F.move n ≠ n) → G.move n=F.move n
  covers : Squarefree k → 1<k → G.move k ≠ k
  unpaid : ∀ X,(prefixUnpaid G.move X).card ≤ (prefixUnpaid F.move X).card
  introduced : ∀ n,n<G.move n → G.move n ≠ F.move n → n=k ∧ b<G.move n

private theorem exists_repair (F : WholeMatching) (k b : ℕ) :
    ∃ G E,RepairSpec F G k b E := by
  by_cases fresh : Squarefree k ∧ 1<k ∧ F.move k=k
  · let V := max k b
    let A := ∑ n ∈ Icc 0 V,F.move n
    obtain ⟨y,hy,edge⟩ := arbitrarily_large_restricted_partner fresh.1 fresh.2.1 (max V A)
    have hVy : V<y := (le_max_left ..).trans_lt hy
    have hz : V<F.move y := by
      by_contra! h
      have hv := single_le_sum (f := F.move) (fun n (_ : n ∈ Icc 0 V) => Nat.zero_le (F.move n))
        (mem_Icc.mpr ⟨Nat.zero_le _,h⟩)
      rw [F.back y] at hv
      exact hy.not_ge (hv.trans (le_max_right ..))
    have hky := (le_max_left k b).trans_lt hVy
    have law := reroute_law F fresh.2.2 hky edge
    let G : WholeMatching := ⟨reroute F.move k y,fun n => (law n).1,fun n => (law n).2⟩
    refine ⟨G,{y,F.move y},⟨?_,?_,?_,?_,reroute_unpaid F fresh.2.2 fresh.1 hky,?_⟩⟩
    · exact (card_insert_le ..).trans (by simp)
    · intro n hn
      rcases mem_insert.mp hn with rfl | h
      · exact hVy
      · rw [mem_singleton.mp h]; exact hz
    · intro n hne hh
      obtain ⟨hy',hz'⟩ := (show n ≠ y ∧ n ≠ F.move y by simpa only [mem_insert,mem_singleton,not_or] using hne)
      have hk : n ≠ k := by rintro rfl; exact hh.elim (fun h => h rfl) (fun h => h fresh.2.2)
      simp only [G,reroute,if_neg hk,if_neg hy',if_neg hz']
    · intro _ _
      rw [show G.move k=y from if_pos rfl]; exact hky.ne'
    · intro n hup hnew
      by_cases he : n=k
      · subst n
        refine ⟨rfl,?_⟩
        rw [show G.move k=y from if_pos rfl]
        exact (le_max_right k b).trans_lt hVy
      by_cases hy' : n=y
      · subst n
        have hyk : G.move y=k := by simp [G,reroute,hky.ne']
        exact (hky.not_gt (hyk ▸ hup)).elim
      by_cases hz' : n=F.move y
      · have hzfix : G.move n=n := by simp only [G,reroute,if_neg he,if_neg hy',if_pos hz']
        exact (hup.ne' hzfix).elim
      exact (hnew (by simp only [G,reroute,if_neg he,if_neg hy',if_neg hz'])).elim
  · exact ⟨F,∅,⟨by simp,by simp,fun _ _ _ => rfl,fun hs hk hf => fresh ⟨hs,hk,hf⟩,
      fun _ => le_rfl,fun _ _ h => (h rfl).elim⟩⟩

private def nextMatching (F : WholeMatching) (k b : ℕ) := (exists_repair F k b).choose
private def changedAt (F : WholeMatching) (k b : ℕ) := (exists_repair F k b).choose_spec.choose
private theorem next_spec (F : WholeMatching) (k b : ℕ) :
    RepairSpec F (nextMatching F k b) k b (changedAt F k b) := (exists_repair F k b).choose_spec.choose_spec

private def advances (F : WholeMatching) (B : ℕ → ℕ) : ℕ → WholeMatching
  | 0 => F
  | k+1 => nextMatching (advances F B k) k (B k)

private theorem advances_stable (F : WholeMatching) (B : ℕ → ℕ) {n k l : ℕ} (hn : n<k) (hkl : k ≤ l) :
    (advances F B l).move n=(advances F B k).move n := by
  induction l,hkl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
    have h := next_spec (advances F B l) l (B l)
    have hn' := hn.trans_le hl
    exact (h.stable n (fun he => hn'.not_gt ((le_max_left ..).trans_lt (h.far n he))) (Or.inl hn'.ne)).trans ih

private def completed (F : WholeMatching) (B : ℕ → ℕ) (n : ℕ) := (advances F B (n+1)).move n

private theorem completed_at (F : WholeMatching) (B : ℕ → ℕ) {n k : ℕ} (h : n<k) :
    completed F B n=(advances F B k).move n := (advances_stable F B (Nat.lt_succ_self n) h).symm

private theorem completed_back (F : WholeMatching) (B : ℕ → ℕ) (n : ℕ) :
    completed F B (completed F B n)=n := by
  let G := completed F B
  let k := max n (G n)+1
  have h1 : n<k := Nat.lt_succ_of_le (le_max_left ..)
  have h2 : G n<k := Nat.lt_succ_of_le (le_max_right ..)
  exact (completed_at F B h2).trans ((congrArg (advances F B k).move (completed_at F B h1)).trans ((advances F B k).back n))

private theorem completed_unpaid (F : WholeMatching) (B : ℕ → ℕ) (X : ℕ) :
    (prefixUnpaid (completed F B) X).card ≤ (prefixUnpaid F.move X).card := by
  have he : prefixUnpaid (completed F B) X=prefixUnpaid (advances F B (X+1)).move X := by
    ext n
    simp only [prefixUnpaid,mem_filter]
    exact and_congr_right (fun hs => by rw [completed_at F B (Nat.lt_succ_of_le (mem_Icc.mp (mem_filter.mp hs).1).2)])
  rw [he]
  have h (k : ℕ) : (prefixUnpaid (advances F B k).move X).card ≤ (prefixUnpaid F.move X).card := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ((next_spec (advances F B k) k (B k)).unpaid X).trans ih
  exact h _

private theorem old_moves_change_sparsely (F : WholeMatching) (B : ℕ → ℕ) (X : ℕ) :
    ((Icc 1 X).filter (fun n => F.move n ≠ n ∧ completed F B n ≠ F.move n)).card ≤
      2*((range (X+1)).filter (fun k => B k<X)).card := by
  let E (j : ℕ) := changedAt (advances F B j) j (B j)
  have witness (k n : ℕ) (hmove : F.move n ≠ n) (hd : (advances F B k).move n ≠ F.move n) :
      ∃ j<k,n ∈ E j := by
    induction k with
    | zero => exact (hd rfl).elim
    | succ k ih =>
      by_cases h : n ∈ E k
      · exact ⟨k,Nat.lt_succ_self _,h⟩
      by_cases hh : (advances F B k).move n=F.move n
      · have hk : (advances F B k).move n ≠ n := fun e => hmove (hh.symm.trans e)
        exact (hd (((next_spec (advances F B k) k (B k)).stable n h (Or.inr hk)).trans hh)).elim
      obtain ⟨j,hj,hv⟩ := ih hh
      exact ⟨j,hj.trans (Nat.lt_succ_self _),hv⟩
  let I := (range (X+1)).filter (fun k => B k<X)
  have sub : (Icc 1 X).filter (fun n => F.move n ≠ n ∧ completed F B n ≠ F.move n) ⊆ I.biUnion E := by
    intro n hn
    obtain ⟨hi,hm,hd⟩ := mem_filter.mp hn
    obtain ⟨j,hj,he⟩ := witness (n+1) n hm hd
    have hx := (mem_Icc.mp hi).2
    have far := (le_max_right ..).trans_lt ((next_spec (advances F B j) j (B j)).far n he)
    exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_range.mpr (by omega),far.trans_le hx⟩,he⟩
  calc _ ≤ ∑ j ∈ I,(E j).card := (card_le_card sub).trans (card_biUnion_le ..)
       _ ≤ ∑ _j ∈ I,2 := sum_le_sum (fun j _ => (next_spec (advances F B j) j (B j)).cost)
       _ = _ := by simp [I,mul_comm]

private theorem completed_long (F : WholeMatching) (B : ℕ → ℕ) (n : ℕ)
    (h : n<completed F B n) : completed F B n=F.move n ∨ B n<completed F B n := by
  have step (k : ℕ) (up : n<(advances F B k).move n) :
      (advances F B k).move n=F.move n ∨ B n<(advances F B k).move n := by
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      by_cases eq : (advances F B (k+1)).move n=(advances F B k).move n
      · rw [eq] at up ⊢
        exact ih up
      obtain ⟨he,far⟩ := (next_spec (advances F B k) k (B k)).introduced n up eq
      exact Or.inr ((congrArg B he).trans_lt far)
  exact step (n+1) h

/-- Every global restricted matching can cover all squarefree nonunits
without increasing any unsigned unpaid prefix. A freely chosen growth
threshold controls changes to its original moving population. -/
theorem perfect_completion_with_separated_edges (F : ℕ → ℕ) (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (B : ℕ → ℕ) :
    ∃ G : ℕ → ℕ, Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ X,(prefixUnpaid G X).card ≤ (prefixUnpaid F X).card) ∧
      (∀ n,n<G n → G n=F n ∨ B n<G n) ∧
      ∀ X,((Icc 1 X).filter (fun n => F n ≠ n ∧ G n ≠ F n)).card ≤
        2*((range (X+1)).filter (fun k => B k<X)).card := by
  let M : WholeMatching := ⟨F,back,legal⟩
  exact ⟨completed M B,completed_back M B,fun n => (advances M B (n+1)).allowed n,
    fun n => (next_spec (advances M B n) n (B n)).covers,completed_unpaid M B,completed_long M B,old_moves_change_sparsely M B⟩

/-- A perfect completion weakly decreases every unpaid prefix and changes
at most two previously moving endpoints per repair below its threshold. -/
theorem perfect_completion_at_every_cutoff (F : ℕ → ℕ) (back : Function.Involutive F)
    (legal : ∀ n,F n=n ∨ GlobalDyadicOneTwoRel n (F n)) (B : ℕ → ℕ) :
    ∃ G : ℕ → ℕ, Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ X,(prefixUnpaid G X).card ≤ (prefixUnpaid F X).card) ∧
      ∀ X,((Icc 1 X).filter (fun n => F n ≠ n ∧ G n ≠ F n)).card ≤
        2*((range (X+1)).filter (fun k => B k<X)).card := by
  obtain ⟨G,hG,law,covers,cost,_,changes⟩ := perfect_completion_with_separated_edges F back legal B
  exact ⟨G,hG,law,covers,cost,changes⟩

/-- A decrease in unpaid cardinality removes exactly the same number of
vertices of either sign at each cutoff. -/
theorem unpaid_signs_of_smaller_prefix {F G : ℕ → ℕ}
    (hF : ∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (hG : ∀ n,Squarefree n → G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)))
    (X : ℕ) (h : (prefixUnpaid G X).card ≤ (prefixUnpaid F X).card) :
    let S := prefixUnpaid F X
    let T := prefixUnpaid G X
    (posParity T).card ≤ (posParity S).card ∧ (negParity T).card ≤ (negParity S).card ∧
      (posParity S).card-(posParity T).card=(negParity S).card-(negParity T).card := by
  let S := prefixUnpaid F X
  let T := prefixUnpaid G X
  have size (J : ℕ → ℕ) :
      (prefixUnpaid J X).card=(posParity (prefixUnpaid J X)).card+(negParity (prefixUnpaid J X)).card := by
    have hs : squarefreeOf (prefixUnpaid J X)=prefixUnpaid J X := filter_eq_self.mpr
      (fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).2)
    simpa only [hs] using card_squarefreeOf (prefixUnpaid J X)
  have eq := ((sum_moebius_eq_card_pos_sub_neg S).symm.trans (prefix_switch_balance F hF X).symm).trans
    ((prefix_switch_balance G hG X).trans (sum_moebius_eq_card_pos_sub_neg T))
  change (posParity T).card ≤ (posParity S).card ∧ (negParity T).card ≤ (negParity S).card ∧ _
  rw [size G,size F] at h
  change (posParity T).card+(negParity T).card ≤ (posParity S).card+(negParity S).card at h
  dsimp only [S,T] at *
  omega

/-- The unit admits no restricted prime exchange. -/
theorem restricted_unit_is_fixed (G : ℕ → ℕ) (legal : ∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) :
    G 1=1 := by
  rcases legal 1 with h | he
  · exact h
  obtain ⟨_,_,_,c,p,q,r,hp,hq,_,_,h⟩ := he
  rcases h with ⟨hn,_⟩ | ⟨_,hn⟩
  · have hd : p ∣ 1 := hn ▸ Nat.dvd_mul_left p c
    exact False.elim (hp.ne_one (Nat.dvd_one.mp hd))
  · have hd : q*r ∣ 1 := hn ▸ Nat.dvd_mul_left (q*r) c
    exact False.elim (hq.ne_one (Nat.dvd_one.mp ((Nat.dvd_mul_right q r).trans hd)))

/-- In a perfect restricted matching the fixed charge is the contribution of the unit. -/
theorem only_unit_charge {G : ℕ → ℕ} (hunit : G 1=1)
    (cover : ∀ n,Squarefree n → 1<n → G n ≠ n) (X : ℕ) :
    fixedSignedPrefix G X=if X=0 then 0 else 1 := by
  by_cases hX : X=0
  · simp [hX,fixedSignedPrefix,squarefreeOf]
  have hs : (squarefreeOf (Icc 1 X)).filter (fun n => G n=n)={1} := by
    ext n
    constructor
    · intro h
      obtain ⟨hi,hfix⟩ := mem_filter.mp h
      obtain ⟨hI,hsq⟩ := mem_filter.mp hi
      have hn := (mem_Icc.mp hI).1
      exact mem_singleton.mpr (by by_contra ne; exact cover n hsq (by omega) hfix)
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,Nat.pos_of_ne_zero hX⟩,squarefree_one⟩,hunit⟩
  simp [fixedSignedPrefix,hs,hX]

/-- Every squarefree nonunit moves in one global matching with a logarithmic
saving at every large cutoff. Its signed crossing count is exactly the Mertens
prefix minus the unit. The growth threshold controls how few old moving
vertices need to change to obtain this completion. -/
theorem logarithmic_saving_with_only_crossing_edges (B : ℕ → ℕ) :
    ∃ G : ℕ → ℕ, Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ n,Squarefree n → 1<n → G n ≠ n) ∧
      (∀ X,crossingSignedPrefix G X=coprimeMoebiusSum 1 X-(if X=0 then 0 else 1)) ∧
      (∀ X,(prefixUnpaid G X).card ≤ (prefixUnpaid dyadicPrimeSwitch X).card) ∧
      (∀ X,((Icc 1 X).filter (fun n => dyadicPrimeSwitch n ≠ n ∧ G n ≠ dyadicPrimeSwitch n)).card ≤
        2*((range (X+1)).filter (fun k => B k<X)).card) ∧
      ∃ c K : ℝ,0<c ∧ 0<K ∧ ∀ᶠ X : ℕ in atTop,
        ((prefixUnpaid G X).card:ℝ) ≤ K*X/(Real.log X)^c := by
  obtain ⟨hI,hF,_,_⟩ := one_involution_with_sublinear_unpaid_prefix
  obtain ⟨G,hG,legal,cover,count,changes⟩ := perfect_completion_at_every_cutoff _ hI hF B
  obtain ⟨c,K,hc,hK,hbound⟩ := logarithmic_saving_for_one_involution
  refine ⟨G,hG,legal,cover,?_,count,changes,c,K,hc,hK,?_⟩
  · intro X
    have h := fixed_add_crossing G (fun n _ => ⟨hG n,legal n⟩) X
    rw [only_unit_charge (restricted_unit_is_fixed G legal) cover] at h
    linarith only [h]
  · filter_upwards [hbound] with X hx
    exact (Nat.cast_le.mpr (count X)).trans hx.1

#print axioms arbitrarily_large_restricted_partner
#print axioms unpaid_signs_of_smaller_prefix
#print axioms perfect_completion_with_separated_edges
#print axioms perfect_completion_at_every_cutoff
#print axioms logarithmic_saving_with_only_crossing_edges

end GaloisForLFunctions.RestrictedFactorizationCalculus
