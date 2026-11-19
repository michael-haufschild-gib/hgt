import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange
import GaloisForLFunctions.RestrictedFactorizationCalculus.DensityOneForRestrictedPrimeExchanges
import GaloisForLFunctions.ArithmeticElectrostatics.TheSelfIntersectionOfATorsionOrbit

/-!
# One sparse fixed set with the full Möbius power spectrum

In each range one marked semiprime exchange can be kept or omitted. The
difference of the two resulting divisor sums detects every sharp power
bound. Selecting the heavier growth class at each step leaves one actual
involution whose fixed signed prefix detects all exponents simultaneously.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def omittedFactors (J k : ℕ) := (switchModulus k).divisors \ bandEndpoints J k
private def variant (J k w : ℕ) (T : Finset ℕ) :=
  T=omittedFactors J k ∨ T=insert w (insert (bandPartner J k w) (omittedFactors J k))

private def fixedClasses (I : Finset ℕ) (A : ℕ → Finset ℕ) :=
  (exchangePeriod I).divisors.filter (fun d => ∀ k ∈ I, d.gcd (switchModulus k) ∈ A k)

private theorem classes_congr {I : Finset ℕ} {A B : ℕ → Finset ℕ}
    (h : ∀ k ∈ I,A k=B k) : fixedClasses I A=fixedClasses I B := by
  ext d
  simp only [fixedClasses,mem_filter]
  exact and_congr_right (fun _ => forall_congr' fun k => forall_congr' fun hk => by rw [h k hk])

private theorem classes_insert {I : Finset ℕ} {k : ℕ} (hk : k ∉ I)
    (hc : (switchModulus k).Coprime (exchangePeriod I))
    (A : ℕ → Finset ℕ) (hA : A k ⊆ (switchModulus k).divisors) (G : ℕ → ℝ) :
    divisorPrefix (fixedClasses (insert k I) A) G =
      divisorPrefix (A k) (divisorPrefix (fixedClasses I A) G) := by
  let P := switchModulus k
  let Q := exchangePeriod I
  have hprod : exchangePeriod (insert k I)=P*Q := prod_insert hk
  have hfilter : P.divisors.filter (· ∈ A k)=A k := by
    ext a; exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨hA h,h⟩⟩
  funext X
  simp only [divisorPrefix,fixedClasses,sum_filter]
  rw [hprod,sum_divisors_mul_of_coprime hc,←hfilter,sum_filter]
  apply sum_congr rfl
  intro a ha
  have haP := Nat.dvd_of_mem_divisors ha
  have hcopA := Nat.Coprime.coprime_dvd_left haP hc
  have split (b : ℕ) (hb : b ∈ Q.divisors) :
      (∀ j ∈ insert k I, (a*b).gcd (switchModulus j) ∈ A j) ↔
      a ∈ A k ∧ ∀ j ∈ I,b.gcd (switchModulus j) ∈ A j := by
    have hbQ := Nat.dvd_of_mem_divisors hb
    have hak : (a*b).gcd (switchModulus k)=a := (Nat.Coprime.gcd_mul_right_cancel _
      (Nat.Coprime.coprime_dvd_left hbQ hc.symm)).trans (Nat.gcd_eq_left haP)
    have hbi (j : ℕ) (hj : j ∈ I) : (a*b).gcd (switchModulus j)=b.gcd (switchModulus j) :=
      Nat.Coprime.gcd_mul_left_cancel _ (Nat.Coprime.coprime_dvd_right (divides_period hj) hcopA)
    rw [forall_mem_insert,hak]
    exact and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hj => by rw [hbi j hj]
  by_cases haa : a ∈ A k
  · rw [if_pos haa,mul_sum]
    apply sum_congr rfl
    intro b hb
    by_cases hh : ∀ j ∈ I,b.gcd (switchModulus j) ∈ A j
    · rw [if_pos ((split b hb).2 ⟨haa,hh⟩),if_pos hh,isMultiplicative_moebius.map_mul_of_coprime
          (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hb) hcopA),
          Int.cast_mul,Nat.div_div_eq_div_mul,mul_assoc]
    · rw [if_neg (fun h => hh ((split b hb).1 h).2),if_neg hh,mul_zero]
  · rw [if_neg haa]
    exact sum_eq_zero (fun b hb => if_neg (fun h => haa ((split b hb).1 h).1))

private theorem variants_subset {J k w : ℕ} (hr : bandReady J k) (hw : w ∈ switchProducts k)
    {T : Finset ℕ} (h : variant J k w T) : T ⊆ (switchModulus k).divisors := by
  have hd := table_pair_divisors_and_signs hr hw
  have hM := (switchModulus_spec k).2.2.ne'
  rcases h with rfl | rfl
  · exact sdiff_subset
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact Nat.mem_divisors.mpr ⟨hd.1,hM⟩
    rcases mem_insert.mp ha with rfl | ha
    · exact Nat.mem_divisors.mpr ⟨hd.2.1,hM⟩
    exact (Finset.mem_sdiff.mp ha).1

private theorem choose_classes {J : ℕ} (I : Finset ℕ) (w : ℕ → ℕ)
    (hR : ∀ k ∈ I,bandReady J k) (hw : ∀ k ∈ I,w k ∈ switchProducts k)
    (hco : ∀ i ∈ I,∀ j ∈ I,i ≠ j → (switchModulus i).Coprime (switchModulus j))
    (G : ℕ → ℝ) (h0 : G 0=0) :
    ∃ A : ℕ → Finset ℕ, (∀ k ∈ I,variant J k (w k) (A k)) ∧
      ∀ θ : ℝ, 0<θ → (PrefixPower θ (divisorPrefix (fixedClasses I A) G) ↔ PrefixPower θ G) := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ∅,by simp,fun θ _ => ?_⟩
    have he : fixedClasses ∅ (fun _ => ∅)={1} := by simp [fixedClasses,exchangePeriod]
    rw [he]
    have hf : divisorPrefix {1} G=G := by funext x; simp [divisorPrefix]
    rw [hf]
  | @insert k I hk ih =>
    have inside {i : ℕ} (hi : i ∈ I) : i ∈ insert k I := mem_insert_of_mem hi
    have here : k ∈ insert k I := mem_insert_self ..
    have hpair (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) := hco i (inside hi) j (inside hj)
    obtain ⟨A,hA,hpow⟩ := ih (fun _ hi => hR _ (inside hi)) (fun _ hi => hw _ (inside hi)) hpair
    let F := divisorPrefix (fixedClasses I A) G
    have hF0 : F 0=0 := by simp [F,divisorPrefix,h0]
    have hr := hR k here
    have hmark := hw k here
    let p := bandPartner J k (w k)
    obtain ⟨_,_,hμw,hμp⟩ := table_pair_divisors_and_signs hr hmark
    have hp := (mem_switchPrimes.mp (hr.1.2 _ hmark).1).1
    have hwpos : 0<w k := by
      obtain ⟨q,hq,r,hr',_,he⟩ := (hr.1.2 _ hmark).2.1
      rw [he]; exact Nat.mul_pos (mem_switchPrimes.mp hq).1.pos (mem_switchPrimes.mp hr').1.pos
    have hne : w k ≠ p := fun h => by change μ p = -1 at hμp; rw [h] at hμw; omega
    have hn₁ : w k ∉ omittedFactors J k := fun h => (Finset.mem_sdiff.mp h).2 (mem_union_left _ hmark)
    have hn₂ : p ∉ omittedFactors J k := fun h => (Finset.mem_sdiff.mp h).2
      (mem_union_right _ (mem_image_of_mem _ hmark))
    obtain ⟨T,ht,hpwr⟩ := choose_pair_preserving_every_power (omittedFactors J k) hwpos hp.pos hne
      hn₁ hn₂ hμw hμp hF0
    let B := Function.update A k T
    have hb : B k=T := Function.update_self ..
    have heq (i : ℕ) (hi : i ∈ I) : B i=A i :=
      Function.update_of_ne (show i ≠ k from fun h => hk (h ▸ hi)) T A
    refine ⟨B,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · rw [hb]; exact ht
      · rw [heq _ hi]; exact hA _ hi
    · intro θ hθ
      have hc : (switchModulus k).Coprime (exchangePeriod I) := Nat.Coprime.prod_right
        (fun j hj => hco k here j (inside hj) (fun h => hk (h ▸ hj)))
      rw [classes_insert hk hc B (hb ▸ variants_subset hr hmark ht),hb,classes_congr heq]
      exact (hpwr θ hθ).trans (hpow θ hθ)

private def chosenBands (I : Finset ℕ) (A : ℕ → Finset ℕ) (n : ℕ) :=
  I.filter (fun k => n.gcd (switchModulus k) ∉ A k)

private def chosenSwitch (J : ℕ) (I : Finset ℕ) (A : ℕ → Finset ℕ) (n : ℕ) :=
  if h : (chosenBands I A n).Nonempty then switchInteger J ((chosenBands I A n).min' h) n else n

/-- A scalar preserving the full gcd preserves every selected band and scales both endpoints. -/
private theorem chosenSwitch_mul {I : Finset ℕ} (J : ℕ) (A : ℕ → Finset ℕ) {c : ℕ}
    (n : ℕ) (hc : (c*n).gcd (exchangePeriod I)=n.gcd (exchangePeriod I)) :
    chosenSwitch J I A (c*n)=c*chosenSwitch J I A n := by
  have gcd_eq (k : ℕ) (hk : k ∈ I) : (c*n).gcd (switchModulus k)=n.gcd (switchModulus k) := by
    simpa only [Nat.gcd_assoc,Nat.gcd_eq_right (divides_period hk)] using
      congrArg (fun a : ℕ => a.gcd (switchModulus k)) hc
  have he : chosenBands I A (c*n)=chosenBands I A n := by
    ext k
    simp only [chosenBands,mem_filter]
    exact and_congr_right fun hk => by rw [gcd_eq k hk]
  by_cases ha : (chosenBands I A n).Nonempty
  · let k := (chosenBands I A n).min' ha
    have hki : k ∈ I := (mem_filter.mp (min'_mem _ ha)).1
    have ha' : (chosenBands I A (c*n)).Nonempty := he ▸ ha
    have hk' : (chosenBands I A (c*n)).min' ha'=k := by dsimp only [k]; congr 1
    simp only [chosenSwitch,dif_pos ha',dif_pos ha,hk']
    change switchInteger J k (c*n)=c*switchInteger J k n
    simp only [switchInteger,gcd_eq k hki,Nat.mul_div_assoc c (Nat.gcd_dvd_left n (switchModulus k)),Nat.mul_assoc]
  · have hn : ¬(chosenBands I A (c*n)).Nonempty := fun h => ha (he ▸ h)
    simp only [chosenSwitch,dif_neg hn,dif_neg ha]

private theorem chosen_edge {J k w n : ℕ} {T : Finset ℕ} (hr : bandReady J k)
    (hw : w ∈ switchProducts k) (hT : variant J k w T) (hn : Squarefree n)
    (hact : n.gcd (switchModulus k) ∉ T) :
    let m := switchInteger J k n
    GlobalDyadicOneTwoRel n m ∧ m.gcd (switchModulus k) ∉ T ∧ switchInteger J k m=n ∧
      |(m:ℝ)-n| ≤ (n:ℝ)/J ∧ ∀ Q : ℕ,(switchModulus k).Coprime Q → m.gcd Q=n.gcd Q := by
  let P := switchModulus k
  let d := n.gcd P
  let m := switchInteger J k n
  let e := m.gcd P
  have hdiv : d ∈ P.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,(switchModulus_spec k).2.2.ne'⟩
  have hbase : omittedFactors J k ⊆ T := by
    rcases hT with rfl | rfl
    · exact Subset.rfl
    · exact (subset_insert ..).trans (subset_insert ..)
  have hd : d ∈ bandEndpoints J k := by
    by_contra h
    exact hact (hbase (Finset.mem_sdiff.mpr ⟨hdiv,h⟩))
  obtain ⟨hedge,he,hback,hnear,hstable⟩ := switchInteger_on_endpoint hr hn hd
  refine ⟨hedge,?_,hback,hnear,hstable⟩
  have heno : e ∉ omittedFactors J k := fun hh => (Finset.mem_sdiff.mp hh).2 he
  rcases hT with rfl | rfl
  · exact heno
  · have hnd : ¬(d=w ∨ d=bandPartner J k w) := by
      rintro (hh | hh)
      · exact hact (mem_insert.mpr (Or.inl hh))
      · exact hact (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl hh))))
    have different {v z : ℕ} (hv : v ∈ switchProducts k) (hz : z ∈ switchProducts k) :
        v ≠ bandPartner J k z := by
      intro hh
      have h1 := (table_pair_divisors_and_signs hr hv).2.2.1
      have h2 := (table_pair_divisors_and_signs hr hz).2.2.2
      rw [hh] at h1
      omega
    obtain ⟨v,hv,hve⟩ := switchInteger_gcd_pair hr hn hd
    let p := bandPartner J k
    have equ : (v=w ∨ v=p w) ↔ (p v=w ∨ p v=p w) := by
      simp only [show v ≠ p w from different hv hw,show p v ≠ w from (different hw hv).symm,
        or_false,false_or]
      exact ⟨congrArg p,hr.1.1 hv hw⟩
    have hnmark : ¬(e=w ∨ e=p w) := by
      rcases hve with ⟨hv',he'⟩ | ⟨hv',he'⟩
      · change d=v at hv'
        change e=p v at he'
        rw [he']
        exact fun hx => hnd (by rw [hv']; exact equ.mpr hx)
      · change d=p v at hv'
        change e=v at he'
        rw [he']
        exact fun hx => hnd (by rw [hv']; exact equ.mp hx)
    intro hh
    rcases mem_insert.mp hh with h | h
    · exact hnmark (Or.inl h)
    rcases mem_insert.mp h with h | h
    · exact hnmark (Or.inr h)
    · exact heno h

private theorem switch_selected {J n : ℕ} {I : Finset ℕ} {A : ℕ → Finset ℕ} {w : ℕ → ℕ}
    (hr : ∀ k ∈ I,bandReady J k) (hw : ∀ k ∈ I,w k ∈ switchProducts k)
    (hA : ∀ k ∈ I,variant J k (w k) (A k))
    (hco : ∀ i ∈ I,∀ j ∈ I,i ≠ j → (switchModulus i).Coprime (switchModulus j))
    (hn : Squarefree n) :
    let F := chosenSwitch J I A
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ (n:ℝ)/J ∧
      (F n=n ↔ ∀ k ∈ I,n.gcd (switchModulus k) ∈ A k) := by
  let F := chosenSwitch J I A
  change F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ (n:ℝ)/J ∧ _
  by_cases ha : (chosenBands I A n).Nonempty
  · let k := (chosenBands I A n).min' ha
    have hk : k ∈ chosenBands I A n := min'_mem _ ha
    obtain ⟨hki,hact⟩ := mem_filter.mp hk
    have hnF : F n=switchInteger J k n := dif_pos ha
    obtain ⟨edge,he,back,near,stable⟩ := chosen_edge (hr k hki) (hw k hki) (hA k hki) hn hact
    have hs : chosenBands I A (F n)=chosenBands I A n := by
      ext j
      simp only [chosenBands,mem_filter,hnF]
      refine and_congr_right fun hj => ?_
      by_cases h : k=j
      · subst j; exact iff_of_true he hact
      · rw [stable _ (hco k hki j hj h)]
    have ha' : (chosenBands I A (F n)).Nonempty := hs ▸ ha
    have hk' : (chosenBands I A (F n)).min' ha'=k := by dsimp only [k]; congr 1
    have hback : F (F n)=n := by
      change chosenSwitch J I A (F n)=n
      rw [chosenSwitch,dif_pos ha',hk',hnF]
      exact back
    have hdiff : F n ≠ n := by
      intro hh
      have h := edge.2.2.1
      rw [←hnF,hh] at h
      rcases moebius_eq_one_or_neg_one_of_squarefree hn with h1 | h1 <;> omega
    exact ⟨hback,Or.inr (hnF ▸ edge),hnF ▸ near,iff_of_false hdiff (fun h => hact (h k hki))⟩
  · have hf : F n=n := dif_neg ha
    have hall : ∀ k ∈ I,n.gcd (switchModulus k) ∈ A k := by
      intro k hk
      by_contra h
      exact ha ⟨k,mem_filter.mpr ⟨hk,h⟩⟩
    refine ⟨(congrArg F hf).trans hf,Or.inl hf,?_,iff_of_true hf hall⟩
    rw [hf,sub_self,abs_zero]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem sq_period (I : Finset ℕ)
    (hco : ∀ i ∈ I,∀ j ∈ I,i ≠ j → (switchModulus i).Coprime (switchModulus j)) :
    Squarefree (exchangePeriod I) := by
  induction I using Finset.induction_on with
  | empty => simp [exchangePeriod]
  | @insert k I hk ih =>
    have hi {i : ℕ} (h : i ∈ I) : i ∈ insert k I := mem_insert_of_mem h
    have hpair (i : ℕ) (h : i ∈ I) (j : ℕ) (hj : j ∈ I) := hco i (hi h) j (hi hj)
    have hkp : (switchModulus k).Coprime (exchangePeriod I) :=
      Nat.Coprime.prod_right (fun j hj => hco k (mem_insert_self ..) j (hi hj) (fun h => hk (h ▸ hj)))
    change Squarefree (∏ j ∈ insert k I,switchModulus j)
    rw [prod_insert hk]
    exact Nat.squarefree_mul_iff.mpr ⟨hkp,(switchModulus_spec k).1,ih hpair⟩

private def fixedPopulation (F : ℕ → ℕ) (X : ℕ) :=
  (squarefreeOf (Icc 1 X)).filter (fun n => F n=n)

private theorem fixed_spectrum {J : ℕ} {I : Finset ℕ} {A : ℕ → Finset ℕ} {w : ℕ → ℕ}
    (hr : ∀ k ∈ I,bandReady J k) (hw : ∀ k ∈ I,w k ∈ switchProducts k)
    (hA : ∀ k ∈ I,variant J k (w k) (A k))
    (hco : ∀ i ∈ I,∀ j ∈ I,i ≠ j → (switchModulus i).Coprime (switchModulus j))
    (X : ℕ) :
    ∑ n ∈ fixedPopulation (chosenSwitch J I A) X,(μ n:ℝ) =
      divisorPrefix (fixedClasses I A) (coprimeMoebiusSum (exchangePeriod I)) X := by
  let Q := exchangePeriod I
  let V := (Icc 1 X).filter (fun n => n.gcd Q ∈ fixedClasses I A)
  have hc (n : ℕ) : n.gcd Q ∈ fixedClasses I A ↔ ∀ k ∈ I,n.gcd (switchModulus k) ∈ A k := by
    have hd : n.gcd Q ∈ Q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,(period_pos I).ne'⟩
    simp only [fixedClasses,mem_filter]
    change (n.gcd Q ∈ Q.divisors ∧ ∀ k ∈ I,(n.gcd Q).gcd (switchModulus k) ∈ A k) ↔ _
    rw [and_iff_right hd]
    exact forall_congr' fun k => forall_congr' fun hk => by rw [Nat.gcd_assoc,Nat.gcd_eq_right (divides_period hk)]
  have he : fixedPopulation (chosenSwitch J I A) X=V.filter Squarefree := by
    ext n
    simp only [fixedPopulation,squarefreeOf,V,mem_filter,hc]
    constructor
    · rintro ⟨⟨hi,hs⟩,hf⟩
      exact ⟨⟨hi,(switch_selected hr hw hA hco hs).2.2.2.mp hf⟩,hs⟩
    · rintro ⟨⟨hi,ha⟩,hs⟩
      exact ⟨⟨hi,hs⟩,(switch_selected hr hw hA hco hs).2.2.2.mpr ha⟩
  rw [he]
  apply Eq.trans _ (signed_prefix_of_gcd_classes (E := fixedClasses I A) (filter_subset _ _) X)
  apply sum_subset (filter_subset _ _)
  intro n hn hno
  rw [moebius_eq_zero_of_not_squarefree (fun h => hno (mem_filter.mpr ⟨hn,h⟩)),Int.cast_zero]

private theorem mark_large {J k u : ℕ} (hJ : 0<J) (hr : bandReady J k) (hu : u ∈ switchProducts k) :
    J ≤ bandPartner J k u := by
  let p := bandPartner J k u
  obtain ⟨_,_,huμ,hpμ⟩ := table_pair_divisors_and_signs hr hu
  have hne : p ≠ u := fun h => by change μ p = -1 at hpμ; rw [h] at hpμ; omega
  have hgap : 1 ≤ |(p:ℝ)-u| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (p:ℝ)+1 ≤ u := by exact_mod_cast Nat.succ_le_of_lt h
      linarith only [hh,neg_le_abs ((p:ℝ)-u)]
    · have hh : (u:ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt h
      linarith only [hh,le_abs_self ((p:ℝ)-u)]
  have hh := (le_div_iff₀ (Nat.cast_pos.mpr hJ : (0:ℝ)<J)).1
    (hgap.trans (hr.1.2 u hu).2.2.2)
  exact Nat.cast_le.mp (by simpa only [one_mul] using hh : (J:ℝ) ≤ p)

private theorem chosen_unpaid_bound {J : ℕ} (hJ : 0<J) (I : Finset ℕ) (A : ℕ → Finset ℕ) (w : ℕ → ℕ)
    (hr : ∀ k ∈ I,bandReady J k) (hw : ∀ k ∈ I,w k ∈ switchProducts k)
    (hA : ∀ k ∈ I,variant J k (w k) (A k))
    (hco : ∀ i ∈ I,∀ j ∈ I,i ≠ j → (switchModulus i).Coprime (switchModulus j)) (X : ℕ) :
    ((prefixUnpaid (chosenSwitch J I A) X).card:ℝ) ≤
      ((missedClasses J I).card:ℝ)*((X:ℝ)/(exchangePeriod I)+1) + (I.card+1:ℝ)*(X:ℝ)/J+1 := by
  let F := chosenSwitch J I A
  let p := fun k => bandPartner J k (w k)
  let E := (Icc 1 X).filter (missesSingles J I)
  let H := fun k => (Icc 1 X).filter (p k ∣ ·)
  let d := ⌈(X:ℝ)/J⌉₊
  let T := Ioc (X-d) X
  have hJr : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  have hsub : prefixUnpaid F X ⊆ (E ∪ I.biUnion H) ∪ T := by
    intro n hn
    obtain ⟨hs,hfixed⟩ := mem_filter.mp hn
    obtain ⟨hi,hsq⟩ := mem_filter.mp hs
    obtain ⟨_,_,hnear,hfix⟩ := switch_selected hr hw hA hco hsq
    rcases hfixed with hf | hcross
    · apply mem_union_left
      by_cases hmiss : missesSingles J I n
      · exact mem_union_left _ (mem_filter.mpr ⟨hi,hmiss⟩)
      · change ¬∀ k ∈ I,n.gcd (switchModulus k) ∉ (switchProducts k).image (bandPartner J k) at hmiss
        push Not at hmiss
        obtain ⟨k,hk,hin⟩ := hmiss
        obtain ⟨v,hv,hsg⟩ := mem_image.mp hin
        have hall := hfix.mp hf k hk
        have hno : n.gcd (switchModulus k) ∉ omittedFactors J k := fun h =>
          (Finset.mem_sdiff.mp h).2 (mem_union_right _ hin)
        have hne : n.gcd (switchModulus k) ≠ w k := by
          intro hh
          have h1 := (table_pair_divisors_and_signs (hr k hk) (hw k hk)).2.2.1
          have h2 := (table_pair_divisors_and_signs (hr k hk) hv).2.2.2
          rw [hsg,hh] at h2
          omega
        rcases hA k hk with he | he
        · rw [he] at hall; exact (hno hall).elim
        · rw [he] at hall
          have hgp := (mem_insert.mp ((mem_insert.mp hall).resolve_left hne)).resolve_right hno
          have hdvd := Nat.gcd_dvd_left n (switchModulus k)
          rw [hgp] at hdvd
          exact mem_union_right _ (mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨hi,hdvd⟩⟩)
    · obtain ⟨hl,hu⟩ := mem_Icc.mp hi
      have hcap := ((abs_le.mp hnear).2).trans
        ((div_le_div_of_nonneg_right (Nat.cast_le.mpr hu) hJr.le).trans (Nat.le_ceil _))
      have hcross' : (X:ℝ)<F n := by exact_mod_cast hcross
      have hreal : (X:ℝ)<(n:ℝ)+d := by
        change (F n:ℝ)-n ≤ d at hcap
        linarith only [hcross',hcap]
      have hgap : X < n+d := by exact_mod_cast hreal
      exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hu⟩)
  have hmul (k : ℕ) (hk : k ∈ I) : ((H k).card:ℝ) ≤ (X:ℝ)/J := by
    have hJp := mark_large hJ (hr k hk) (hw k hk)
    have hp : 0 < p k := hJ.trans_le hJp
    have hh := RHTower.sum_Icc_dvd_reindex (p k) X hp (fun _ => (1:ℕ))
    simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel] at hh
    change (((Icc 1 X).filter (p k ∣ ·)).card:ℝ) ≤ _
    have count : ((Icc 1 X).filter (p k ∣ ·)).card=X/p k := hh
    exact (Nat.cast_le.mpr count.le).trans (Nat.cast_div_le.trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg X) hJr (Nat.cast_le.mpr hJp)))
  have hcost := (card_le_card hsub).trans ((card_union_le ..).trans
    (Nat.add_le_add_right ((card_union_le ..).trans (Nat.add_le_add_left (card_biUnion_le ..) _)) _))
  have hcr := (Nat.cast_le (α := ℝ)).mpr hcost
  push_cast only [Nat.cast_sum,Nat.cast_add] at hcr
  have hsum := sum_le_sum hmul
  rw [sum_const,nsmul_eq_mul] at hsum
  have hd : T.card ≤ d := by dsimp [T]; rw [Nat.card_Ioc]; omega
  have hceil : (d:ℝ)<(X:ℝ)/J+1 := Nat.ceil_lt_add_one (by positivity)
  have hm := missed_upto J X I
  change (E.card:ℝ) ≤ _ at hm
  apply hcr.trans
  calc _ ≤ (missedClasses J I).card*((X:ℝ)/(exchangePeriod I)+1) +
          I.card*((X:ℝ)/J) + ((X:ℝ)/J+1) :=
         add_le_add (add_le_add hm hsum) (((Nat.cast_le (α := ℝ)).mpr hd).trans hceil.le)
       _ = _ := by ring

/-- A finite divisor table detects all positive Mertens powers at prescribed
sparsity. The complete gcd with its modulus determines the local partner. -/
theorem finite_divisor_table_detecting_every_mertens_power {ε : ℝ} (hε : 0<ε) :
    ∃ Q : ℕ, Squarefree Q ∧ ∃ F : ℕ → ℕ, (∀ n : ℕ,F n=(n/n.gcd Q)*F (n.gcd Q)) ∧
      (∀ n : ℕ, Squarefree n → F (F n)=n ∧
        (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ ε*n) ∧
      (∀ X : ℕ, ∑ n ∈ Icc 1 X,μ n = ∑ n ∈ prefixUnpaid F X,μ n) ∧
      (∀ᶠ X : ℕ in atTop, ((prefixUnpaid F X).card:ℝ) ≤ ε*X) ∧
      ∀ θ : ℝ, 0<θ →
        (PrefixPower θ (fun X => ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => F n=n),(μ n:ℝ)) ↔
         PrefixPower θ (fun X => ∑ n ∈ Icc 1 X,(μ n:ℝ))) := by
  obtain ⟨m,hm⟩ : ∃ m : ℕ,(1-coveredFraction)^m < ε/4 :=
    exists_pow_lt_of_lt_one (by positivity) (by linarith only [coveredFraction_pos])
  obtain ⟨J,hJbig⟩ := exists_nat_gt (4*((m:ℝ)+1)/ε)
  have hJr : (0:ℝ)<J := (div_pos (by positivity) hε).trans hJbig
  have hJ := Nat.cast_pos.mp hJr
  have hbudget : ((m:ℝ)+1)/(J:ℝ) ≤ ε/4 := by
    apply (div_le_iff₀ hJr).2
    linarith only [((div_lt_iff₀ hε).1 hJbig)]
  obtain ⟨L,hL⟩ := eventually_atTop.mp (eventually_bandReady J hJ)
  obtain ⟨I,hcard,_,hR,hco,hfrac⟩ := packing_within J (L+1) (Nat.succ_pos _) (fun k hk => hL k (by omega)) m
  let Q := exchangePeriod I
  let B := missedClasses J I
  have hQ : (0:ℝ)<Q := Nat.cast_pos.mpr (period_pos I)
  have hratio : (B.card:ℝ)/Q ≤ ε/4 := ((div_le_iff₀ hQ).2 hfrac).trans hm.le
  have exists_mark (k : ℕ) (hk : k ∈ I) : (switchProducts k).Nonempty := by
    by_contra h
    have ht := (hR k hk).2
    rw [not_nonempty_iff_eq_empty.mp h,image_empty,sum_empty] at ht
    norm_num at ht
  let w (k : ℕ) : ℕ := if h : k ∈ I then (exists_mark k h).choose else 0
  have hw (k : ℕ) (hk : k ∈ I) : w k ∈ switchProducts k := by
    simpa only [w,dif_pos hk] using (exists_mark k hk).choose_spec
  have h0 : coprimeMoebiusSum Q 0=0 := by simp [coprimeMoebiusSum]
  obtain ⟨A,hA,hpow⟩ := choose_classes I w hR hw hco (coprimeMoebiusSum Q) h0
  let F := chosenSwitch J I A
  have inv (n : ℕ) (hn : Squarefree n) := switch_selected hR hw hA hco hn
  have hwidth : 1/(J:ℝ) ≤ ε := by
    have hh := div_le_div_of_nonneg_right (show (1:ℝ) ≤ (m:ℝ)+1 by linarith only [Nat.cast_nonneg (α := ℝ) m]) hJr.le
    linarith only [hh,hbudget,hε]
  have scaled (n : ℕ) : F n=(n/n.gcd Q)*F (n.gcd Q) := by
    have hn := Nat.div_mul_cancel (Nat.gcd_dvd_left n Q)
    have hh : ((n/n.gcd Q)*n.gcd Q).gcd Q=(n.gcd Q).gcd Q := by
      rw [hn,Nat.gcd_eq_left (Nat.gcd_dvd_right n Q)]
    exact (congrArg F hn.symm).trans (chosenSwitch_mul J A (n.gcd Q) hh)
  refine ⟨Q,sq_period I hco,F,scaled,fun n hn => ⟨(inv n hn).1,(inv n hn).2.1,((inv n hn).2.2.1).trans ?_⟩,
    prefix_switch_balance _ (fun n hn => ⟨(inv n hn).1,(inv n hn).2.1⟩),?_,?_⟩
  · calc (n:ℝ)/J=(1/(J:ℝ))*n := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop ⌈4*((B.card:ℝ)+1)/ε⌉₊] with X hX
    have hfree := chosen_unpaid_bound hJ I A w hR hw hA hco X
    rw [hcard] at hfree
    change ((prefixUnpaid F X).card:ℝ) ≤ (B.card:ℝ)*((X:ℝ)/Q+1)+((m:ℝ)+1)*X/J+1 at hfree
    have hbase := (div_le_iff₀ hε).1 ((Nat.le_ceil (4*((B.card:ℝ)+1)/ε)).trans (Nat.cast_le.mpr hX))
    have hres := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (α := ℝ) X)
    have hmark := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) X)
    apply hfree.trans
    calc _ = (B.card:ℝ)/Q*X + (((m:ℝ)+1)/J)*X + ((B.card:ℝ)+1) := by ring
         _ ≤ (ε/4)*X + (ε/4)*X + ((B.card:ℝ)+1) := add_le_add (add_le_add hres hmark) le_rfl
         _ ≤ ε*X := by linarith only [hbase,mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) X)]
  · intro θ hθ
    have he := funext (fixed_spectrum hR hw hA hco)
    have hM : coprimeMoebiusSum 1=(fun X => ∑ n ∈ Icc 1 X,(μ n:ℝ)) := by
      funext X
      simp [coprimeMoebiusSum,coprimeMoebiusIndicator]
    change PrefixPower θ (fun X => ∑ n ∈ fixedPopulation F X,(μ n:ℝ)) ↔ _
    rw [he,←hM]
    exact (hpow θ hθ).trans (coprime_prefix_preserves_every_power (sq_period I hco) hθ)

/-- One short involution has an arbitrarily sparse unpaid population and
its fixed signed prefix detects every positive power, including the endpoint. -/
theorem one_sparse_fixed_set_detects_every_mertens_power {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℕ → ℕ, (∀ n : ℕ, Squarefree n → F (F n)=n ∧
        (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ ε*n) ∧
      (∀ X : ℕ, ∑ n ∈ Icc 1 X,μ n = ∑ n ∈ prefixUnpaid F X,μ n) ∧
      (∀ᶠ X : ℕ in atTop, ((prefixUnpaid F X).card:ℝ) ≤ ε*X) ∧
      ∀ θ : ℝ, 0<θ →
        (PrefixPower θ (fun X => ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => F n=n),(μ n:ℝ)) ↔
         PrefixPower θ (fun X => ∑ n ∈ Icc 1 X,(μ n:ℝ))) := by
  obtain ⟨_,_,F,_,hF⟩ := finite_divisor_table_detecting_every_mertens_power hε
  exact ⟨F,hF⟩

#print axioms finite_divisor_table_detecting_every_mertens_power
#print axioms one_sparse_fixed_set_detects_every_mertens_power

end GaloisForLFunctions.RestrictedFactorizationCalculus
