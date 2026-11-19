import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignOfCubeRootRows
import GaloisForLFunctions.RestrictedFactorizationCalculus.AlternatingCofactorDescent
import GaloisForLFunctions.QuantitativeFactorizationMatching.DyadicMatchingStripAndRiemannEquivalence
import GaloisForLFunctions.QuantitativeFactorizationMatching.AllFiniteLayersCellMatching

/-!
# Exact matching on the fourth-root rough block

A triple contracts to a semiprime in its own least-prime row. After every
triple has contracted, every remaining negative is a single prime and hence
adjacent to every remaining positive. These two sets of edges attain the
absolute signed imbalance on the entire growing block.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem cube_child {X y p : ℕ} (hX : 2*X ≤ y^4) (hp : p.Prime) (hy : y < p) :
    2*X/p ≤ p^3 := by
  have h := hX.trans (Nat.pow_le_pow_left hy.le 4)
  rw [show p^4=p^3*p from pow_succ p 3] at h
  exact (Nat.div_le_div_right h).trans_eq (Nat.mul_div_cancel _ hp.pos)

/-- Uniform room for every triple in every least-prime row, including rows
whose quotient interval has already become small. Such rows contain no triple. -/
theorem eventually_fourth_root_child_capacity :
    ∀ᶠ X : ℕ in atTop, ∀ y p : ℕ, 2*X ≤ y^4 → y < p → p.Prime →
      (compositeTails (X/p) (2*X/p) p).card ≤ (tailPrimes (X/p) (2*X/p) p).card := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_real_cube_root_surplus 0)
  let J := max 2 H
  have hJ : (2:ℝ) ≤ J := le_max_left _ _
  have hJ0 : 0 < J := by linarith only [hJ]
  filter_upwards [eventually_ge_atTop ⌈2*J^6*J^6⌉₊] with X hX
  intro y p hfour hyp hp
  let C := compositeTails (X/p) (2*X/p) p
  by_cases hC : C.Nonempty
  · obtain ⟨m,hm⟩ := hC
    have hU := cube_child hfour hp hyp
    obtain ⟨_,_,hmU,_,hpm⟩ := mem_roughTails.mp (mem_filter.mp hm).1
    obtain ⟨hm1,_,_,_,_⟩ := mem_roughTails.mp (mem_filter.mp hm).1
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    let T := (X:ℝ)/p
    have hT0 : 0 ≤ T := div_nonneg (Nat.cast_nonneg _) hp0.le
    have hXX : T*(p:ℝ)=X := div_mul_cancel₀ _ hp0.ne'
    have hpT : (p:ℝ) ≤ 2*T := by
      have hh := (Nat.le_div_iff_mul_le hp.pos).1
        ((hpm.le.trans (Nat.minFac_le (by omega))).trans hmU)
      change (p:ℝ) ≤ 2*((X:ℝ)/p)
      rw [←mul_div_assoc,le_div_iff₀ hp0]
      exact_mod_cast hh
    have hscale : J^6 ≤ T := by
      by_contra! hsmall
      have hx := (Nat.le_ceil (2*J^6*J^6)).trans (Nat.cast_le.mpr hX)
      have h₁ := mul_le_mul_of_nonneg_left hpT hT0
      have h₂ := mul_lt_mul_of_pos_right hsmall (show 0 < J^6+T by positivity)
      nlinarith only [hx,hXX,h₁,h₂]
    let s := T^(1/6:ℝ)
    have hs0 : 0 ≤ s := Real.rpow_nonneg hT0 _
    have hs6 : s^6=T := by dsimp [s]; rw [←Real.rpow_natCast,←Real.rpow_mul hT0]; norm_num
    have hJs : J ≤ s := (pow_le_pow_iff_left₀ hJ0.le hs0 (by decide : 6 ≠ 0)).1
      (hscale.trans_eq hs6.symm)
    have hLo : ⌊T⌋₊=X/p := by dsimp [T]; rw [Nat.floor_div_natCast,Nat.floor_natCast]
    have hHi : ⌊2*T⌋₊=2*X/p := by
      have h : 2*T=((2*X:ℕ):ℝ)/p := by dsimp [T]; push_cast; ring
      rw [h,Nat.floor_div_natCast,Nat.floor_natCast]
    have h := hH s ((le_max_right _ _).trans hJs) T (2*T) p hs6.le (by linarith only [hT0])
      (by rw [hs6]) (by rw [hs6,pow_zero,div_one]; linarith) (hHi ▸ hU)
    rw [hLo,hHi,cube_root_tail_balance _ _ _ hU] at h
    omega
  · change C.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hC,card_empty]
    exact Nat.zero_le _

/-- Raising the least-prime cutoff between the fourth root and the start of
the octave can only increase the signed balance. All removed children have
nonnegative balance, while the root prime count is constant. -/
theorem eventually_fourth_root_balance_monotone :
    ∀ᶠ X : ℕ in atTop, ∀ y z : ℕ, 2*X ≤ y^4 → y ≤ z → z ≤ X →
      tailBalance X (2*X) y ≤ tailBalance X (2*X) z := by
  filter_upwards [eventually_fourth_root_child_capacity] with X hX
  intro y z hy hyz hz
  let P := fun a => (Nat.primesLE (2*X)).filter (fun p => a < p)
  have hsub : P z ⊆ P y := by
    intro p hp
    obtain ⟨hm,hl⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hm,hyz.trans_lt hl⟩
  have hs : ∑ p ∈ P z, tailBalance (X/p) (2*X/p) p ≤
      ∑ p ∈ P y, tailBalance (X/p) (2*X/p) p := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p hm _
    obtain ⟨hp,hl⟩ := mem_filter.mp hm
    have hpr := (Nat.mem_primesLE.mp hp).2
    rw [cube_root_tail_balance _ _ _ (cube_child hy hpr hl)]
    exact sub_nonneg.mpr (Int.ofNat_le.mpr (hX y p hy hl hpr))
  rw [tailBalance_recursion X (2*X) y,tailBalance_recursion X (2*X) z,
    max_eq_left (hyz.trans hz),max_eq_left hz]
  exact sub_le_sub_left hs _

/-- The complementary tail and its sign after removing the least prime. -/
private theorem child_of_composite {L U y n : ℕ} (hn : n ∈ roughTails L U y) (hc : ¬n.Prime) :
    n/n.minFac ∈ roughTails (L/n.minFac) (U/n.minFac) n.minFac ∧
    n/n.minFac*n.minFac=n ∧ μ n = -μ (n/n.minFac) := by
  obtain ⟨m,hm,he⟩ := peel_composite_tail hn hc
  obtain ⟨hn1,_,_,hsq,_⟩ := mem_roughTails.mp hn
  have hp := Nat.minFac_prime hn1.ne'
  have hd : n/n.minFac=m := (congrArg (· / n.minFac) he.symm).trans (Nat.mul_div_cancel _ hp.pos)
  have hsq' : Squarefree (m*n.minFac) := (congrArg Squarefree he).mpr hsq
  have hcop := (Nat.squarefree_mul_iff.mp hsq').1
  rw [hd]
  refine ⟨hm,he,?_⟩
  calc μ n = μ (m*n.minFac) := congrArg (fun t => μ t) he.symm
       _ = _ := by rw [isMultiplicative_moebius.map_mul_of_coprime hcop,moebius_apply_prime hp]; ring

private theorem pair_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    μ (p*q) = 1 := by
  rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.coprime_primes hp hq).2 hpq.ne),
    moebius_apply_prime hp,moebius_apply_prime hq]
  decide

/-- Every positive fourth-root rough vertex consists of its least prime and one larger prime. -/
theorem positive_is_semiprime {X y n : ℕ} (hfour : 2*X ≤ y^4)
    (hn : n ∈ posParity (roughTails X (2*X) y)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n=p*q := by
  obtain ⟨ht,hμ⟩ := mem_filter.mp hn
  obtain ⟨hn1,_,_,_,hyp⟩ := mem_roughTails.mp ht
  have hp := Nat.minFac_prime hn1.ne'
  have hncomp : ¬n.Prime := fun h => by rw [moebius_apply_prime h] at hμ; contradiction
  obtain ⟨hm,hd,hsgn⟩ := child_of_composite ht hncomp
  have hprime : (n/n.minFac).Prime := by
    by_contra h
    obtain ⟨a,b,ha,hb,_,hab,he⟩ := cube_root_tail_pair (cube_child hfour hp hyp)
      (mem_filter.mpr ⟨hm,h⟩)
    rw [he,pair_mu ha hb hab] at hsgn
    omega
  obtain ⟨_,_,_,_,hgt⟩ := mem_roughTails.mp hm
  exact ⟨n.minFac,n/n.minFac,hp,hprime,by simpa only [hprime.minFac_eq] using hgt,
    hd.symm.trans (Nat.mul_comm ..)⟩

/-- Pair any specified family of negative triples inside their least-prime rows.
Only the rows represented in the family supply positive endpoints. -/
theorem match_selected_triples {X y : ℕ} (hfour : 2*X ≤ y^4)
    (hcap : ∀ p : ℕ, y < p → p.Prime →
      (compositeTails (X/p) (2*X/p) p).card ≤ (tailPrimes (X/p) (2*X/p) p).card)
    (D : Finset ℕ) (hD : D ⊆ (negParity (roughTails X (2*X) y)).filter (fun n => ¬n.Prime)) :
    ∃ A : OppositeParityMatching GlobalDyadicOneTwoRel (roughTails X (2*X) y),
      A.targets=D ∧ ∀ n ∈ A.sources, ∃ m ∈ D,n.minFac=m.minFac := by
  let S := roughTails X (2*X) y
  let P := fun p => tailPrimes (X/p) (2*X/p) p
  let C := fun p => compositeTails (X/p) (2*X/p) p
  let f := fun i : D => let p := (i:ℕ).minFac; rankedSlot (C p) (P p) ((i:ℕ)/p)*p
  have info (i : D) : f i ∈ posParity S ∧ GlobalDyadicOneTwoRel (f i) i ∧
      (f i).minFac=(i:ℕ).minFac ∧ (i:ℕ)/(i:ℕ).minFac ∈ C (i:ℕ).minFac := by
    obtain ⟨hn,hc⟩ := mem_filter.mp (hD i.property)
    obtain ⟨ht,hμ⟩ := mem_filter.mp hn
    obtain ⟨hn1,_,hnU,hsq,hyp⟩ := mem_roughTails.mp ht
    let p := (i:ℕ).minFac
    have hp : p.Prime := Nat.minFac_prime hn1.ne'
    have hpU := (Nat.minFac_le (by omega : 0 < (i:ℕ))).trans hnU
    obtain ⟨hm,hd,hsgn⟩ := child_of_composite ht hc
    have hw : (i:ℕ)/p ∈ C p := mem_filter.mpr ⟨hm,fun h => by
      rw [moebius_apply_prime h,hμ] at hsgn; contradiction⟩
    let z := rankedSlot (C p) (P p) ((i:ℕ)/p)
    obtain ⟨hz,hzpr⟩ := mem_tailPrimes.mp (rankedSlot_mem (hcap p hyp hp) hw)
    have hpz : p < z := by
      have hzmin := (mem_roughTails.mp hz).2.2.2.2
      simpa only [hzpr.minFac_eq] using hzmin
    have hrow : z*p ∈ S.filter (fun x => x.minFac=p) := by
      change z*p ∈ (roughTails X (2*X) y).filter (fun x => x.minFac=p)
      rw [roughTails_minFac_fibre hp hyp hpU]
      exact mem_union_right _ (mem_image.mpr ⟨z,hz,rfl⟩)
    have hμf : μ (z*p)=1 := by rw [Nat.mul_comm, pair_mu hp hzpr hpz]
    obtain ⟨a,b,ha,hb,_,hab,he⟩ := cube_root_tail_pair (cube_child hfour hp hyp) hw
    refine ⟨mem_filter.mpr ⟨(mem_filter.mp hrow).1,hμf⟩,?_,(mem_filter.mp hrow).2,hw⟩
    refine ⟨(mem_roughTails.mp (mem_filter.mp hrow).1).2.2.2.1,hsq,?_,p,z,a,b,hzpr,ha,hb,hab,
      Or.inl ⟨Nat.mul_comm _ _,?_⟩⟩
    · change μ (z*p) = - μ (i:ℕ)
      rw [hμf,hμ]; decide
    · calc (i:ℕ) = ((i:ℕ)/p)*p := hd.symm
           _ = p*(a*b) := by rw [he,Nat.mul_comm]
  have hinj : Function.Injective f := by
    intro i j h
    have he := (info i).2.2.1.symm.trans ((congrArg Nat.minFac h).trans (info j).2.2.1)
    let p := (i:ℕ).minFac
    have hp : p.Prime := Nat.minFac_prime (mem_roughTails.mp
      (mem_filter.mp (mem_filter.mp (hD i.property)).1).1).1.ne'
    have hy := (mem_roughTails.mp (mem_filter.mp (mem_filter.mp (hD i.property)).1).1).2.2.2.2
    have hwi := (info i).2.2.2
    have hwj := (info j).2.2.2
    dsimp only [f] at h
    rw [←he] at h hwj
    have hslot := Nat.eq_of_mul_eq_mul_right hp.pos h
    have hq := rankedSlot_inj (hcap p hy hp) hwi hwj hslot
    apply Subtype.ext
    calc (i:ℕ) = ((i:ℕ)/p)*p := (Nat.div_mul_cancel (Nat.minFac_dvd _)).symm
         _ = ((j:ℕ)/p)*p := congrArg (· * p) hq
         _ = (j:ℕ) := Nat.div_mul_cancel (show p ∣ (j:ℕ) by rw [show p=(j:ℕ).minFac from he]; exact Nat.minFac_dvd _)
  obtain ⟨A,hs,hA⟩ := matching_of_indexed_edges f Subtype.val hinj Subtype.val_injective
    (fun i => ⟨(info i).1,(mem_filter.mp (hD i.property)).1,(info i).2.1⟩)
  refine ⟨A,?_,?_⟩
  · rw [hA]
    ext n
    exact ⟨fun h => by obtain ⟨i,_,rfl⟩ := mem_image.mp h; exact i.property,
      fun hn => mem_image.mpr ⟨⟨n,hn⟩,mem_univ _,rfl⟩⟩
  · intro n hn
    rw [hs] at hn
    obtain ⟨i,_,rfl⟩ := mem_image.mp hn
    exact ⟨i,i.property,(info i).2.2.1⟩

/-- Uniformly in the roughness threshold, genuine one-to-two exchanges on the
whole fourth-root block attain the absolute Möbius imbalance. All remaining
negative vertices are primes. -/
theorem eventually_saturation_at_the_fourth_root :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 2*X ≤ y^4 →
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (roughTails X (2*X) y),
        (M.unmatchedSet.card:ℤ) = |tailBalance X (2*X) y| ∧
        ∀ n ∈ M.unmatchedSet, μ n = -1 → n.Prime := by
  filter_upwards [eventually_fourth_root_child_capacity] with X hX
  intro y hfour
  let S := roughTails X (2*X) y
  let D := (negParity S).filter (fun n => ¬n.Prime)
  obtain ⟨A,hD,_⟩ := match_selected_triples hfour (hX y · hfour) D Subset.rfl
  have hA (n : ℕ) (hn : n ∈ negParity S) (hc : ¬n.Prime) : n ∈ A.targets := hD ▸ mem_filter.mpr ⟨hn,hc⟩
  let H := A.unmatchedSet
  have hs : squarefreeOf S=S := filter_eq_self.mpr fun _ hn => (mem_roughTails.mp hn).2.2.2.1
  have hsmall : H ⊆ S := fun n hn => hs ▸ (mem_sdiff.mp hn).1
  have hsH : squarefreeOf H=H := filter_eq_self.mpr fun _ hn =>
    (mem_roughTails.mp (hsmall hn)).2.2.2.1
  have prime_left {n : ℕ} (hn : n ∈ H) (hμ : μ n = -1) : n.Prime := by
    by_contra hc
    exact (mem_sdiff.mp hn).2 (mem_union_right _ (hA n (mem_filter.mpr ⟨hsmall hn,hμ⟩) hc))
  -- A remaining negative prime is adjacent to every remaining positive semiprime.
  obtain ⟨F,hF⟩ := exists_fullOppositeParityMatching_unmatched_eq_abs_sum H
  let B : OppositeParityMatching GlobalDyadicOneTwoRel S := {
    sources := F.sources
    partner := F.partner
    injOn := F.injOn
    sources_subset := fun _ hn => mem_filter.mpr ⟨hsmall (mem_filter.mp (F.sources_subset hn)).1,
      (mem_filter.mp (F.sources_subset hn)).2⟩
    partner_mem := fun m hm => mem_filter.mpr ⟨hsmall (mem_filter.mp (F.partner_mem m hm)).1,
      (mem_filter.mp (F.partner_mem m hm)).2⟩
    adj := by
      intro m hm
      obtain ⟨hmH,hμm⟩ := mem_filter.mp (F.sources_subset hm)
      obtain ⟨hnH,hμn⟩ := mem_filter.mp (F.partner_mem m hm)
      obtain ⟨q,r,hq,hr,hqr,hpair⟩ := positive_is_semiprime hfour (mem_filter.mpr ⟨hsmall hmH,hμm⟩)
      exact ⟨(mem_roughTails.mp (hsmall hmH)).2.2.2.1,(mem_roughTails.mp (hsmall hnH)).2.2.2.1,
        by rw [hμm,hμn]; decide,1,F.partner m,q,r,prime_left hnH hμn,hq,hr,hqr,
        Or.inr ⟨(one_mul _).symm,by rw [one_mul,hpair]⟩⟩ }
  have hBF : B.matchedSet=F.matchedSet := rfl
  have hdis : Disjoint A.matchedSet B.matchedSet := by
    apply disjoint_left.mpr
    intro n ha hb
    rw [hBF] at hb
    exact (mem_sdiff.mp (hsH ▸ F.matchedSet_subset hb : n ∈ H)).2 ha
  let M := A.disjointUnion B hdis
  have hmatched := (A.disjointUnion_spec B hdis).1
  change M.matchedSet=_ at hmatched
  have hu : M.unmatchedSet=F.unmatchedSet := by
    change squarefreeOf S \ M.matchedSet = squarefreeOf H \ F.matchedSet
    rw [hsH,hmatched,hBF]
    change squarefreeOf S \ (A.matchedSet ∪ F.matchedSet) =
      (squarefreeOf S \ A.matchedSet) \ F.matchedSet
    ext n
    simp only [Finset.mem_sdiff,mem_union]
    tauto
  have hsub : A.matchedSet ⊆ S := hs ▸ A.matchedSet_subset
  have hsum : ∑ n ∈ H, μ n = ∑ n ∈ S, μ n := by
    change ∑ n ∈ squarefreeOf S \ A.matchedSet, μ n = _
    rw [hs,sum_sdiff_eq_sub hsub,A.sum_moebius_matchedSet,sub_zero]
  refine ⟨M,?_,fun n hn hμ => ?_⟩
  · rw [hu,hF,hsum,tailBalance,abs_neg]
  · rw [hu] at hn
    exact prime_left (hsH ▸ (mem_sdiff.mp hn).1) hμ

end GaloisForLFunctions.RestrictedFactorizationCalculus
