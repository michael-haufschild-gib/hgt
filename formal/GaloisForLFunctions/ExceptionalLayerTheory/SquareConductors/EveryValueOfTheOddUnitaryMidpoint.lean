import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOneSidedExtremaOfTheOddUnitaryMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RealizingTheUnitaryMidpointChambers
import GaloisForLFunctions.HTGeometry.ProuhetAlternating

/-!
# Complete cofinal range of the odd unitary midpoint

Give one block twice the base weight of a leaf. At that threshold the
only possible low-rank defects are maximal low-rank sets containing the
center. Tiny distinct binary perturbations order those sets without
ties. Moving the center through their thresholds realizes every possible
defect count on every prescribed odd prime support.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

private def score (S : Finset ℕ) := ∑ i ∈ S, (2:ℕ)^i

private theorem score_inj : Function.Injective score := by
  intro S T h
  have he := congrArg Nat.bitIndices h
  change (∑ i ∈ S, (2:ℕ)^i).bitIndices = (∑ i ∈ T, (2:ℕ)^i).bitIndices at he
  simp only [GaloisForLFunctions.bitIndices_sum_two_pow_finset] at he
  simpa only [sort_toFinset] using congrArg List.toFinset he

private theorem score_mono {S T : Finset ℕ} (h : S ⊆ T) : score S ≤ score T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => Nat.zero_le _

private theorem score_threshold (F : Finset (Finset ℕ)) {U j : ℕ}
    (hU : ∀ S ∈ F, score S ≤ U) (hj : j ≤ F.card) :
    ∃ t ≤ U+1, (F.filter (fun S => t ≤ score S)).card = j := by
  by_cases hz : j=0
  · subst j
    refine ⟨U+1,le_rfl,card_eq_zero.mpr ?_⟩
    exact eq_empty_iff_forall_notMem.mpr fun S h => (Nat.not_succ_le_self U)
      ((mem_filter.mp h).2.trans (hU S (mem_filter.mp h).1))
  let V := F.image score
  have hc : V.card = F.card := card_image_of_injective _ score_inj
  let i : Fin F.card := ⟨F.card-j,by omega⟩
  let e := V.orderEmbOfFin hc
  have hi : e i ∈ V := orderEmbOfFin_mem ..
  obtain ⟨S,hS,heS⟩ := mem_image.mp hi
  refine ⟨e i,heS ▸ (hU S hS).trans (Nat.le_succ U),?_⟩
  have he : V.filter (e i ≤ ·) = (Ici i).image e := by
    rw [←image_orderEmbOfFin_univ V hc,filter_image]
    congr 1
    ext k
    simp [e]
  have hfilter : V.filter (e i ≤ ·) = (F.filter (fun S => e i ≤ score S)).image score := filter_image
  rw [←card_image_of_injective _ score_inj,←hfilter,he,card_image_of_injective _ e.injective,Fin.card_Ici]
  change F.card-(F.card-j)=j
  omega

private def base (U : ℕ) : ℤ := 4*((U:ℤ)+2)

private def centerPrice (U t : ℕ) : ℤ := 2*base U+U+1-2*t

private def price (p U t a : ℕ) : ℤ := if a=p then centerPrice U t else base U+(2:ℤ)^a

private theorem price_on_leaves {p U t : ℕ} {A : Finset ℕ} (hp : p ∉ A) :
    ∑ a ∈ A, price p U t a = base U*A.card+score A := by
  calc _ = ∑ a ∈ A, (base U+(2:ℤ)^a) := sum_congr rfl fun a ha =>
             if_neg (fun he => hp (he ▸ ha))
       _ = _ := by simp only [score,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_sum,Nat.cast_pow,
                        Nat.cast_ofNat,mul_comm (A.card:ℤ)]

private theorem price_total {P : Finset ℕ} {p r U t : ℕ} (hp : p ∈ P) (hc : P.card=2*(r+1)+1)
    (hU : score (P.erase p)=U) :
    ∑ a ∈ P, price p U t a = (2*(r:ℤ)+4)*base U+2*U+1-2*t := by
  have he := add_sum_erase P (price p U t) hp
  rw [←he,price_on_leaves (notMem_erase _ _),hU,card_erase_of_mem hp,hc]
  simp only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    price,if_pos rfl,centerPrice]
  ring

private theorem leaf_test {P A : Finset ℕ} {p r U t : ℕ} (hp : p ∉ A)
    (hA : A ⊆ P.erase p) (hU : score (P.erase p)=U) (ht : t ≤ U+1) (hc : A.card ≤ r+1) :
    2*(∑ a ∈ A,price p U t a) < (2*(r:ℤ)+4)*base U+2*U+1-2*t := by
  have hsc : (score A : ℤ) ≤ U := by exact_mod_cast (score_mono hA).trans_eq hU
  have hcard : (A.card:ℤ) ≤ r+1 := by exact_mod_cast hc
  have ht' : (t:ℤ) ≤ U+1 := by exact_mod_cast ht
  have hB : 0 ≤ base U := by unfold base; positivity
  have hB' : base U=4*((U:ℤ)+2) := rfl
  rw [price_on_leaves hp]
  linarith only [mul_le_mul_of_nonneg_left hcard hB,hsc,ht',hB',Nat.cast_nonneg (R:=ℤ) U]

private theorem center_test {P A : Finset ℕ} {p r U t : ℕ} (hA : A ⊆ P.erase p)
    (hU : score (P.erase p)=U) (ht : t ≤ U+1) (hc : A.card ≤ r) :
    (2*(r:ℤ)+4)*base U+2*U+1-2*t < 2*(∑ a ∈ insert p A, price p U t a) ↔
      A.card=r ∧ t ≤ score A := by
  have hp : p ∉ A := fun h => notMem_erase p P (hA h)
  have hsc : (score A : ℤ) ≤ U := by exact_mod_cast (score_mono hA).trans_eq hU
  have hB : 0 ≤ base U := by unfold base; positivity
  have hB' : base U=4*((U:ℤ)+2) := rfl
  rw [sum_insert hp,price_on_leaves hp,price,if_pos rfl,centerPrice]
  by_cases he : A.card=r
  · rw [he,and_iff_right rfl,←Nat.cast_le (α:=ℤ)]
    constructor <;> intro h <;> linarith only [h]
  · have hc' : (A.card:ℤ)+1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_ne hc he)
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_left hc' hB
      exfalso
      linarith only [h,hm,hsc,hB',Nat.cast_nonneg (R:=ℤ) U,Nat.cast_nonneg (R:=ℤ) t]
    · rintro ⟨h,_⟩
      exact (he h).elim

/-- Prescribed cofinal realization of every oriented defect count. -/
theorem realize_odd_unitary_midpoint {P : Finset ℕ} {p r : ℕ} (hp : p ∈ P)
    (hP : ∀ a ∈ P, Nat.Prime a) (hc : P.card=2*(r+1)+1) {j : ℕ}
    (hj : j ≤ (2*(r+1)).choose r) (B : ℕ) :
    ∃ k > B, k.primeFactors=P ∧
      unitaryHalfWeight k = (-1:ℤ)^(r+1)*(((2*(r+1)).choose (r+1):ℤ)-2*j) := by
  let L := P.erase p
  let F := L.powersetCard r
  let U := score L
  have hf : F.card=(2*(r+1)).choose r := by rw [card_powersetCard,card_erase_of_mem hp,hc,Nat.add_sub_cancel]
  obtain ⟨t,ht,hj'⟩ := score_threshold F (U:=U) (fun S hs => score_mono (mem_powersetCard.mp hs).1) (hj.trans_eq hf.symm)
  let w (a : ℕ) : ℝ := price p U t a
  have hpos (a : ℕ) : 0 ≤ price p U t a := by
    unfold price centerPrice base
    split_ifs
    · have h : (t:ℤ) ≤ U+1 := by exact_mod_cast ht
      omega
    · positivity
  have htot := price_total (t:=t) hp hc (rfl : score L=U)
  have hodd (S : Finset ℕ) (hS : S ⊆ P) : ∑ a ∈ S, price p U t a ≠ ∑ a ∈ P \ S, price p U t a := by
    intro he
    have h := sum_sdiff hS (f := price p U t)
    rw [htot,←he] at h
    have hpar : (2*(r:ℤ)+4)*base U = 2*((r+2)*base U) := by ring
    rw [hpar] at h
    omega
  obtain ⟨k,hk,hPk,hC⟩ := unitary_chamber_cofinal ⟨_,hp⟩ hP w (fun a _ => by exact_mod_cast hpos a)
    (fun S hS he => hodd S hS (by exact_mod_cast he)) B
  let G := F.filter fun S => t ≤ score S
  have hsmall {S : Finset ℕ} (hS : S ⊆ P) :
      S ∉ smallUnitarySubsets k ↔ (2*(r:ℤ)+4)*base U+2*U+1-2*t < 2*(∑ a ∈ S,price p U t a) := by
    rw [hC,logChamber,mem_filter,mem_powerset,and_iff_right hS]
    change ¬(∑ a ∈ S, (price p U t a:ℝ)) < ∑ a ∈ P \ S, (price p U t a:ℝ) ↔ _
    norm_cast
    have h := sum_sdiff hS (f := price p U t)
    rw [htot] at h
    have hn := hodd S hS
    omega
  have heq : unitaryRankDefects k (r+1) = G.image (insert p) := by
    ext S
    have hmem : S ∈ unitaryRankDefects k (r+1) ↔ S ⊆ P ∧ S.card ≤ r+1 ∧ S ∉ smallUnitarySubsets k := by
      simp [unitaryRankDefects,hPk,and_assoc]
    rw [hmem,mem_image]
    constructor
    · rintro ⟨hS,hs,hdef⟩
      have hhot := (hsmall hS).mp hdef
      by_cases hpS : p ∈ S
      · let A := S.erase p
        have hA : A ⊆ L := erase_subset_erase _ hS
        have hcard : A.card ≤ r := by dsimp only [A]; rw [card_erase_of_mem hpS]; omega
        have hin : insert p A=S := insert_erase hpS
        rw [←hin] at hhot
        obtain ⟨ha,hts⟩ := (center_test hA (rfl : score L=U) ht hcard).mp hhot
        exact ⟨A,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hA,ha⟩,hts⟩,hin⟩
      · have hA : S ⊆ L := fun x hx => mem_erase.mpr ⟨fun he => hpS (he ▸ hx),hS hx⟩
        exact ((leaf_test hpS hA (rfl : score L=U) ht hs).not_gt hhot).elim
    · rintro ⟨A,hA,rfl⟩
      obtain ⟨hF,hscore⟩ := mem_filter.mp hA
      obtain ⟨hL,ha⟩ := mem_powersetCard.mp hF
      have hpa : p ∉ A := fun h => notMem_erase _ _ (hL h)
      have hS : insert p A ⊆ P := insert_subset hp (hL.trans (erase_subset ..))
      exact ⟨hS,by rw [card_insert_of_notMem hpa,ha],(hsmall hS).mpr
        ((center_test hL (rfl : score L=U) ht ha.le).mpr ⟨ha,hscore⟩)⟩
  have hinj : Set.InjOn (insert p) (G : Set (Finset ℕ)) := by
    intro A hA D hD he
    have hpa : p ∉ A := fun h => notMem_erase _ _ ((mem_powersetCard.mp (mem_filter.mp hA).1).1 h)
    have hpd : p ∉ D := fun h => notMem_erase _ _ ((mem_powersetCard.mp (mem_filter.mp hD).1).1 h)
    simpa only [erase_insert hpa,erase_insert hpd] using congrArg (·.erase p) he
  have hsum : ∑ S ∈ unitaryRankDefects k (r+1), (-1:ℤ)^S.card = j*(-1:ℤ)^(r+1) := by
    rw [heq,sum_image hinj]
    calc _ = ∑ _A ∈ G, (-1:ℤ)^(r+1) := by
              apply sum_congr rfl
              intro A hA
              obtain ⟨ha,hcard⟩ := mem_powersetCard.mp (mem_filter.mp hA).1
              rw [card_insert_of_notMem (fun h => notMem_erase _ _ (ha h)),hcard]
         _ = _ := by simp only [sum_const,nsmul_eq_mul]; rw [show G.card=j from hj']
  have h := unitaryHalfWeight_rank_formula k
  dsimp only at h
  rw [hPk,hc,if_neg (by omega),if_neg (by simp),show (2*(r+1)+1)/2=r+1 by omega,hsum] at h
  exact ⟨k,hk,hPk,h.trans (by ring)⟩

/-- Exact cofinal range on every prescribed odd prime support of size at least three. -/
theorem cofinal_range_of_odd_unitary_midpoint {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (r : ℕ) (hr : P.card=2*(r+1)+1) (v : ℤ) :
    (∀ B : ℕ, ∃ k > B, k.primeFactors=P ∧ unitaryHalfWeight k=v) ↔
      ∃ j ≤ (2*(r+1)).choose r, v=(-1:ℤ)^(r+1)*(((2*(r+1)).choose (r+1):ℤ)-2*j) := by
  constructor
  · intro H
    obtain ⟨k,_,hk,hv⟩ := H 0
    simpa only [hv,Nat.add_sub_cancel] using odd_unitary_midpoint_range_bound (hk.trans hr)
  · rintro ⟨j,hj,rfl⟩ B
    obtain ⟨p,hp⟩ := card_pos.mp (by omega : 0 < P.card)
    exact realize_odd_unitary_midpoint hp hP hr hj B

#print axioms realize_odd_unitary_midpoint
#print axioms cofinal_range_of_odd_unitary_midpoint

end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
