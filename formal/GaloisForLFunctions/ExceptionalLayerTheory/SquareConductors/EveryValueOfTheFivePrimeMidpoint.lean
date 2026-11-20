import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheNegativeRankFiveMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RealizingTheUnitaryMidpointChambers

/-!
# Every five-prime midpoint value on every prescribed support

Give the four leaves weights 8 or 9, and the center weight 15+h, where
h is the number of 9s. Total weight 47+2h is odd. The only overweight
subsets of size at most two are the h pairs joining the center to a 9.
Approximating this chamber by prime powers realizes the chosen star and
its value 6−2h arbitrarily far out on the same primes.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

private def price (p : ℕ) (U : Finset ℕ) (j : ℕ) : ℕ :=
  8+(if j ∈ U then 1 else 0)+(if j=p then 7+U.card else 0)

private theorem price_sum (p : ℕ) (U S : Finset ℕ) :
    ∑ j ∈ S, price p U j = 8*S.card+(S ∩ U).card+(if p ∈ S then 7+U.card else 0) := by
  simp only [price,sum_add_distrib,sum_const,nsmul_eq_mul,sum_ite_eq',←sum_filter,
    filter_mem_eq_inter, mul_one,mul_comm S.card 8]

private theorem pair_test {S U : Finset ℕ} {p : ℕ} (hp : p ∉ U) (hc : S.card ≤ 2) :
    47+2*U.card < 2*(∑ j ∈ S, price p U j) ↔
      ∃ x ∈ U, S = {p,x} := by
  rw [price_sum]
  have hcard := card_le_card (inter_subset_left (s₁:=S) (s₂:=U))
  constructor
  · intro h
    by_cases hpS : p ∈ S
    · rw [if_pos hpS] at h
      have hb : 1 ≤ (S ∩ U).card := by omega
      obtain ⟨x,hx⟩ := card_pos.mp hb
      obtain ⟨hxS,hxU⟩ := mem_inter.mp hx
      have hpx : p ≠ x := fun he => hp (he ▸ hxU)
      refine ⟨x,hxU,(eq_of_subset_of_card_le (insert_subset hpS (singleton_subset_iff.mpr hxS)) ?_).symm⟩
      simpa [hpx] using hc
    · rw [if_neg hpS] at h
      omega
  · rintro ⟨x,hx,rfl⟩
    have hpx : p ≠ x := fun he => hp (he ▸ hx)
    simp only [mem_insert_self,if_true,card_insert_of_notMem (by simpa using hpx : p ∉ ({x}:Finset ℕ)),
      card_singleton]
    have hmem : x ∈ ({p,x}:Finset ℕ) ∩ U := mem_inter.mpr ⟨by simp,hx⟩
    have := card_pos.mpr ⟨_,hmem⟩
    omega

private theorem five_defect_star {P U : Finset ℕ} {p k : ℕ} (hp : p ∈ P)
    (hU : U ⊆ P.erase p) (h5 : P.card=5) (hs : k.primeFactors=P)
    (hC : smallUnitarySubsets k = logChamber P (fun j => (price p U j:ℝ))) :
    unitaryRankDefects k 2 = U.image (fun x => ({p,x}:Finset ℕ)) := by
  have hsub := hU.trans (erase_subset _ _)
  have hpu : p ∉ U := fun h => notMem_erase _ _ (hU h)
  have htotal : ∑ j ∈ P, price p U j = 47+2*U.card := by
    rw [price_sum,h5,inter_eq_right.mpr hsub,if_pos hp]
    omega
  have hsmall {S : Finset ℕ} (hS : S ⊆ P) :
      S ∈ smallUnitarySubsets k ↔ 2*(∑ j ∈ S,price p U j) < 47+2*U.card := by
    rw [hC,logChamber,mem_filter,mem_powerset,and_iff_right hS]
    have hadd := sum_sdiff hS (f := price p U)
    rw [htotal] at hadd
    norm_cast
    omega
  ext S
  have hd : S ∈ unitaryRankDefects k 2 ↔ S ⊆ P ∧ S.card ≤ 2 ∧ S ∉ smallUnitarySubsets k := by
    simp [unitaryRankDefects,hs,and_assoc]
  rw [hd,mem_image]
  constructor
  · rintro ⟨hS,hcard,hn⟩
    rw [hsmall hS] at hn
    obtain ⟨x,hx,he⟩ := (pair_test hpu hcard).mp (by omega)
    exact ⟨x,hx,he.symm⟩
  · rintro ⟨x,hx,rfl⟩
    have hpx : p ≠ x := fun he => hpu (he ▸ hx)
    have hS : ({p,x}:Finset ℕ) ⊆ P := insert_subset hp (singleton_subset_iff.mpr (hsub hx))
    have hcard : ({p,x}:Finset ℕ).card ≤ 2 := by simp [hpx]
    exact ⟨hS,hcard,fun h => ((pair_test hpu hcard).mpr ⟨x,hx,rfl⟩).not_gt ((hsmall hS).mp h)⟩

/-- A prescribed center and any prescribed subset of its four partners occur
cofinally as exactly the low-rank defects, on the same five primes. -/
theorem realize_five_prime_star {P U : Finset ℕ} {p : ℕ} (h5 : P.card=5)
    (hP : ∀ a ∈ P, Nat.Prime a) (hp : p ∈ P) (hU : U ⊆ P.erase p) (B : ℕ) :
    ∃ k > B, k.primeFactors = P ∧ unitaryRankDefects k 2 = U.image (fun x => ({p,x}:Finset ℕ)) ∧
      unitaryHalfWeight k = 6-2*(U.card:ℤ) := by
  have hsub := hU.trans (erase_subset _ _)
  have hpu : p ∉ U := fun h => notMem_erase _ _ (hU h)
  let w (a : ℕ) : ℝ := price p U a
  have htotal : ∑ j ∈ P, price p U j = 47+2*U.card := by
    rw [price_sum,h5,inter_eq_right.mpr hsub,if_pos hp]
    omega
  have hstrict (S : Finset ℕ) (hS : S ⊆ P) : ∑ j ∈ S, w j ≠ ∑ j ∈ P \ S, w j := by
    intro h
    have hn : ∑ j ∈ S, price p U j = ∑ j ∈ P \ S, price p U j := by exact_mod_cast h
    have hadd := sum_sdiff hS (f := price p U)
    rw [htotal] at hadd
    omega
  obtain ⟨k,hk,hs,hC⟩ := unitary_chamber_cofinal ⟨_,hp⟩ hP w (fun _ _ => Nat.cast_nonneg _)
    hstrict B
  have hd := five_defect_star hp hU h5 hs hC
  refine ⟨k,hk,hs,hd,?_⟩
  have hinj : Set.InjOn (fun x : ℕ => ({p,x}:Finset ℕ)) U := by
    intro a ha b hb he
    have hmem : a ∈ ({p,b}:Finset ℕ) := he ▸ (by simp : a ∈ ({p,a}:Finset ℕ))
    exact ((mem_insert.mp hmem).resolve_left (fun hh => hpu (hh ▸ ha))) |> mem_singleton.mp
  have hsum : ∑ S ∈ unitaryRankDefects k 2, (-1:ℤ)^S.card = U.card := by
    rw [hd,sum_image hinj]
    calc _ = ∑ _x ∈ U, (1:ℤ) := sum_congr rfl fun x hx => by
           have hpx : p ≠ x := fun he => hpu (he ▸ hx)
           simp [hpx]
         _ = _ := by simp
  have H := unitaryHalfWeight_rank_formula k
  dsimp only at H
  rw [hs,h5] at H
  norm_num [hsum,Nat.choose] at H
  exact H

/-- On every five-prime support the cofinal range of the signed midpoint
is precisely {-2,0,2,4,6}. -/
theorem cofinal_range_of_five_prime_midpoint {P : Finset ℕ} (h5 : P.card=5)
    (hP : ∀ a ∈ P, Nat.Prime a) (v : ℤ) :
    (∀ B : ℕ, ∃ k > B, k.primeFactors=P ∧ unitaryHalfWeight k=v) ↔
      ∃ h : Fin 5, v=6-2*(h.val:ℤ) := by
  constructor
  · intro H
    obtain ⟨k,hk,hs,hv⟩ := H 1
    by_cases hz : unitaryHalfWeight k=0
    · exact ⟨⟨3,by decide⟩,by omega⟩
    have hbalance := unitary_half_weight_support hk hz (by rw [hs,h5]; decide)
    let u : {k : ℕ // k.primeFactors.card=5 ∧ oddSmoothSupport k} := ⟨k,by rw [hs,h5],hbalance⟩
    have H₁ := balanced_five_unitary_weight u
    have H₂ := (negative_balanced_five_iff_full_star u).2.2
    change unitaryHalfWeight k = 6-2*((heavyUnitaryPairs k).card:ℤ) at H₁
    change -2 ≤ unitaryHalfWeight k at H₂
    exact ⟨⟨(heavyUnitaryPairs k).card,by omega⟩,hv ▸ H₁⟩
  · rintro ⟨h,rfl⟩ B
    obtain ⟨p,hp⟩ := card_pos.mp (by omega : 0 < P.card)
    obtain ⟨U,hU,hcard⟩ := exists_subset_card_eq (s:=P.erase p) (n:=h.val) (by
      rw [card_erase_of_mem hp,h5]; have := h.isLt; omega)
    obtain ⟨k,hk,hs,_,hw⟩ := realize_five_prime_star h5 hP hp hU B
    exact ⟨k,hk,hs,by rwa [hcard] at hw⟩


end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
