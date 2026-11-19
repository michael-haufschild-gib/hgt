import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OneExchangeAtTheUnitarySquareRoot
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WalshConstraintsAtTheUnitaryMidpoint

/-!
# The Walsh spectrum of a one-exchange midpoint

When the small-divisor cut differs from a coordinate cut at just one pair
of complementary vertices, every nonlinear odd Walsh coefficient has
magnitude four. The distinguished linear coefficient absorbs the rest.
The critical virial energy consequently becomes a binomial rank sum.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem complement_value {P T : Finset ℕ} (ht : T ⊆ P) (A : Finset ℕ) :
    blockCharacter T (P \ A) = (-1:ℤ)^T.card*blockCharacter T A := by
  rw [←prod_const,blockCharacter,blockCharacter,←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  by_cases h : p ∈ A <;> simp [h,ht hp]

private theorem face_character_sum {P T : Finset ℕ} {p : ℕ} (hp : p ∈ P) (ht : T ⊆ P) (ho : Odd T.card) :
    ∑ A ∈ (P.erase p).powerset, blockCharacter T A =
      if T={p} then (2:ℤ)^(P.erase p).card else 0 := by
  simp_rw [blockCharacter_comm T]
  simp only [blockCharacter,←prod_one_add]
  by_cases he : T={p}
  · subst T
    rw [if_pos rfl,←prod_const]
    exact prod_congr rfl fun q hq => by simp [(mem_erase.mp hq).1]
  · rw [if_neg he]
    have hn : T.Nonempty := card_pos.mp (by obtain ⟨j,hj⟩ := ho; omega)
    obtain ⟨q,hq,hqp⟩ : ∃ q ∈ T, q ≠ p := by
      by_contra! h
      have hsub : T ⊆ {p} := fun q hq => mem_singleton.mpr (h q hq)
      obtain ⟨q,hq⟩ := hn
      have hpT : p ∈ T := (h q hq) ▸ hq
      exact he (Subset.antisymm hsub (singleton_subset_iff.mpr hpT))
    exact prod_eq_zero (mem_erase.mpr ⟨hqp,ht hq⟩) (by simp [hq])

/-- Exact odd spectrum, including the exceptional linear direction of
amplitude two to the block count minus four. -/
theorem unitaryWalshContrast_one_exchange {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hl : (p^k.factorization p)^2 < k) (hu : k < (2*p^k.factorization p)^2)
    {T : Finset ℕ} (ht : T ⊆ k.primeFactors) (ho : Odd T.card) :
    unitaryWalshContrast k T =
      (if T={p} then (2:ℤ)^k.primeFactors.card else 0) + (if p ∈ T then -4 else 4) := by
  let P := k.primeFactors
  let B := P.erase p
  have replace := unitary_one_exchange_price hp hl hu (blockCharacter T)
  have comp := complement_value ht ({p} : Finset ℕ)
  rw [sdiff_singleton_eq_erase,ho.neg_one_pow,neg_one_mul] at comp
  have ch : blockCharacter T {p} = if p ∈ T then -1 else 1 := by
    simp [blockCharacter,prod_ite_eq']
  change (∑ A ∈ smallUnitarySubsets k, blockCharacter T A)+blockCharacter T (P.erase p) =
    blockCharacter T {p} + ∑ A ∈ (P.erase p).powerset, blockCharacter T A at replace
  rw [comp,ch,face_character_sum hp ht ho] at replace
  have ratio : (2:ℤ)^P.card=2*(2:ℤ)^B.card := by
    rw [←card_erase_add_one hp,pow_succ,mul_comm]
  have im : unitaryWalshContrast k T = 2*∑ A ∈ smallUnitarySubsets k, blockCharacter T A := by
    rw [unitaryWalshContrast,mul_sum]
    exact sum_congr rfl fun A _ => by rw [complement_value ht,ho.neg_one_pow]; ring
  rw [im]
  change _ = (if T={p} then (2:ℤ)^P.card else 0) + _
  change _ + _ = _ + (if T={p} then (2:ℤ)^B.card else 0) at replace
  rw [ratio]
  split_ifs at replace ⊢ <;> omega

/-- In a near-dominant cut the virial form is a universal binomial sum
plus the correction of the distinguished coordinate. -/
theorem one_exchange_virial_spectrum {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hl : (p^k.factorization p)^2 < k) (hu : k < (2*p^k.factorization p)^2) (γ : ℝ) :
    let r := k.primeFactors.card
    unitaryVirialEnergy γ k =
      (((2:ℝ)^r-4)^2-16)*blockVirialSymbol γ 2 +
        16*∑ j ∈ range (r+1), if Odd j then (r.choose j:ℝ)*blockVirialSymbol γ (2*j) else 0 := by
  intro r
  let P := k.primeFactors
  let E (T : Finset ℕ) := blockVirialSymbol γ (2*T.card)*(unitaryWalshContrast k T:ℝ)^2
  let b (j : ℕ) : ℝ := if Odd j then blockVirialSymbol γ (2*j) else 0
  let d := (((2:ℝ)^r-4)^2-16)*blockVirialSymbol γ 2
  have point (T : Finset ℕ) (hT : T ∈ P.powerset) :
      E T = (if T={p} then d else 0) + 16*b T.card := by
    by_cases he : T={p}
    · subst T
      have ho : Odd ({p}:Finset ℕ).card := by simp
      simp only [E,unitaryWalshContrast_one_exchange hp hl hu (mem_powerset.mp hT) ho,
        if_true,mem_singleton_self,card_singleton,Nat.cast_one,mul_one,Int.cast_add,Int.cast_pow,
        Int.cast_ofNat,Int.cast_neg,Int.cast_one,b,show Odd 1 from ⟨0,rfl⟩,d,r]
      ring
    · rw [if_neg he,zero_add]
      rcases Nat.even_or_odd T.card with h|h
      · simp [E,b,h.not_odd,unitaryWalshContrast_even (mem_powerset.mp hT) h]
      · rw [show E T = _ from rfl,unitaryWalshContrast_one_exchange hp hl hu (mem_powerset.mp hT) h,
          if_neg he,zero_add]
        by_cases hpt : p ∈ T <;> simp [hpt,b,h] <;> ring
  change (∑ T ∈ P.powerset, E T) = d + _
  rw [sum_congr rfl point,sum_add_distrib,sum_ite_eq',if_pos (mem_powerset.mpr (singleton_subset_iff.mpr hp)),
    ←mul_sum,sum_powerset_apply_card]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  by_cases h : Odd j <;> simp [b,h,nsmul_eq_mul,P,r]

#print axioms unitaryWalshContrast_one_exchange
#print axioms one_exchange_virial_spectrum
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
