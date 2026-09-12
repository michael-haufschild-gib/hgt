import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor

/-!
# Route E incidence-switch parity rigidity

For finite supports of distinct primes, the Möbius signs agree exactly when the symmetric
difference has even cardinality and are opposite exactly when it has odd cardinality.  This gives
the exact move-classification needed by prime-incidence pairing proposals.

A standard two-by-two incidence switch replaces one prime by another in each of two receiver
columns.  It preserves both column cardinalities, hence both Möbius values.  Such margin-preserving
switches can redistribute receivers inside a fixed parity class, but cannot create any
sign-reversing edge.  A surviving pairing mechanism must change receiver prime-count parity; after
the one-toggle Hall obstruction, the first still-live class is the full three-toggle graph.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius symmDiff

noncomputable section

namespace RHTower

/-- Symmetric difference removes two copies of the intersection from the sum of cardinalities. -/
theorem card_add_eq_card_symmDiff_add_twice_inter (S T : Finset ℕ) :
    S.card + T.card = (S ∆ T).card + 2 * (S ∩ T).card := by
  have hdisj : Disjoint (S \ T) (T \ S) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  rw [Finset.symmDiff_def, card_union_of_disjoint hdisj]
  have hS := card_sdiff_add_card_inter S T
  have hT := card_sdiff_add_card_inter T S
  rw [inter_comm T S] at hT
  omega

/-- The symmetric-difference cardinality is even exactly when the sum of endpoint cardinalities
is even. -/
theorem even_card_symmDiff_iff_even_card_add (S T : Finset ℕ) :
    Even (S ∆ T).card ↔ Even (S.card + T.card) := by
  have hcard := card_add_eq_card_symmDiff_add_twice_inter S T
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + (S ∩ T).card, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - (S ∩ T).card, by omega⟩

/-- **Exact same-sign criterion.** Two squarefree prime products have the same Möbius value exactly
when their prime supports differ in an even number of coordinates. -/
theorem moebius_primeProducts_eq_iff_even_symmDiff
    {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    (μ (∏ p ∈ S, p) : ℤ) = μ (∏ p ∈ T, p) ↔ Even (S ∆ T).card := by
  rw [GibbsGas.moebius_prod_primes hS, GibbsGas.moebius_prod_primes hT]
  have hparity : Even (S ∆ T).card ↔ (Even S.card ↔ Even T.card) :=
    (even_card_symmDiff_iff_even_card_add S T).trans Nat.even_add
  rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite]
  by_cases hSe : Even S.card <;> by_cases hTe : Even T.card <;>
    simp [hSe, hTe] at hparity ⊢
  all_goals assumption

/-- **Exact opposite-sign criterion.** Two squarefree prime products have opposite Möbius values
exactly when their prime supports differ in an odd number of coordinates. -/
theorem moebius_primeProducts_eq_neg_iff_odd_symmDiff
    {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    (μ (∏ p ∈ T, p) : ℤ) = -(μ (∏ p ∈ S, p) : ℤ) ↔ Odd (S ∆ T).card := by
  rw [GibbsGas.moebius_prod_primes hT, GibbsGas.moebius_prod_primes hS]
  have hparity : Even (S ∆ T).card ↔ (Even S.card ↔ Even T.card) :=
    (even_card_symmDiff_iff_even_card_add S T).trans Nat.even_add
  have hodd : Odd (S ∆ T).card ↔ ¬(Even S.card ↔ Even T.card) := by
    rw [← Nat.not_even_iff_odd]
    exact not_congr hparity
  rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite]
  by_cases hSe : Even S.card <;> by_cases hTe : Even T.card <;>
    simp [hSe, hTe] at hodd ⊢
  all_goals assumption

/-- Replace one occupied prime coordinate by one unoccupied prime coordinate. -/
def routeEPrimeSupportSwap (S : Finset ℕ) (out incoming : ℕ) : Finset ℕ :=
  insert incoming (S.erase out)

/-- A valid one-out/one-in prime-support swap preserves support cardinality. -/
theorem card_routeEPrimeSupportSwap
    {S : Finset ℕ} {out incoming : ℕ}
    (hout : out ∈ S) (hincoming : incoming ∉ S) :
    (routeEPrimeSupportSwap S out incoming).card = S.card := by
  have hnot : incoming ∉ S.erase out := fun h => hincoming (mem_of_mem_erase h)
  rw [routeEPrimeSupportSwap, card_insert_of_notMem hnot]
  exact card_erase_add_one hout

/-- Replacing a support coordinate by a prime preserves the prime-support property. -/
theorem routeEPrimeSupportSwap_primes
    {S : Finset ℕ} {out incoming : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hincoming : incoming.Prime) :
    ∀ p ∈ routeEPrimeSupportSwap S out incoming, p.Prime := by
  intro p hp
  simp only [routeEPrimeSupportSwap, mem_insert, mem_erase] at hp
  rcases hp with rfl | ⟨_, hpS⟩
  · exact hincoming
  · exact hS p hpS

/-- One-out/one-in support replacement preserves the Möbius value. -/
theorem moebius_routeEPrimeSupportSwap_eq
    {S : Finset ℕ} {out incoming : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    (hout : out ∈ S) (hincoming : incoming ∉ S) (hprime : incoming.Prime) :
    (μ (∏ p ∈ routeEPrimeSupportSwap S out incoming, p) : ℤ) =
      μ (∏ p ∈ S, p) := by
  rw [GibbsGas.moebius_prod_primes
      (routeEPrimeSupportSwap_primes hS hprime),
    GibbsGas.moebius_prod_primes hS,
    card_routeEPrimeSupportSwap hout hincoming]

/-- **Two-by-two switch rigidity.** Exchanging occupied prime coordinates between two columns
preserves both Möbius values. -/
theorem routeE_twoByTwo_incidence_switch_preserves_moebius
    {S T : Finset ℕ} {p q : ℕ}
    (hS : ∀ r ∈ S, r.Prime) (hT : ∀ r ∈ T, r.Prime)
    (hpS : p ∈ S) (hqS : q ∉ S) (hqT : q ∈ T) (hpT : p ∉ T) :
    (μ (∏ r ∈ routeEPrimeSupportSwap S p q, r) : ℤ) = μ (∏ r ∈ S, r) ∧
      (μ (∏ r ∈ routeEPrimeSupportSwap T q p, r) : ℤ) = μ (∏ r ∈ T, r) := by
  exact ⟨moebius_routeEPrimeSupportSwap_eq hS hpS hqS (hT q hqT),
    moebius_routeEPrimeSupportSwap_eq hT hqT hpT (hS p hpS)⟩

/-- Therefore neither receiver endpoint of a valid two-by-two incidence switch reverses Möbius
sign. -/
theorem routeE_twoByTwo_incidence_switch_cannot_reverse_moebius
    {S T : Finset ℕ} {p q : ℕ}
    (hS : ∀ r ∈ S, r.Prime) (hT : ∀ r ∈ T, r.Prime)
    (hpS : p ∈ S) (hqS : q ∉ S) (hqT : q ∈ T) (hpT : p ∉ T) :
    ¬(μ (∏ r ∈ routeEPrimeSupportSwap S p q, r) : ℤ) = -(μ (∏ r ∈ S, r) : ℤ) ∧
      ¬(μ (∏ r ∈ routeEPrimeSupportSwap T q p, r) : ℤ) = -(μ (∏ r ∈ T, r) : ℤ) := by
  have hpres := routeE_twoByTwo_incidence_switch_preserves_moebius
    hS hT hpS hqS hqT hpT
  constructor
  · intro hneg
    rw [hpres.1] at hneg
    have hne : (μ (∏ r ∈ S, r) : ℤ) ≠ 0 := by
      rw [GibbsGas.moebius_prod_primes hS]
      exact pow_ne_zero _ (by norm_num)
    omega
  · intro hneg
    rw [hpres.2] at hneg
    have hne : (μ (∏ r ∈ T, r) : ℤ) ≠ 0 := by
      rw [GibbsGas.moebius_prod_primes hT]
      exact pow_ne_zero _ (by norm_num)
    omega

end RHTower
