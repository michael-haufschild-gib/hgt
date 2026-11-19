import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddSmoothCompositesAtThePrimeMidpoint

/-!
# Rank defects at the unitary midpoint

Gatea and Huang's alternating binomial row may be truncated by cardinality
instead of divisor size. For odd support its middle partial sum is a signed
central binomial coefficient. Every disagreement between these two cuts
exchanges a subset with its complement and hence changes the price by twice
its sign. This gives an exact expansion of the actual composite midpoint.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

/-- Low-rank subsets whose unitary divisor lies above the square root. -/
def unitaryRankDefects (k r : ℕ) : Finset (Finset ℕ) :=
  (k.primeFactors.powerset.filter fun S => S.card ≤ r).filter fun S => S ∉ smallUnitarySubsets k

private theorem strict_complement {k : ℕ} (hk : 1 < k) {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    primePowerSubset k S ≠ primePowerSubset k (k.primeFactors \ S) := by
  have hc : (primePowerSubset k S).Coprime (primePowerSubset k (k.primeFactors \ S)) := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hs hp))
      (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)).mpr
        (fun he => (mem_sdiff.mp hq).2 (he ▸ hp)))
  have hm : primePowerSubset k S * primePowerSubset k (k.primeFactors \ S) = k := by
    rw [primePowerSubset, primePowerSubset, mul_comm, prod_sdiff hs]
    exact (Nat.prod_primeFactors_pow_factorization (by omega : k ≠ 0)).symm
  intro he
  rw [← he] at hc hm
  change (primePowerSubset k S).gcd (primePowerSubset k S) = 1 at hc
  rw [Nat.gcd_self] at hc
  rw [hc, one_mul] at hm
  omega

private theorem complement_membership {k : ℕ} (hk : 1 < k) {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    k.primeFactors \ S ∈ smallUnitarySubsets k ↔ S ∉ smallUnitarySubsets k := by
  simp only [smallUnitarySubsets, mem_filter, mem_powerset, sdiff_subset, hs, true_and,
    sdiff_sdiff_eq_self hs, not_le]
  exact ⟨fun h => h.lt_of_ne (strict_complement hk hs).symm, LT.lt.le⟩

private theorem odd_complement_sign {k r : ℕ} (hr : k.primeFactors.card = 2*r+1)
    {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    (-1 : ℤ)^(k.primeFactors \ S).card = -((-1 : ℤ)^S.card) := by
  have hc : (k.primeFactors \ S).card + S.card = 2*r+1 := by
    rw [card_sdiff_of_subset hs]; have := card_le_card hs; omega
  have hp : (-1 : ℤ)^(k.primeFactors \ S).card * (-1 : ℤ)^S.card = -1 := by
    rw [← pow_add, hc, pow_succ, (even_two_mul r).neg_one_pow, one_mul]
  have hsq : (-1 : ℤ)^S.card * (-1 : ℤ)^S.card = 1 := by rw [← mul_pow]; norm_num
  apply mul_right_cancel₀ (pow_ne_zero S.card (by norm_num : (-1 : ℤ) ≠ 0))
  rw [hp, neg_mul, hsq]

private theorem odd_defect_formula {k r : ℕ} (hk : 1 < k) (hr : k.primeFactors.card = 2*r+1) :
    unitaryHalfWeight k = (-1 : ℤ)^r * (2*r).choose r -
      2 * ∑ S ∈ unitaryRankDefects k r, (-1 : ℤ)^S.card := by
  let P := k.primeFactors
  let low := P.powerset.filter fun S => S.card ≤ r
  let small := smallUnitarySubsets k
  let sign (S : Finset ℕ) := (-1 : ℤ)^S.card
  have common : low.filter (· ∈ small) = small.filter (fun S => S.card ≤ r) := by
    ext S
    simp only [low, mem_filter, mem_powerset]
    have hsub : S ∈ small → S ⊆ P := fun h => mem_powerset.mp (mem_filter.mp h).1
    tauto
  have flip : ∑ S ∈ small.filter (fun S => ¬ S.card ≤ r), sign S =
      -∑ S ∈ unitaryRankDefects k r, sign S := by
    rw [← sum_neg_distrib]
    apply sum_nbij' (fun S => P \ S) (fun S => P \ S)
    · intro S hS
      obtain ⟨hsm, hcard⟩ := mem_filter.mp hS
      have hs : S ⊆ P := mem_powerset.mp (mem_filter.mp hsm).1
      have hlow : (P \ S).card ≤ r := by
        rw [card_sdiff_of_subset hs]; change k.primeFactors.card - S.card ≤ r; omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, hlow⟩,
        fun hc => (complement_membership hk hs).mp hc hsm⟩
    · intro S hS
      obtain ⟨hlow, hnot⟩ := mem_filter.mp hS
      obtain ⟨hpow, hcard⟩ := mem_filter.mp hlow
      have hs : S ⊆ P := mem_powerset.mp hpow
      refine mem_filter.mpr ⟨(complement_membership hk hs).mpr hnot, ?_⟩
      rw [card_sdiff_of_subset hs]; change ¬k.primeFactors.card-S.card ≤ r; omega
    · intro S hS
      exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp (mem_filter.mp hS).1).1)
    · intro S hS
      exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp (mem_filter.mp hS).1).1)
    · intro S hS
      have hs : S ⊆ P := mem_powerset.mp (mem_filter.mp (mem_filter.mp hS).1).1
      simp only [sign, odd_complement_sign hr hs, neg_neg]
  have hlow := sum_filter_add_sum_filter_not low (· ∈ small) sign
  have hsmall := sum_filter_add_sum_filter_not small (fun S => S.card ≤ r) sign
  rw [common] at hlow
  rw [flip] at hsmall
  change _ + (∑ S ∈ unitaryRankDefects k r, sign S) = _ at hlow
  have hbin : ∑ S ∈ low, sign S = (-1 : ℤ)^r * (2*r).choose r := by
    rw [_root_.RHTower.Sieve.sum_powerset_filter_card_le]
    change (∑ j ∈ range (r+1), k.primeFactors.card.choose j • (-1 : ℤ)^j) = _
    simpa only [hr, nsmul_eq_mul, mul_comm] using
      (_root_.RHTower.Sieve.alternating_choose_partialSum (2*r) r)
  rw [hbin] at hlow
  change (∑ S ∈ small, sign S) = _ - 2 * ∑ S ∈ unitaryRankDefects k r, sign S
  linarith only [hlow, hsmall]

/-- Rank formula for every integer, including the empty support at zero and one. -/
theorem unitaryHalfWeight_rank_formula (k : ℕ) :
    let m := k.primeFactors.card
    let r := m/2
    unitaryHalfWeight k = if m = 0 then 1 else if Even m then 0 else
      (-1 : ℤ)^r * (2*r).choose r - 2 * ∑ S ∈ unitaryRankDefects k r, (-1 : ℤ)^S.card := by
  dsimp only
  by_cases hz : k.primeFactors.card = 0
  · rw [if_pos hz]
    simp [unitaryHalfWeight, smallUnitarySubsets, card_eq_zero.mp hz, primePowerSubset]
  rw [if_neg hz]
  have hk : 1 < k := Nat.nonempty_primeFactors.mp (card_pos.mp (Nat.pos_of_ne_zero hz))
  split_ifs with he
  · exact unitary_half_weight_even hk he
  · obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp he
    rw [show k.primeFactors.card/2 = r by omega]
    exact odd_defect_formula hk hr

/-- Weight used by the rank expansion of the actual odd composite price. -/
def rankCompositeWeight (k : ℕ) : ℤ :=
  let r := k.primeFactors.card/2
  (-1 : ℤ)^r * (2*r).choose r - 2 * ∑ S ∈ unitaryRankDefects k r, (-1 : ℤ)^S.card

/-- In the sharp arithmetic midpoint, the only correction to the central binomial
price is the signed mass of low-rank unitary divisors above the square root. -/
theorem oddSmoothCompositePrice_rank_expansion (n : ℕ) :
    oddSmoothCompositePrice n = unitarySignedIntervals (fun k =>
      if n.Coprime k ∧ oddSmoothSupport k then (rankCompositeWeight k : ℝ)*Real.log k else 0) n := by
  classical
  unfold oddSmoothCompositePrice
  congr 1
  funext k
  split_ifs with h
  · change (unitaryHalfWeight k : ℝ)*Real.log k = _
    have hr := unitaryHalfWeight_rank_formula k
    dsimp only at hr
    rw [if_neg (by have := h.2.2.1; omega), if_neg (Nat.not_even_iff_odd.mpr h.2.1)] at hr
    rw [hr]
    rfl
  · rfl

#print axioms oddSmoothCompositePrice_rank_expansion
#print axioms unitaryHalfWeight_rank_formula

end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
