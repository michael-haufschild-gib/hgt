import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRootCollisionWeightPieces
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CollisionWeightSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Summing the two collision bounds over eligible primes and
factor degrees gives the local separation estimate. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open FiniteWeight

private theorem two_pow_card_primeFactors_le_add_one (n : ℕ) : 2 ^ n.primeFactors.card ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc
      2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
      _ ≤ _ := Nat.le_succ n

private theorem primeFactors_card_le (g δ : ℕ) (hg : 1 ≤ g) :
    (((g ^ δ - 1).primeFactors.card : ℕ) : ℝ) ≤ 3 / 2 * (δ : ℝ) * Real.log g := by
  have hp := Nat.one_le_pow δ g (by omega)
  have h := (two_pow_card_primeFactors_le_add_one (g ^ δ - 1)).trans_eq (Nat.sub_add_cancel hp)
  have hr : (2 : ℝ) ^ (g ^ δ - 1).primeFactors.card ≤ (g : ℝ) ^ δ := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hr
  rw [Real.log_pow, Real.log_pow] at hlog
  have h2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hh := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (g ^ δ - 1).primeFactors.card)
  linarith only [hh, hlog]

variable (g N : ℕ) [Fact g.Prime]

private theorem weight_sameFactorEvents_le :
    weight (polynomialWeight g N) (sameFactorEvents g N) ≤
      ∑ δ ∈ Finset.Icc 2 N, (3 / 2 * δ * Real.log g) *
        ((g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹) := by
  have hg : 1 ≤ g := (Fact.out : g.Prime).one_lt.le
  unfold sameFactorEvents
  refine (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  refine Finset.sum_le_sum fun δ hδ => (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  have hδ2 := (Finset.mem_Icc.mp hδ).1
  let C := (g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹
  let S := smallPrimaryPrimes g δ (g ^ δ - 1).primeFactors
  have hC : 0 ≤ C := mul_nonneg (by positivity) (inv_nonneg.mpr (residue_denom_pos g (by omega)).le)
  have hS : (S.card : ℝ) ≤ 3 / 2 * (δ : ℝ) * Real.log g := by
    refine (le_trans ?_ (primeFactors_card_le g δ hg))
    exact_mod_cast Finset.card_filter_le _ _
  calc
    _ ≤ ∑ _l ∈ S, C := by
      refine Finset.sum_le_sum fun l hl => ?_
      have ⟨hp, hsmall⟩ := Finset.mem_filter.mp hl
      exact weight_same_factor_le g N δ l (Nat.prime_of_mem_primeFactors hp) hδ2 hsmall
    _ = (S.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hS hC

private theorem weight_crossFactorEvents_le :
    weight (polynomialWeight g N) (crossFactorEvents g N) ≤
      ∑ δ ∈ Icc 1 N, (3 * (δ : ℝ) ^ 2 * Real.log g) *
        ((g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹) := by
  have hg : 1 ≤ g := (Fact.out : g.Prime).one_lt.le
  have hlog : 0 ≤ Real.log g := Real.log_nonneg (by exact_mod_cast hg)
  unfold crossFactorEvents
  refine (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  refine Finset.sum_le_sum fun δ hδ => (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  have hδ1 := (Finset.mem_Icc.mp hδ).1
  let C := (g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹
  have hC : 0 ≤ C := mul_nonneg (by positivity) (inv_nonneg.mpr (residue_denom_pos g hδ1).le)
  calc
    _ ≤ ∑ _δ' ∈ Icc 1 δ, (3 * (δ : ℝ) * Real.log g) * C := by
      refine Finset.sum_le_sum fun δ' hδ' => (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
      let S := smallPrimaryPrimes g δ ((g ^ δ - 1).primeFactors ∪ (g ^ δ' - 1).primeFactors)
      have hS : (S.card : ℝ) ≤ 3 * (δ : ℝ) * Real.log g := by
        have hsub : (S.card : ℝ) ≤ ((g ^ δ - 1).primeFactors.card : ℝ) +
            ((g ^ δ' - 1).primeFactors.card : ℝ) := by
          exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_union_le _ _)
        have hle : (δ' : ℝ) ≤ δ := by exact_mod_cast (Finset.mem_Icc.mp hδ').2
        have hlogle := mul_le_mul_of_nonneg_right hle hlog
        linarith only [hsub, primeFactors_card_le g δ hg, primeFactors_card_le g δ' hg, hlogle]
      calc
        _ ≤ ∑ _l ∈ S, C := by
          refine Finset.sum_le_sum fun l hl => ?_
          have ⟨hp, hsmall⟩ := Finset.mem_filter.mp hl
          have hlp : l.Prime := (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
          exact weight_cross_factor_le g N δ δ' l hlp hδ1 (Finset.mem_Icc.mp hδ').1 hsmall
        _ = (S.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hS hC
    _ = (3 * (δ : ℝ) ^ 2 * Real.log g) * C := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      ring

open Classical in
theorem local_root_collision_weight_le (hg : 2 ^ 12 ≤ g) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ separatesPrimeToParts g N c),
      squarefreeWeight g (monicOf c) ≤ 23 * Real.log g / Real.sqrt g := by
  change (∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ separatesPrimeToParts g N c),
    polynomialWeight g N c) ≤ _
  rw [← weight_eq_filter' (polynomialWeight g N) (squarefreeCoefficients g N)
    (fun c => ¬ separatesPrimeToParts g N c)]
  refine (weight_mono _ (polynomialWeight_nonneg g N) (root_collision_events_cover g N)).trans ?_
  exact (weight_union_le _ (polynomialWeight_nonneg g N) _ _).trans
    ((add_le_add (weight_sameFactorEvents_le g N) (weight_crossFactorEvents_le g N)).trans
      (collision_series_le g N hg))

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.local_root_collision_weight_le
