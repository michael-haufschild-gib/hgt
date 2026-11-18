import GaloisForLFunctions.ExceptionalLayerTheory.BinaryCarryTentAndAdjacentQuotientIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.DivisionTreesOfDyadicSmoothCounts
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeEditObstructionForBinomialCarries

/-!
# Complete resolution of binary-carry cancellation for distinct primes in central binomials

We synthesize the complete mathematical resolution of whether binary carries,
adjacent quotient-interval pairings, growing quotient bands, and smooth-integer
division trees can yield a cancellation law for distinct ordinary prime divisors
of the central binomial coefficient with positivity and spectral methods excluded:

1. **Adjacent quotient intervals and the tent profile**:
   `discreteQuotientMean binaryCarryProfile m X = X / 2 - binaryCarryTent m X / 2`
   is strictly positive (`≥ Q / (2Q + 1) * X ≥ X / 3`) across **both** `⌊X / m⌋ = 2Q`
   and `⌊X / m⌋ = 2Q + 1` (`Q ≥ 1`), so adjacent quotient intervals create zero sign
   opposition; von Mangoldt weights cancel unconditionally to `O(X^{3/2})`, whereas
   unweighted distinct primes retain exact exponent `1 + zeroReSup`.

2. **Smooth-integer division trees and top-octave aliasing**:
   for all `n` and `y ≥ 2`, `2 Ψ(n, y) - Ψ(2n, y) = ∑_{j ≤ 2n, P⁺(j) ≤ y} (-1)^j`
   splits over odd `y`-smooth roots `u` with weight `⌊log₂(2n/u)⌋ - 1` and satisfies
   an exact odd-prime Buchstab recurrence down to `Φ(M, 2) = ⌊log₂ M⌋ - 1`; while the
   raw complement identity uniquely selects primes on `(y, (y+1)²)`, the central-binomial
   carry aliases `2r - 1` and `2r` identically (`= 1_{r ≤ n}`) across `r ∈ (⌊N/2⌋, N]`.

3. **Growing quotient-band trichotomy**:
   moving-cutoff slices `S_{2Q+1}(X)` partition `ordinaryLastClassTotal 2 X`, satisfy
   `|S_{2Q+1}(X)| ≤ C (X / (2Q + 2))^{15/8}` summably over all `Q < X` (beating the
   unsigned `X² / (64 (d+1)² log X)` benchmark on wide bands), while `O_ε(X^{3/2 + ε})`
   on even one slice `d ≥ 1` is equivalent to `RiemannHypothesis`; outer-cutoff paired
   bands satisfy `|T_out(Q, X)| ≤ C X (X / (2Q))^{7/8}`, yet near `√X` Bertrand's
   postulate forces `(1 - ε) T_out^triv(Q, X) ≤ |T_out(Q, X)|`.

4. **Sub-square-root prime-edit selectivity barrier and `O(X^{15/8})` corollaries**:
   unconditionally on `β ∈ (1/2, 27001 / 48000)`, there exists a two-sided prime edit
   with sub-square-root count remainder `c₀ < 1/2` (so its dyadic norm-count first total
   is `O(X^{c₀ + 1}) = o(X^{3/2})`) whose distinct-generator carry first total still
   exceeds `K X^{b + 1}` infinitely often for every `b ∈ [1/2, β)`; for actual primes,
   all distinct-prime binomial carry and smooth dyadic first totals are unconditionally
   `O(X^{15/8})` exact (`O(X^{1 + β})` for every `β > 20999 / 24000`).
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Master theorem 1: Exact tent law, positivity across adjacent quotient intervals,
unconditional `O(X^{3/2})` von Mangoldt carry cancellation, and `1 + zeroReSup`
exponent lock for distinct ordinary primes. -/
theorem complete_adjacent_quotient_and_tent_resolution :
    (∀ {m : ℕ}, 0 < m → ∀ X : ℕ,
      discreteQuotientMean binaryCarryProfile m X =
        (X : ℝ) / 2 - binaryCarryTent m X / 2) ∧
    (∀ {Q m X : ℕ}, 1 ≤ Q → 0 < m → (X / m = 2 * Q ∨ X / m = 2 * Q + 1) →
      (X : ℝ) / 3 ≤ discreteQuotientMean binaryCarryProfile m X ∧
        discreteQuotientMean binaryCarryProfile m X ≤ (X : ℝ) / 2) ∧
    (∀ X : ℕ,
      |∑ k ∈ range X, ∑ m ∈ Icc 1 k, (vonMangoldt m - 1) * binaryCarryProfile (k / m)| ≤
        (75 + 2 * |Real.eulerMascheroniConstant|) * (X : ℝ) ^ (3 / 2 : ℝ)) ∧
    (∀ (j : ℕ) {b C : ℝ}, 1 / 2 ≤ b → b < 1 →
      (∀ X : ℕ, 1 ≤ X → |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (b + 1)) →
      (∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0) ∧ _root_.RHTower.zeroReSup ≤ b) :=
  ⟨fun hm X => discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent hm X,
   fun hQ hm hband => ⟨(discreteQuotientMean_binaryCarryProfile_adjacent_intervals hQ hm hband).2.1,
     (discreteQuotientMean_binaryCarryProfile_adjacent_intervals hQ hm hband).2.2⟩,
   mangoldt_binaryCarry_first_total_le_three_halves,
   fun j {_} {_} hb hb1 h =>
     binomialDistinctPrimeTotal_bound_excludes_zero_and_bounds_zeroReSup j hb hb1 h⟩

/-- Master theorem 2: Complete smooth-integer division-tree laws, Buchstab prime tree,
unique prime selection by raw complements, and top-octave central-binomial parity aliasing. -/
theorem complete_smooth_division_tree_resolution :
    (∀ (n : ℕ) {y : ℕ}, 2 ≤ y →
      2 * (smoothIntegerCount n y : ℝ) - (smoothIntegerCount (2 * n) y : ℝ) =
        alternatingSmoothSum (2 * n) y ∧
      2 * (smoothIntegerCount n y : ℝ) - (smoothIntegerCount (2 * n) y : ℝ) =
        (smoothIntegerCount (n / 2) y : ℝ) -
          ((oddSmoothIntegerCount (2 * n) y : ℝ) - (oddSmoothIntegerCount n y : ℝ))) ∧
    (∀ (M : ℕ) {z y : ℕ}, 2 ≤ z → z ≤ y →
      alternatingSmoothSum M y =
        alternatingSmoothSum M z +
          ∑ p ∈ (Nat.primesLE y).filter (fun p => z < p), alternatingSmoothSum (M / p) p) ∧
    (∀ {y B : ℕ}, B < (y + 1) ^ 2 → ∀ g : ℕ → ℝ,
      (∀ x ∈ Ioc y B, (smoothIntegerCount x y : ℝ) +
        ∑ m ∈ Ioc y B, g m * ((x / m : ℕ) : ℝ) = x) ↔
        ∀ m ∈ Ioc y B, g m = if m.Prime then 1 else 0) ∧
    (∀ {N r n : ℕ}, N < 2 * r - 1 → r ≤ N → n ≤ N →
      ((2 * n) / (2 * r - 1)) % 2 = ((2 * n) / (2 * r)) % 2 ∧
        ((2 * n) / (2 * r)) % 2 = if r ≤ n then 1 else 0) :=
  ⟨fun n {_} hy => ⟨(two_mul_smoothIntegerCount_sub_eq_alternating n hy).2,
     two_mul_smoothIntegerCount_sub_eq_middle_octave_cancel n hy⟩,
   fun M {_} {_} hz hzy => alternatingSmoothSum_buchstab M hz hzy,
   fun hB g => smooth_complement_uniquely_selects_primes hB g,
   fun hr _ hn => centralBinom_carry_top_octave_aliasing hr hn⟩

/-- Master theorem 3: Growing quotient-band summability, wide-band cancellation gain,
single-slice equivalence with `RiemannHypothesis`, and Bertrand short-interval saturation near `√X`. -/
theorem complete_growing_quotient_band_resolution :
    (∀ X : ℕ, (∑ Q ∈ range X, movingOddQuotientBand Q X) = ordinaryLastClassTotal 2 X) ∧
    (∃ C Csum : ℝ, 0 ≤ C ∧ 0 ≤ Csum ∧
      (∀ d X : ℕ, 1 ≤ d →
        |movingQuotientSlice d X| ≤ C * ((X : ℝ) / ((d : ℝ) + 1)) ^ (15 / 8 : ℝ)) ∧
      (∀ X : ℕ,
        (∑ Q ∈ range X, |movingOddQuotientBand Q X|) ≤ Csum * (X : ℝ) ^ (15 / 8 : ℝ))) ∧
    (∀ {d X : ℕ}, 1 ≤ d → 8 * (d + 1) ≤ X →
      (X : ℝ) ^ 2 / (64 * ((d : ℝ) + 1) ^ 2 * Real.log X) ≤ movingQuotientSliceTrivial d X) ∧
    (∀ {d : ℕ}, 1 ≤ d →
      (RiemannHypothesis ↔ ∀ b : ℝ, 1 / 2 < b → b < 1 → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
        |movingQuotientSlice d X| ≤ C * (X : ℝ) ^ (b + 1))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ Q X : ℕ, 1 ≤ Q →
      |outerQuotientPairBand Q X| ≤ C * (X : ℝ) * ((X : ℝ) / (2 * (Q : ℝ))) ^ (7 / 8 : ℝ)) ∧
    (∀ {ε : ℝ}, 0 < ε → ∀ᶠ X : ℕ in atTop, ∃ Q : ℕ,
      X.sqrt / 5 + 1 ≤ Q ∧ 2 * Q + 2 < X.sqrt ∧
      (X : ℝ) / 4 ≤ outerQuotientPairBand Q X ∧
      (1 - ε) * outerQuotientPairBandTrivial Q X ≤ |outerQuotientPairBand Q X|) :=
  ⟨sum_movingOddQuotientBand_eq_ordinaryLastClassTotal,
   exists_movingOddQuotientBand_fifteen_eighths_exact,
   fun hd hX => movingQuotientSliceTrivial_lower_bound hd hX,
   fun hd => riemannHypothesis_iff_one_movingQuotientSlice hd,
   exists_outerQuotientPairBand_seven_eighths_exact,
   fun hε => (eventually_exists_sqrt_band_near_trivial hε).mono fun _ ⟨Q, h1, h2, _, _, _, h6, h7⟩ =>
     ⟨Q, h1, h2, h6, h7⟩⟩

/-- Master theorem 4: Sub-square-root prime-edit selectivity obstruction (`o(X^{3/2})` dyadic
norm-count first total vs. `Ω(X^{b + 1})` distinct-generator carry blow-up) and unconditional
`O(X^{15/8})` exact bounds for actual primes. -/
theorem complete_prime_edit_barrier_and_unconditional_corollaries :
    (∀ {β : ℝ}, 1 / 2 < β → β < 27001 / 48000 →
      ∃ (e : ℕ → ℤ) (c₀ Cdyad : ℝ),
        IsEdit e ∧ 0 ≤ c₀ ∧ c₀ < 1 / 2 ∧ 0 ≤ Cdyad ∧
        IsIntegerNormFakeAt (editSystem e) c₀ ∧
        (∀ X : ℕ, 1 ≤ X →
          (∑ k ∈ range X,
            |2 * ((editSystem e).countBall (k / 2 : ℕ) : ℝ) -
              ((editSystem e).countBall ((2 * (k / 2) : ℕ)) : ℝ)|) ≤
            Cdyad * (X : ℝ) ^ (c₀ + 1)) ∧
        (∀ (q : ℕ), 2 ≤ q → ∀ (b : ℝ), 1 / 2 ≤ b → b < β → ∀ (K : ℝ),
          ∃ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (b + 1) < |editedLastClassTotal e q X|)) ∧
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ q X : ℕ, 2 ≤ q → 1 ≤ X →
      |ordinaryLastClassTotal q X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |∑ k ∈ range X, (((Nat.centralBinom (k / 2)).primeFactors.card : ℝ) -
        quotientClassMassOf (fun m => (Real.log m)⁻¹) 2 k)| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |smoothDyadicFirstTotal X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ))) :=
  ⟨fun hβ hβ_hi => exists_sub_sqrt_count_edit_with_carry_obstruction hβ hβ_hi,
   exists_binomialDistinctPrime_and_smooth_fifteen_eighths_exact⟩

end GaloisForLFunctions.ExceptionalLayerTheory