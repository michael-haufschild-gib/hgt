import GaloisForLFunctions.RHTower.MobiusCoprimeProductSignExtraction
import GaloisForLFunctions.RHTower.RouteECofactorParityBalance
import GaloisForLFunctions.RHTower.Sieve.BalancedPairs
import GaloisForLFunctions.RHTower.Sieve.CoprimeSignDensity

/-!
# Exact finite coprime squarefree product-sign count

For an arbitrary finite pair set, filter to coprime pairs whose two factors are squarefree.  Möbius
multiplicativity then identifies the product signed imbalance exactly with the bilinear factor-sign
sum.  Both product signs have cardinality at least half the packet size minus half the absolute
imbalance.  Specializing the pair set to the corpus's exact balanced product window gives the
card's finite sign-extraction law with no premise.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Coprime squarefree factor pairs selected from an arbitrary finite pair set. -/
def finiteCoprimeSquarefreeProductPairPacket
    (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.filter fun p =>
    Nat.Coprime p.1 p.2 ∧ Squarefree p.1 ∧ Squarefree p.2

/-- Exact product-sign factorization over the finite coprime squarefree packet. -/
theorem sum_moebius_finiteCoprimeSquarefreeProductPair_eq_sum_mul
    (S : Finset (ℕ × ℕ)) :
    (∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
        (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)) =
      ∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
        (ArithmeticFunction.moebius p.1 : ℝ) *
          (ArithmeticFunction.moebius p.2 : ℝ) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (Finset.mem_filter.mp hp).2.1]
  norm_cast

/-- Both product signs have at least half the packet cardinality minus half its exact bilinear
Möbius imbalance. -/
theorem finiteCoprimeSquarefreeProductPair_bothSignCount_lower
    (S : Finset (ℕ × ℕ)) :
    (((finiteCoprimeSquarefreeProductPairPacket S).card : ℝ) -
          |∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
            (ArithmeticFunction.moebius p.1 : ℝ) *
              (ArithmeticFunction.moebius p.2 : ℝ)|) / 2 ≤
        (((finiteCoprimeSquarefreeProductPairPacket S).filter fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = 1).card : ℝ) ∧
      (((finiteCoprimeSquarefreeProductPairPacket S).card : ℝ) -
          |∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
            (ArithmeticFunction.moebius p.1 : ℝ) *
              (ArithmeticFunction.moebius p.2 : ℝ)|) / 2 ≤
        (((finiteCoprimeSquarefreeProductPairPacket S).filter fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = -1).card : ℝ) := by
  classical
  let T := finiteCoprimeSquarefreeProductPairPacket S
  let sign : ℕ × ℕ → ℝ := fun p =>
    (ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 : ℤ)
  have hsign : ∀ p ∈ T, sign p = 1 ∨ sign p = -1 := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    rcases CofactorParity.moebius_eq_one_or_neg_one hp'.2.1 with ha | ha <;>
      rcases CofactorParity.moebius_eq_one_or_neg_one hp'.2.2 with hb | hb
    all_goals simp [sign, ha, hb]
  have h := finiteProductPair_bothSignMass_after_bad_lower
    T (fun _ => (1 : ℝ)) sign (fun _ => False)
      (by intro p hp; positivity) hsign
  simpa [T, sign, finiteProductPairTotalMass,
      finiteProductPairSignedMass, finiteProductPairBadMass,
      finiteProductPairGoodPositiveMass, finiteProductPairGoodNegativeMass] using h

/-- Both literal product-Möbius signs have at least half the packet cardinality minus half the
absolute product-Möbius imbalance. -/
theorem finiteCoprimeSquarefreeProductPair_bothProductSignCount_lower
    (S : Finset (ℕ × ℕ)) :
    (((finiteCoprimeSquarefreeProductPairPacket S).card : ℝ) -
          |∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        (((finiteCoprimeSquarefreeProductPairPacket S).filter fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = 1).card : ℝ) ∧
      (((finiteCoprimeSquarefreeProductPairPacket S).card : ℝ) -
          |∑ p ∈ finiteCoprimeSquarefreeProductPairPacket S,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        (((finiteCoprimeSquarefreeProductPairPacket S).filter fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = -1).card : ℝ) := by
  classical
  let T := finiteCoprimeSquarefreeProductPairPacket S
  have hmul : ∀ p ∈ T,
      (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) =
        (ArithmeticFunction.moebius p.1 : ℝ) *
          (ArithmeticFunction.moebius p.2 : ℝ) := by
    intro p hp
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Finset.mem_filter.mp hp).2.1]
    norm_cast
  have hone :
      T.filter (fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = 1) =
        T.filter (fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = 1) := by
    ext p
    by_cases hp : p ∈ T
    · simp only [Finset.mem_filter, hp, true_and]
      rw [hmul p hp]
    · simp [hp]
  have hneg :
      T.filter (fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = -1) =
        T.filter (fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = -1) := by
    ext p
    by_cases hp : p ∈ T
    · simp only [Finset.mem_filter, hp, true_and]
      rw [hmul p hp]
    · simp [hp]
  rw [sum_moebius_finiteCoprimeSquarefreeProductPair_eq_sum_mul, ← hone, ← hneg]
  exact finiteCoprimeSquarefreeProductPair_bothSignCount_lower S

/-- The card's literal balanced-window coprime squarefree pair packet. -/
def balancedCoprimeSquarefreeProductPairPacket
    (x h : ℝ) : Finset (ℕ × ℕ) :=
  finiteCoprimeSquarefreeProductPairPacket (RHTower.Sieve.balancedPairs x h)

/-- Exact product-sign factorization on the card's balanced product window. -/
theorem sum_moebius_balancedCoprimeSquarefreeProductPair_eq_sum_mul
    (x h : ℝ) :
    (∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
        (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)) =
      ∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
        (ArithmeticFunction.moebius p.1 : ℝ) *
          (ArithmeticFunction.moebius p.2 : ℝ) := by
  simpa only [balancedCoprimeSquarefreeProductPairPacket] using
    sum_moebius_finiteCoprimeSquarefreeProductPair_eq_sum_mul
      (RHTower.Sieve.balancedPairs x h)

/-- Exact simultaneous two-sign count on the card's balanced product window. -/
theorem balancedCoprimeSquarefreeProductPair_bothSignCount_lower
    (x h : ℝ) :
    (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius p.1 : ℝ) *
              (ArithmeticFunction.moebius p.2 : ℝ)|) / 2 ≤
        (((balancedCoprimeSquarefreeProductPairPacket x h).filter fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = 1).card : ℝ) ∧
      (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius p.1 : ℝ) *
              (ArithmeticFunction.moebius p.2 : ℝ)|) / 2 ≤
        (((balancedCoprimeSquarefreeProductPairPacket x h).filter fun p =>
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (ArithmeticFunction.moebius p.2 : ℝ) = -1).card : ℝ) := by
  simpa only [balancedCoprimeSquarefreeProductPairPacket] using
    finiteCoprimeSquarefreeProductPair_bothSignCount_lower
      (RHTower.Sieve.balancedPairs x h)

/-- Exact simultaneous lower count for the two literal product-Möbius signs on the card's balanced
product window. -/
theorem balancedCoprimeSquarefreeProductPair_bothProductSignCount_lower
    (x h : ℝ) :
    (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        (((balancedCoprimeSquarefreeProductPairPacket x h).filter fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = 1).card : ℝ) ∧
      (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        (((balancedCoprimeSquarefreeProductPairPacket x h).filter fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = -1).card : ℝ) := by
  simpa only [balancedCoprimeSquarefreeProductPairPacket] using
    finiteCoprimeSquarefreeProductPair_bothProductSignCount_lower
      (RHTower.Sieve.balancedPairs x h)

/-- For both signs, the explicit squarefree packet filter is exactly the card's canonical coprime
sign class.  In the reverse direction squarefreeness is forced by the nonzero product sign. -/
theorem balancedCoprimeSquarefreeProductPair_factorSignFilters_eq_coprimeSignClasses
    (x h : ℝ) :
    (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
        ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 = 1) =
      RHTower.Sieve.coprimeSignClass x h 1 ∧
    (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
        ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 = -1) =
      RHTower.Sieve.coprimeSignClass x h (-1) := by
  classical
  constructor
  · rw [balancedCoprimeSquarefreeProductPairPacket,
      finiteCoprimeSquarefreeProductPairPacket, RHTower.Sieve.coprimeSignClass]
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hcop, hsa, hsb⟩, hs⟩
      exact ⟨hp, hs, hcop⟩
    · rintro ⟨hp, hs, hcop⟩
      have ha0 : ArithmeticFunction.moebius p.1 ≠ 0 := by
        intro ha
        rw [ha, zero_mul] at hs
        norm_num at hs
      have hb0 : ArithmeticFunction.moebius p.2 ≠ 0 := by
        intro hb
        rw [hb, mul_zero] at hs
        norm_num at hs
      exact ⟨⟨hp, hcop,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ha0,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hb0⟩, hs⟩
  · rw [balancedCoprimeSquarefreeProductPairPacket,
      finiteCoprimeSquarefreeProductPairPacket, RHTower.Sieve.coprimeSignClass]
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hp, hcop, hsa, hsb⟩, hs⟩
      exact ⟨hp, hs, hcop⟩
    · rintro ⟨hp, hs, hcop⟩
      have ha0 : ArithmeticFunction.moebius p.1 ≠ 0 := by
        intro ha
        rw [ha, zero_mul] at hs
        norm_num at hs
      have hb0 : ArithmeticFunction.moebius p.2 ≠ 0 := by
        intro hb
        rw [hb, mul_zero] at hs
        norm_num at hs
      exact ⟨⟨hp, hcop,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ha0,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hb0⟩, hs⟩

/-- The literal product-Möbius sign filters are exactly the card's canonical coprime sign classes. -/
theorem balancedCoprimeSquarefreeProductPair_productSignFilters_eq_coprimeSignClasses
    (x h : ℝ) :
    (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
        (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = 1) =
      RHTower.Sieve.coprimeSignClass x h 1 ∧
    (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
        (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = -1) =
      RHTower.Sieve.coprimeSignClass x h (-1) := by
  classical
  have hfactor :=
    balancedCoprimeSquarefreeProductPair_factorSignFilters_eq_coprimeSignClasses x h
  constructor
  · calc
      (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = 1) =
          (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
            ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 = 1) := by
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hp, hs⟩
              refine ⟨hp, ?_⟩
              have hs' : ArithmeticFunction.moebius (p.1 * p.2) = 1 := by
                exact_mod_cast hs
              rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
                (Finset.mem_filter.mp hp).2.1] at hs'
              exact hs'
            · rintro ⟨hp, hs⟩
              refine ⟨hp, ?_⟩
              have hs' : ArithmeticFunction.moebius (p.1 * p.2) = 1 := by
                rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
                  (Finset.mem_filter.mp hp).2.1]
                exact hs
              exact_mod_cast hs'
      _ = RHTower.Sieve.coprimeSignClass x h 1 := hfactor.1
  · calc
      (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
          (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) = -1) =
          (balancedCoprimeSquarefreeProductPairPacket x h).filter (fun p =>
            ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 = -1) := by
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hp, hs⟩
              refine ⟨hp, ?_⟩
              have hs' : ArithmeticFunction.moebius (p.1 * p.2) = -1 := by
                exact_mod_cast hs
              rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
                (Finset.mem_filter.mp hp).2.1] at hs'
              exact hs'
            · rintro ⟨hp, hs⟩
              refine ⟨hp, ?_⟩
              have hs' : ArithmeticFunction.moebius (p.1 * p.2) = -1 := by
                rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
                  (Finset.mem_filter.mp hp).2.1]
                exact hs
              exact_mod_cast hs'
      _ = RHTower.Sieve.coprimeSignClass x h (-1) := hfactor.2

/-- Exact finite lower bound stated directly on the card's canonical counts `R₊` and `R₋`. -/
theorem balancedCoprimeSquarefreeProductPair_bothCanonicalSignCount_lower
    (x h : ℝ) :
    (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        RHTower.Sieve.coprimeSignClassCount x h 1 ∧
      (((balancedCoprimeSquarefreeProductPairPacket x h).card : ℝ) -
          |∑ p ∈ balancedCoprimeSquarefreeProductPairPacket x h,
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ)|) / 2 ≤
        RHTower.Sieve.coprimeSignClassCount x h (-1) := by
  have hbound := balancedCoprimeSquarefreeProductPair_bothProductSignCount_lower x h
  have heq :=
    balancedCoprimeSquarefreeProductPair_productSignFilters_eq_coprimeSignClasses x h
  rw [heq.1, heq.2] at hbound
  simpa only [RHTower.Sieve.coprimeSignClassCount] using hbound

end

end RHTower
