import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22Identity
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceClosure

/-!
# One tagged finite family of retained boxes

The four retained box families are combined through disjoint sums.  Tags preserve multiplicity,
and the negative signs of the one-prime and triple terms are incorporated into their functions.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

abbrev MTHarmanRetainedBoxIndex (outerQ outerD recDepth : ℕ) :=
  MTOuterSeparatedBoxIndex (Fin 1) recDepth ⊕
    (MTOuterSeparatedBoxIndex (Fin outerQ) recDepth ⊕
      (MTPairSeparatedBoxIndex outerD recDepth ⊕
        MTTripleSeparatedBoxIndex outerD recDepth))

local instance instDecidableEqMTHarmanRetainedBoxIndex
    (outerQ outerD recDepth : ℕ) :
    DecidableEq (MTHarmanRetainedBoxIndex outerQ outerD recDepth) := Classical.decEq _

local instance instDecidableEqMTTripleSeparatedBoxIndexFamily
    (outerD recDepth : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex outerD recDepth) := Classical.decEq _

def mtHarmanRetainedBoxIndexSet {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    Finset (MTHarmanRetainedBoxIndex outerQ outerD recDepth) :=
  (mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y).disjSum
  ((mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y).disjSum
  ((mtProductScaleIndices
      (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedPairBoxScale endpointD delta recStart) Y).disjSum
    (mtProductScaleIndices
      (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedTripleBoxScale endpointD delta recStart) Y)))

def mtHarmanRetainedBoxAF {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ)
    (data : MTFiniteIterationSourceData recDepth) (delta : ℝ) :
    MTHarmanRetainedBoxIndex outerQ outerD recDepth → ArithmeticFunction ℂ
  | Sum.inl idx =>
      mtOuterSeparatedBoxAF mtBaseOuterAlpha data data.z₀ data.D delta idx
  | Sum.inr (Sum.inl idx) =>
      -mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
        data data.z₀ data.D delta idx
  | Sum.inr (Sum.inr (Sum.inl idx)) =>
      mtSeparatedPairBoxAF endpointD (primesIco z D)
        data data.z₀ data.D delta idx
  | Sum.inr (Sum.inr (Sum.inr idx)) =>
      -mtSeparatedTripleBoxAF endpointD (primesIco z D)
        data data.z₀ data.D delta idx

/-- The tagged family sum is definitionally the retained Harman main. -/
theorem sum_mtHarmanRetainedBoxAF_eq_main
    {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    ∑ idx ∈ mtHarmanRetainedBoxIndexSet (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD E data maxDepth j delta N recStart Y,
      mtHarmanRetainedBoxAF endpointQ endpointD z Q D data delta idx =
    mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
      endpointQ endpointD z Q D E data maxDepth j delta N recStart Y := by
  unfold mtHarmanRetainedBoxIndexSet mtHarmanRetainedBoxMainAF
  rw [Finset.sum_disjSum, Finset.sum_disjSum, Finset.sum_disjSum]
  simp only [mtHarmanRetainedBoxAF]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  abel

theorem card_mtHarmanRetainedBoxIndexSet
    {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    (mtHarmanRetainedBoxIndexSet (outerQ := outerQ) (outerD := outerD)
      endpointQ endpointD E data maxDepth j delta N recStart Y).card =
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
          data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y).card +
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
          data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y).card +
      (mtProductScaleIndices
        (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedPairBoxScale endpointD delta recStart) Y).card +
      (mtProductScaleIndices
        (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedTripleBoxScale endpointD delta recStart) Y).card := by
  simp [mtHarmanRetainedBoxIndexSet, Finset.card_disjSum, add_assoc]

end

end RHTower.Sieve
