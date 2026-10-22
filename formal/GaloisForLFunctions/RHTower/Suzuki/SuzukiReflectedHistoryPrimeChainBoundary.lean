import GaloisForLFunctions.RHTower.PrimeProductCutoffContraction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSuccessorCurvatureHistoryNoGo

/-!
# The reflected Suzuki `2,-3` history is an abelian prime-chain boundary

The reflected successor cell from `2` to `3` is the first literal Suzuki curvature history
carrier whose pruned boundary-excursion skew is nonzero.  Its valuation is the signed two-leg
word `e₂ - e₃`.  This module asks whether that survivor remains nontrivial after forgetting order
and retaining only an abelian prime-chain current.

It does not.  The explicit oriented chain `-(e₂ ∧ e₃)` has boundary `e₂ - e₃`; the latter is a
reduced cycle at prime-product cutoff `3`, while its filling is already present at cutoff `6`.
The statement is source exact: a linear abelianization sends the actual reflected Suzuki
valuation to that cycle.

Thus the surviving pruned chronology cannot be transported by abelian prime-chain homology alone.
Any cofinal P/SP-E carrier that uses this source witness must retain secondary ordered data (for
example a noncommutative boundary-excursion cocycle), rather than only its valuation class.  This
does not bound the completed SP-E current or prove RH.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal prime-two source atom used by the reflected `2,-3` history. -/
def reflectedHistoryPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Literal prime-three source atom used by the reflected `2,-3` history. -/
def reflectedHistoryPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The oriented degree-two prime chain whose boundary is the abelian reflected history. -/
def reflectedTwoThreeHistoryChain : PrimeChainSpace ℤ 2 :=
  -primeChainAtom ℤ ![reflectedHistoryPrimeTwo, reflectedHistoryPrimeThree]

/-- The signed degree-one prime history obtained after forgetting the order of the two legs. -/
def reflectedTwoThreeHistoryBoundary : PrimeChainSpace ℤ 1 :=
  primeChainAtom ℤ ![reflectedHistoryPrimeTwo] -
    primeChainAtom ℤ ![reflectedHistoryPrimeThree]

/-- Linear abelianization from finite Suzuki valuations to degree-one prime chains.  It retains
the signed prime coefficients but deliberately forgets word order and aperture history. -/
def suzukiValuationAbelianization :
    GaloisForLFunctions.RHTower.SuzukiSeamValuation →ₗ[ℤ] PrimeChainSpace ℤ 1 :=
  Finsupp.lsum ℤ fun p =>
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (primeChainAtom ℤ ![p])

/-- Abelianization of a visible Suzuki prime-power step is its signed prime-chain atom. -/
theorem suzukiValuationAbelianization_primePowerStep
    (p : Nat.Primes) (j : ℕ) :
    suzukiValuationAbelianization
      (GaloisForLFunctions.RHTower.suzukiPrimePowerStep (p, j)) =
      (j : ℤ) • primeChainAtom ℤ ![p] := by
  rw [suzukiValuationAbelianization,
    GaloisForLFunctions.RHTower.suzukiPrimePowerStep, Finsupp.lsum_single]
  rfl

/-- The literal oriented `2∧3` chain has exactly the signed `2,-3` history as its boundary. -/
theorem reflectedTwoThreeHistoryChain_boundary :
    primeChainBoundary ℤ 1 reflectedTwoThreeHistoryChain =
      reflectedTwoThreeHistoryBoundary := by
  rw [reflectedTwoThreeHistoryChain, reflectedTwoThreeHistoryBoundary, map_neg,
    primeChainBoundary_atom]
  have hfirst :
      (fun j : Fin 1 =>
        ![reflectedHistoryPrimeTwo, reflectedHistoryPrimeThree] (Fin.succAbove 1 j)) =
        ![reflectedHistoryPrimeTwo] := by
    funext j
    fin_cases j
    rfl
  have hsecond : (fun _ : Fin 1 => reflectedHistoryPrimeThree) =
      ![reflectedHistoryPrimeThree] := by
    funext j
    fin_cases j
    rfl
  rw [sub_eq_add_neg]
  simp [hfirst, hsecond]

/-- The abelian reflected history is reduced: its augmentation to the empty prime face vanishes. -/
theorem reflectedTwoThreeHistoryBoundary_cycle :
    primeChainBoundary ℤ 0 reflectedTwoThreeHistoryBoundary = 0 := by
  rw [reflectedTwoThreeHistoryBoundary, map_sub,
    primeChainBoundary_atom, primeChainBoundary_atom]
  have hempty : (fun _ : Fin 0 => reflectedHistoryPrimeTwo) =
      (fun _ : Fin 0 => reflectedHistoryPrimeThree) := by
    funext i
    exact Fin.elim0 i
  simp [hempty]

/-- The explicit oriented filling is supported at its exact prime-product cutoff `2·3 = 6`. -/
theorem reflectedTwoThreeHistoryChain_mem_cutoff :
    reflectedTwoThreeHistoryChain ∈ primeChainCutoff ℤ 2 6 := by
  rw [reflectedTwoThreeHistoryChain]
  apply Submodule.neg_mem
  apply Submodule.subset_span
  refine ⟨![reflectedHistoryPrimeTwo, reflectedHistoryPrimeThree], ?_, rfl⟩
  norm_num [reflectedHistoryPrimeTwo, reflectedHistoryPrimeThree]

/-- The abelianized signed pair is already supported at cutoff `3`. -/
theorem reflectedTwoThreeHistoryBoundary_mem_cutoff :
    reflectedTwoThreeHistoryBoundary ∈ primeChainCutoff ℤ 1 3 := by
  rw [reflectedTwoThreeHistoryBoundary]
  apply Submodule.sub_mem
  · apply Submodule.subset_span
    refine ⟨![reflectedHistoryPrimeTwo], ?_, rfl⟩
    norm_num [reflectedHistoryPrimeTwo]
  · apply Submodule.subset_span
    refine ⟨![reflectedHistoryPrimeThree], ?_, rfl⟩
    norm_num [reflectedHistoryPrimeThree]

/-- Source-exact comparison: abelianization of the actual reflected Suzuki successor valuation
is the signed prime-chain boundary. -/
theorem suzukiCurvatureSuccessorTwo_reflection_abelianization :
    suzukiValuationAbelianization
      (-GaloisForLFunctions.RHTower.suzukiCurvatureSuccessorValuation 2) =
      reflectedTwoThreeHistoryBoundary := by
  rw [GaloisForLFunctions.RHTower.suzukiCurvatureSuccessorValuation_two_reflection_factorization,
    map_add, map_neg, suzukiValuationAbelianization_primePowerStep,
    suzukiValuationAbelianization_primePowerStep]
  simp [reflectedTwoThreeHistoryBoundary, reflectedHistoryPrimeTwo,
    reflectedHistoryPrimeThree, sub_eq_add_neg]

/-- The actual reflected Suzuki valuation becomes a reduced prime-chain cycle at cutoff `3`. -/
theorem suzukiCurvatureSuccessorTwo_reflection_abelianization_mem_cutoff_cycle :
    suzukiValuationAbelianization
        (-GaloisForLFunctions.RHTower.suzukiCurvatureSuccessorValuation 2) ∈
      primeChainCutoff ℤ 1 3 ⊓ (primeChainBoundary ℤ 0).ker := by
  rw [suzukiCurvatureSuccessorTwo_reflection_abelianization]
  exact ⟨reflectedTwoThreeHistoryBoundary_mem_cutoff,
    reflectedTwoThreeHistoryBoundary_cycle⟩

/-- The cutoff-3 abelianized reflected Suzuki cycle has an explicit literal filling by cutoff
`6`; hence it is null in the cofinal abelian prime-chain carrier. -/
theorem exists_reflectedSuzukiCurvatureSuccessorTwo_abelianization_filling :
    ∃ y : primeChainCutoff ℤ 2 6,
      primeChainBoundary ℤ 1 y =
        suzukiValuationAbelianization
          (-GaloisForLFunctions.RHTower.suzukiCurvatureSuccessorValuation 2) := by
  refine ⟨⟨reflectedTwoThreeHistoryChain, reflectedTwoThreeHistoryChain_mem_cutoff⟩, ?_⟩
  rw [reflectedTwoThreeHistoryChain_boundary,
    suzukiCurvatureSuccessorTwo_reflection_abelianization]

/-- The same reflected source word is nontrivial as ordered aperture chronology but null after
abelian prime-chain cofinalization.  This isolates the exact kind of information a P/SP-E lift
must retain: a secondary ordered boundary-excursion current. -/
theorem exists_reflectedSuzukiCurvatureSuccessorTwo_ordered_nonzero_abelian_null :
    ∃ a : ℝ, 0 < a ∧
      GaloisForLFunctions.RHTower.suzukiPrunedBoundaryExcursion a
          (GaloisForLFunctions.RHTower.suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1))
          (-GaloisForLFunctions.RHTower.suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1)) -
        GaloisForLFunctions.RHTower.suzukiPrunedBoundaryExcursion a
          (-GaloisForLFunctions.RHTower.suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1))
          (GaloisForLFunctions.RHTower.suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1)) ≠ 0 ∧
      ∃ y : primeChainCutoff ℤ 2 6,
        primeChainBoundary ℤ 1 y =
          suzukiValuationAbelianization
            (-GaloisForLFunctions.RHTower.suzukiCurvatureSuccessorValuation 2) := by
  obtain ⟨a, ha, hskew⟩ :=
    GaloisForLFunctions.RHTower.exists_suzukiCurvatureSuccessorTwo_reflectedFactorized_boundaryExcursion_skew_nonzero
  exact ⟨a, ha, hskew,
    exists_reflectedSuzukiCurvatureSuccessorTwo_abelianization_filling⟩

end

end RHTower
