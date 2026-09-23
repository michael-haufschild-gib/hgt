import GaloisForLFunctions.RHTower.PrimeSupportBoundaryJets

/-!
# Binary lift parity cannot see the full prime-support boundary germ

A `2`-lift signing evaluates a word through the parity of each edge multiplicity.  Consequently,
adding two occurrences of a previously absent label leaves every signing character unchanged even
though it increases the distinct-support cardinality.  The prime-support boundary jets distinguish
the two words exactly.

This rules out an unmarked binary signing as the finite carrier for the boundary-jet tower.  The
positive successor is a multivariate edge-zeta or marked lift character that retains full support
before any parity specialization.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open Polynomial

/-- The character of a two-label word seen by a binary graph-lift signing. -/
def binaryLiftCharacter (σ : Fin 2 → ℤ) (m : Fin 2 → ℕ) : ℤ :=
  ∏ i, σ i ^ m i

/-- A word using only the first label once. -/
def singletonLiftMultiplicity : Fin 2 → ℕ
  | 0 => 1
  | 1 => 0

/-- A word using the first label once and the second label twice. -/
def doubledSecondLiftMultiplicity : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

/-- The number of distinct labels occurring in a finite multiplicity packet. -/
def liftMultiplicitySupportCard (m : Fin 2 → ℕ) : ℕ :=
  (Finset.univ.filter fun i => m i ≠ 0).card

/-- Every binary signing gives the singleton word and the word with a doubled new label the same
character.  This is the parity blindness of an ordinary `2`-lift. -/
theorem binaryLiftCharacter_support_blind
    (σ : Fin 2 → ℤ) (hσ : ∀ i, σ i ^ (2 : ℕ) = 1) :
    binaryLiftCharacter σ singletonLiftMultiplicity =
      binaryLiftCharacter σ doubledSecondLiftMultiplicity := by
  simp [binaryLiftCharacter, singletonLiftMultiplicity, doubledSecondLiftMultiplicity, hσ]

/-- The singleton word has support cardinality one. -/
theorem singletonLiftMultiplicity_supportCard :
    liftMultiplicitySupportCard singletonLiftMultiplicity = 1 := by
  decide

/-- Adding the doubled second label raises the support cardinality to two. -/
theorem doubledSecondLiftMultiplicity_supportCard :
    liftMultiplicitySupportCard doubledSecondLiftMultiplicity = 2 := by
  decide

/-- The two words are indistinguishable to every binary signing but are separated by the first two
prime-support boundary jets. -/
theorem binaryLiftCharacter_blind_but_boundaryJets_separate
    (σ : Fin 2 → ℤ) (hσ : ∀ i, σ i ^ (2 : ℕ) = 1) :
    binaryLiftCharacter σ singletonLiftMultiplicity =
        binaryLiftCharacter σ doubledSecondLiftMultiplicity ∧
      ((derivative^[0]) (primeSupportMarkedDeformation 1)).eval 1 = 1 ∧
      ((derivative^[0]) (primeSupportMarkedDeformation 2)).eval 1 = 0 ∧
      ((derivative^[1]) (primeSupportMarkedDeformation 1)).eval 1 = 0 ∧
      ((derivative^[1]) (primeSupportMarkedDeformation 2)).eval 1 = -2 := by
  refine ⟨binaryLiftCharacter_support_blind σ hσ, ?_⟩
  constructor
  · simpa using primeSupportMarkedDeformation_boundaryJet 1 0
  constructor
  · simpa using primeSupportMarkedDeformation_boundaryJet 2 0
  constructor
  · simpa using primeSupportMarkedDeformation_boundaryJet 1 1
  · simpa using primeSupportMarkedDeformation_boundaryJet 2 1

end GaloisForLFunctions.RHTower
