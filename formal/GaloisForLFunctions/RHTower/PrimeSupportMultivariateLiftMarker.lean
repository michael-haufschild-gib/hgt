import GaloisForLFunctions.RHTower.PrimeSupportLiftParityNoGo
import GaloisForLFunctions.HTGeometry.PrimeWordSupportSelector
import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# A multivariate lift marker retains the prime-support germ

The binary-lift character forgets even edge multiplicities.  Before any lift-phase specialization,
the squarefree multivariate monomial supported on the distinct letters of a word retains exactly
the datum required by the prime-support boundary jets.

This is the positive finite successor to `PrimeSupportLiftParityNoGo`: an edge-zeta construction
must first retain this multivariate marker and may specialize to lift characters only afterward.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open MvPolynomial

/-- The squarefree multivariate marker of the distinct labels in a prime word. -/
noncomputable def primeWordSquarefreeMarker {α : Type*} [DecidableEq α]
    (w : List α) : MvPolynomial α ℤ :=
  ∏ i ∈ GaloisForLFunctions.primeWordSupport w, X i

/-- The marker is the squarefree monomial with indicator exponent of the word support. -/
theorem primeWordSquarefreeMarker_eq_monomial {α : Type*} [DecidableEq α]
    (w : List α) :
    primeWordSquarefreeMarker w =
      monomial (∑ i ∈ GaloisForLFunctions.primeWordSupport w, Finsupp.single i 1) 1 := by
  exact GaloisForLFunctions.VeroneseIdeal.prod_X_eq_monomial _

/-- The indicator exponent of the marker has exactly the word's distinct-letter support. -/
theorem primeWordSquarefreeMarker_exponent_support {α : Type*} [DecidableEq α]
    (w : List α) :
    (∑ i ∈ GaloisForLFunctions.primeWordSupport w,
      Finsupp.single i (1 : ℕ)).support = GaloisForLFunctions.primeWordSupport w := by
  exact GaloisForLFunctions.VeroneseIdeal.support_sum_single _

/-- Specialization evaluates the marker as the product of the phase variables on distinct support,
not as the parity character of the original multiplicity packet. -/
theorem eval_primeWordSquarefreeMarker {α : Type*} [DecidableEq α]
    (σ : α → ℤ) (w : List α) :
    eval σ (primeWordSquarefreeMarker w) =
      ∏ i ∈ GaloisForLFunctions.primeWordSupport w, σ i := by
  simp [primeWordSquarefreeMarker]

/-- Evaluation of the support marker in any commutative ring is the product over the distinct
letters of the word.  This is the coefficient-changing form used by analytic and spectral
specializations of the marker. -/
theorem eval₂Hom_primeWordSquarefreeMarker
    {α R : Type*} [DecidableEq α] [CommRing R]
    (f : α → R) (w : List α) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) f
        (primeWordSquarefreeMarker w) =
      ∏ i ∈ GaloisForLFunctions.primeWordSupport w, f i := by
  simp [primeWordSquarefreeMarker]

/-- Word corresponding to the singleton multiplicity packet in the parity no-go. -/
def singletonLiftWord : List (Fin 2) := [0]

/-- Word corresponding to the packet with one first label and a doubled second label. -/
def doubledSecondLiftWord : List (Fin 2) := [0, 1, 1]

theorem singletonLiftWord_support :
    GaloisForLFunctions.primeWordSupport singletonLiftWord = {0} := by
  decide

theorem doubledSecondLiftWord_support :
    GaloisForLFunctions.primeWordSupport doubledSecondLiftWord = {0, 1} := by
  decide

/-- The squarefree multivariate marker separates the pair that every binary signing character
identifies. -/
theorem primeWordSquarefreeMarker_separates_parityBlindWords :
    primeWordSquarefreeMarker singletonLiftWord ≠
      primeWordSquarefreeMarker doubledSecondLiftWord := by
  intro h
  have hc := congrArg (fun P : MvPolynomial (Fin 2) ℤ =>
    coeff (Finsupp.single 0 1) P) h
  norm_num [primeWordSquarefreeMarker, singletonLiftWord, doubledSecondLiftWord,
    GaloisForLFunctions.primeWordSupport, X] at hc

/-- Positive capstone: the same pair is invisible after binary specialization but separated before
specialization by its canonical squarefree source marker. -/
theorem multivariateMarker_repairs_binaryLift_support_blindness
    (σ : Fin 2 → ℤ) (hσ : ∀ i, σ i ^ (2 : ℕ) = 1) :
    binaryLiftCharacter σ singletonLiftMultiplicity =
        binaryLiftCharacter σ doubledSecondLiftMultiplicity ∧
      primeWordSquarefreeMarker singletonLiftWord ≠
        primeWordSquarefreeMarker doubledSecondLiftWord :=
  ⟨binaryLiftCharacter_support_blind σ hσ,
    primeWordSquarefreeMarker_separates_parityBlindWords⟩

end GaloisForLFunctions.RHTower
