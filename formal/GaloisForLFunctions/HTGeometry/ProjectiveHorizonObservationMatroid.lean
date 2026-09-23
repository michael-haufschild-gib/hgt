import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# Arbitrary reciprocal-jet observations and their path balance

For an inverse jet `Y`, the infinitesimal reciprocal response to a raw monomial of degree `c`
has degree-`b` coefficient `-[t^(b-c)]Y^(2 : ℕ)`, with zero when `c > b`.  Thus every arbitrary finite
mixed raw/reciprocal observation cut is controlled by a lower-Toeplitz minor, not only the
consecutive horizon cuts treated by `ProjectiveHorizonSchurCaustic`.

The second part records the source-pure combinatorics behind the resulting Catalan-matroid bridge.
If the ordered missing-raw indices occur no later than the ordered observed-reciprocal indices,
every resolution prefix has nonnegative latent-information balance.  The resolution order is a
static filtration and is not a time evolution.
-/

open Polynomial
open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The reciprocal Jacobian on arbitrary ordered row and column indices. -/
noncomputable def arbitraryReciprocalJacobian {K : Type*} [CommRing K] {k : ℕ}
    (Y : K[X]) (rows cols : Fin k → ℕ) : Matrix (Fin k) (Fin k) K :=
  fun i j =>
    (criticalReciprocalInfinitesimal Y (X ^ cols j)).coeff (rows i)

/-- The lower-Toeplitz section of the squared reciprocal coefficients on arbitrary indices. -/
def arbitrarySquaredReciprocalToeplitz {K : Type*} [Zero K] {k : ℕ}
    (q : ℕ → K) (rows cols : Fin k → ℕ) : Matrix (Fin k) (Fin k) K :=
  fun i j => if cols j ≤ rows i then q (rows i - cols j) else 0

/-- Every arbitrary reciprocal Jacobian entry is the negative corresponding lower-Toeplitz
coefficient of `Y^(2 : ℕ)`. -/
theorem arbitraryReciprocalJacobian_apply {K : Type*} [CommRing K] {k : ℕ}
    (Y : K[X]) (rows cols : Fin k → ℕ) (i j : Fin k) :
    arbitraryReciprocalJacobian Y rows cols i j =
      -arbitrarySquaredReciprocalToeplitz
        (fun d => (Y * Y).coeff d) rows cols i j := by
  simp only [arbitraryReciprocalJacobian, criticalReciprocalInfinitesimal,
    coeff_neg, arbitrarySquaredReciprocalToeplitz]
  rw [coeff_mul_X_pow']

/-- The arbitrary-cut reciprocal Jacobian is exactly a negative lower-Toeplitz minor. -/
theorem arbitraryReciprocalJacobian_eq_neg_toeplitz
    {K : Type*} [CommRing K] {k : ℕ}
    (Y : K[X]) (rows cols : Fin k → ℕ) :
    arbitraryReciprocalJacobian Y rows cols =
      -arbitrarySquaredReciprocalToeplitz
        (fun d => (Y * Y).coeff d) rows cols := by
  ext i j
  exact arbitraryReciprocalJacobian_apply Y rows cols i j

/-- Number of entries of an ordered index packet that have appeared before resolution `r`. -/
def indexedObservationPrefixCount {k n : ℕ} (indices : Fin k → Fin n) (r : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i => (indices i : ℕ) < r).card

/-- Static latent-information height: missing raw coordinates minus observed reciprocal
coordinates in a resolution prefix. -/
def indexedObservationHeight {k n : ℕ}
    (missingRaw observedReciprocal : Fin k → Fin n) (r : ℕ) : ℤ :=
  indexedObservationPrefixCount missingRaw r -
    indexedObservationPrefixCount observedReciprocal r

/-- Componentwise order of the missing-raw packet before the reciprocal-observation packet forces
the correct prefix-count inequality at every resolution. -/
theorem indexedObservationPrefixCount_le_of_componentwise
    {k n : ℕ} {missingRaw observedReciprocal : Fin k → Fin n}
    (h : ∀ i, missingRaw i ≤ observedReciprocal i) (r : ℕ) :
    indexedObservationPrefixCount observedReciprocal r ≤
      indexedObservationPrefixCount missingRaw r := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_le_of_lt (h i) hi

/-- Under the componentwise observation law, every finite resolution prefix has nonnegative
latent-information height. -/
theorem indexedObservationHeight_nonnegative_of_componentwise
    {k n : ℕ} {missingRaw observedReciprocal : Fin k → Fin n}
    (h : ∀ i, missingRaw i ≤ observedReciprocal i) (r : ℕ) :
    0 ≤ indexedObservationHeight missingRaw observedReciprocal r := by
  simp only [indexedObservationHeight]
  exact sub_nonneg.mpr <| by
    exact_mod_cast indexedObservationPrefixCount_le_of_componentwise h r

/-- Every complete equal-cardinality observation packet returns to height zero after the last
finite-jet resolution. -/
theorem indexedObservationHeight_terminal
    {k n : ℕ} (missingRaw observedReciprocal : Fin k → Fin n) :
    indexedObservationHeight missingRaw observedReciprocal n = 0 := by
  simp [indexedObservationHeight, indexedObservationPrefixCount]

/-- The four possible local states of a raw/reciprocal observation cut. -/
inductive ReciprocalObservationStep
  | up
  | down
  | rawOnly
  | reciprocalOnly
  deriving DecidableEq

/-- Encode whether the raw coordinate is missing and the reciprocal coordinate is observed. -/
def reciprocalObservationStep
    (rawMissing reciprocalObserved : Bool) : ReciprocalObservationStep :=
  match rawMissing, reciprocalObserved with
  | true, false => .up
  | false, true => .down
  | false, false => .rawOnly
  | true, true => .reciprocalOnly

/-- Height change of one static resolution step. -/
def ReciprocalObservationStep.heightChange : ReciprocalObservationStep → ℤ
  | .up => 1
  | .down => -1
  | .rawOnly => 0
  | .reciprocalOnly => 0

/-- The four-state path height is exactly missing-raw information minus doubly observed
information at that resolution. -/
theorem reciprocalObservationStep_heightChange
    (rawMissing reciprocalObserved : Bool) :
    (reciprocalObservationStep rawMissing reciprocalObserved).heightChange =
      (if rawMissing then 1 else 0) - (if reciprocalObserved then 1 else 0) := by
  cases rawMissing <;> cases reciprocalObserved <;>
    rfl

end GaloisForLFunctions.HTGeometry
