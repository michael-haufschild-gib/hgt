import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianRadicalConnector

/-!
# Gaussian principal minors and the transverse Xi differential matroid

Positive principal minors of the first transverse valuation Gaussian kernel represent the
ordinary collision matroid of the integral shift labels: repetitions are parallel, but zero is an
ordinary label.  The actual transverse differential matroid over either the rational-coordinate
base or the complete scalar-valuation base is the pointed version of the same collision matroid,
with zero distinguished as a loop.

Consequently this connector works on every finite subpacket, not only the full shift family.  Its
rank law isolates the whole metric/differential discrepancy: differential rank is Gaussian
collision rank minus one exactly when the selected packet contains a zero shift.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open Matrix
open scoped ComplexOrder Differential Matroid

local instance xiGaussianMatroidUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiGaussianMatroidUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiGaussianMatroidUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiGaussianMatroidUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiGaussianMatroidCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiGaussianMatroidCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiGaussianMatroidAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiGaussianMatroidAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Gaussian principal Gram selected by a finite packet of shift indices. -/
def xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ)
    (I : Finset (Fin N)) : Matrix I I ℝ :=
  finiteGaussianDistanceGram
    (fun i : I => xiTransversePrimeFirstValuationGaussianFeature (shift i) p) t

/-- At positive bandwidth, a Gaussian principal minor is strictly positive exactly when its
selected shift labels are collision-free. -/
theorem xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_posDef_iff_injOn
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).PosDef ↔
      Set.InjOn shift (↑I : Set (Fin N)) := by
  rw [xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix,
    finiteGaussianDistanceGram_posDef_iff_injective_of_pos_fintype _ ht]
  constructor
  · intro hcomp i hi j hj hij
    have hsub : (⟨i, hi⟩ : I) = ⟨j, hj⟩ := by
      apply hcomp
      exact congrArg
        (fun a => xiTransversePrimeFirstValuationGaussianFeature a p) hij
    exact congrArg Subtype.val hsub
  · intro hinj i j hij
    apply Subtype.ext
    apply hinj i.2 j.2
    apply xiTransversePrimeFirstValuationGaussianFeature_injective p
    exact hij

/-- The rank of every Gaussian principal minor is exactly the number of distinct shift labels in
that packet. -/
theorem xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_rank_eq_image_card
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).rank =
      (I.image shift).card := by
  rw [xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix,
    finiteGaussianDistanceGram_rank_eq_image_card_of_pos _ ht]
  calc
    (Finset.univ.image
        (fun i : I => xiTransversePrimeFirstValuationGaussianFeature (shift i) p)).card =
        ((Finset.univ.image (fun i : I => shift i)).image
          (fun a => xiTransversePrimeFirstValuationGaussianFeature a p)).card := by
      congr 1
      ext b
      simp
    _ = (Finset.univ.image (fun i : I => shift i)).card :=
      Finset.card_image_of_injective _
        (xiTransversePrimeFirstValuationGaussianFeature_injective p)
    _ = (I.image shift).card := by
      congr 1
      ext a
      simp

/-- The existing affine collision matroid is exactly the positivity matroid of the Gaussian
principal minors at every positive bandwidth. -/
theorem xiTransverseGaussianCollisionMatroid_indep_iff_principalGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    (affineCollisionMatroid shift).Indep (↑I : Set (Fin N)) ↔
      (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).PosDef := by
  rw [affineCollisionMatroid_indep_iff,
    xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_posDef_iff_injOn _ _ ht]

/-- **Principal-minor Gaussian/differential radical law.** Over the rational-coordinate base, an
arbitrary finite packet is differential-matroid independent exactly when its Gaussian principal
minor is positive and the packet avoids the zero shift. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialMatroid_indep_iff_gaussianPrincipalGram_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).Indep
          (↑I : Set (Fin N)) ↔
      (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).PosDef ∧
        ∀ i ∈ I, shift i ≠ 0 := by
  rw [xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_indep_iff,
    xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_posDef_iff_injOn _ _ ht]
  rfl

/-- The principal-minor radical law survives after adjoining every scalar prime-valuation layer. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_indep_iff_gaussianPrincipalGram_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).Indep
          (↑I : Set (Fin N)) ↔
      (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).PosDef ∧
        ∀ i ∈ I, shift i ≠ 0 := by
  rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_indep_iff,
    xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_posDef_iff_injOn _ _ ht]
  rfl

/-- **Exact zero-loop rank fracture.** Gaussian collision rank exceeds rational-base transverse
differential rank by one precisely when the selected packet contains a zero shift. -/
theorem xiTransverseGaussianCollisionMatroid_eRk_eq_baseDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (I : Finset (Fin N)) :
    (affineCollisionMatroid shift).eRk (↑I : Set (Fin N)) =
      (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk
          (↑I : Set (Fin N)) +
        if 0 ∈ I.image shift then 1 else 0 := by
  rw [affineCollisionMatroid_eRk_finset,
    xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk_finset]
  by_cases hzero : 0 ∈ I.image shift
  · rw [if_pos hzero]
    norm_cast
    exact (Finset.card_erase_add_one hzero).symm
  · rw [if_neg hzero]
    rw [Finset.erase_eq_self.mpr hzero]
    simp

/-- The exact zero-loop rank fracture is unchanged over the complete scalar-valuation base. -/
theorem xiTransverseGaussianCollisionMatroid_eRk_eq_allValuationDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (I : Finset (Fin N)) :
    (affineCollisionMatroid shift).eRk (↑I : Set (Fin N)) =
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk
          (↑I : Set (Fin N)) +
        if 0 ∈ I.image shift then 1 else 0 := by
  rw [affineCollisionMatroid_eRk_finset,
    xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk_finset]
  by_cases hzero : 0 ∈ I.image shift
  · rw [if_pos hzero]
    norm_cast
    exact (Finset.card_erase_add_one hzero).symm
  · rw [if_neg hzero]
    rw [Finset.erase_eq_self.mpr hzero]
    simp

/-- **Literal matrix-rank fracture.** At every positive bandwidth, the rank of each Gaussian
principal matrix equals rational-base transverse differential rank plus exactly the zero-loop
indicator. -/
theorem
    xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_rank_eq_baseDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    ((xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).rank : ℕ∞) =
      (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk
          (↑I : Set (Fin N)) +
        if 0 ∈ I.image shift then 1 else 0 := by
  rw [xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_rank_eq_image_card
    shift p ht I]
  simpa [affineCollisionMatroid_eRk_finset] using
    xiTransverseGaussianCollisionMatroid_eRk_eq_baseDifferential_eRk_add_zero shift I

/-- The literal Gaussian/differential matrix-rank fracture is unchanged after adjoining all scalar
prime-valuation layers. -/
theorem
    xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_rank_eq_allValuationDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t)
    (I : Finset (Fin N)) :
    ((xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix shift p t I).rank : ℕ∞) =
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk
          (↑I : Set (Fin N)) +
        if 0 ∈ I.image shift then 1 else 0 := by
  rw [xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix_rank_eq_image_card
    shift p ht I]
  simpa [affineCollisionMatroid_eRk_finset] using
    xiTransverseGaussianCollisionMatroid_eRk_eq_allValuationDifferential_eRk_add_zero shift I

/-- On the whole packet, the Gaussian Gram rank exceeds rational-base transverse differential rank
exactly when zero occurs among the shifts. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_baseDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    ((xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).rank : ℕ∞) =
      (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
        if 0 ∈ Finset.univ.image shift then 1 else 0 := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_image_card shift p ht]
  have h :=
    xiTransverseGaussianCollisionMatroid_eRk_eq_baseDifferential_eRk_add_zero
      shift Finset.univ
  rw [affineCollisionMatroid_eRk_finset] at h
  simpa using h

/-- The same whole-packet matrix-rank law holds over the complete scalar-valuation base. -/
theorem
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_allValuationDifferential_eRk_add_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    ((xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).rank : ℕ∞) =
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
        if 0 ∈ Finset.univ.image shift then 1 else 0 := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_image_card shift p ht]
  have h :=
    xiTransverseGaussianCollisionMatroid_eRk_eq_allValuationDifferential_eRk_add_zero
      shift Finset.univ
  rw [affineCollisionMatroid_eRk_finset] at h
  simpa using h

end

end RHTower
