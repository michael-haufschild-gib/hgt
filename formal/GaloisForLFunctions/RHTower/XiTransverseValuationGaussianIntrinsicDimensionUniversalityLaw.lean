import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureSignDuality
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Xi transverse valuation Gaussian intrinsic-dimension universality

The first transverse valuation coordinate embeds a collision-free integral shift packet in a
one-dimensional real Hilbert space.  Existing HilbertMetric results give an intrinsic centered
Gaussian determinant whose logarithmic metric scale is convex and whose affine-dimension power
scale is concave.  Packet rank two forces the intrinsic affine dimension to be exactly one, so the
power coordinate collapses to the ordinary logarithmic reparametrization.

This file connects that intrinsic dimension sandwich to the existing collision-only Gaussian
sign-duality phase.  The equivalence is independent of the prime used for curvature and the prime
used for the intrinsic geometry, and introduces no analytic premise.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped Differential Matroid

open scoped UpperEndDifferentialInstances

/-- First transverse valuation configuration in mathlib's finite Euclidean Hilbert wrapper. -/
def xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Fin N → EuclideanSpace ℝ (Fin 1) :=
  fun j => WithLp.toLp 2
    (xiTransversePrimeFirstValuationCoherentConfiguration shift p j)

/-- The intrinsic Hilbert wrapper identifies two packet entries exactly when their integral shift
labels coincide. -/
theorem xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (i j : Fin N) :
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p i =
        xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p j ↔
      shift i = shift j := by
  constructor
  · intro hij
    apply xiTransversePrimeFirstValuationGaussianFeature_injective p
    exact WithLp.toLp_injective 2 hij
  · intro hij
    simp [xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration,
      xiTransversePrimeFirstValuationCoherentConfiguration, hij]

/-- The intrinsic Hilbert wrapper remembers exactly the shift-collision relation. -/
theorem xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_injective_iff
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Function.Injective
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) ↔
      Function.Injective shift := by
  constructor
  · intro hconfiguration i j hij
    apply hconfiguration
    exact
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
        shift p i j).2 hij
  · intro hshift i j hij
    apply hshift
    exact
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
        shift p i j).1 hij

/-- Intrinsic centered Gaussian log determinant of the first transverse valuation configuration. -/
def xiTransversePrimeValuationCorrectedGaussianLogScale
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (s : ℝ) : ℝ :=
  gaussianCorrectedLogScale
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) s

/-- Intrinsic affine-dimension power coordinate for the corrected first-valuation determinant. -/
def xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (u : ℝ) : ℝ :=
  gaussianCorrectedDimensionPowerLogDet
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) u

/-- Literal positive-bandwidth logarithm of the corrected first-valuation determinant. -/
def xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (u : ℝ) : ℝ :=
  Real.log
    (gaussianCorrectedDeterminant
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) u)

/-- **Exact arbitrary-collision intrinsic dimension.**  The first-valuation configuration has
affine dimension one exactly when the shift packet contains two distinct labels. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_exists_pair_ne
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      ∃ i j, shift i ≠ shift j := by
  let x := xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p
  have hle :
      gaussianAffineDimension x ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) := by
    unfold gaussianAffineDimension
    exact Submodule.finrank_le _
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by
    simp
  rw [hambient] at hle
  have hpos :
      0 < gaussianAffineDimension x ↔ ∃ i j, shift i ≠ shift j := by
    rw [gaussianAffineDimension_pos_iff_exists_pair_ne]
    constructor
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, fun h =>
        hij
          ((xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
            shift p i j).2 h)⟩
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, fun h =>
        hij
          ((xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
            shift p i j).1 h)⟩
  constructor
  · intro hone
    apply hpos.1
    rw [hone]
    simp
  · intro hpair
    have hpositive : 0 < gaussianAffineDimension x := hpos.2 hpair
    exact Nat.le_antisymm hle hpositive

/-- A finite shift packet contains two distinct labels exactly when its occupied-label image has
cardinality at least two. -/
theorem xiTransverseShift_exists_pair_ne_iff_two_le_image_card
    {N : ℕ} (shift : Fin N → ℕ) :
    (∃ i j, shift i ≠ shift j) ↔
      2 ≤ (Finset.univ.image shift).card := by
  constructor
  · rintro ⟨i, j, hij⟩
    have hone : 1 < (Finset.univ.image shift).card :=
      Finset.one_lt_card.mpr
        ⟨shift i, by simp, shift j, by simp, hij⟩
    omega
  · intro hcard
    have hone : 1 < (Finset.univ.image shift).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hone
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨i, j, hab⟩

/-- Intrinsic dimension one is exactly occupied-label collision rank at least two. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      2 ≤ (Finset.univ.image shift).card :=
  (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_exists_pair_ne
    shift p).trans
      (xiTransverseShift_exists_pair_ne_iff_two_le_image_card shift)

/-- The intrinsic first-valuation geometry is completely classified for every packet: its affine
dimension is the indicator that at least two distinct shift labels occur. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_classification
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) =
      if 2 ≤ (Finset.univ.image shift).card then 1 else 0 := by
  by_cases hcard : 2 ≤ (Finset.univ.image shift).card
  · rw [if_pos hcard]
    exact
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card
        shift p).2 hcard
  · rw [if_neg hcard]
    apply (gaussianAffineDimension_eq_zero_iff _).2
    intro i j
    apply
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_apply_eq_iff
        shift p i j).2
    by_contra hij
    exact hcard
      ((xiTransverseShift_exists_pair_ne_iff_two_le_image_card shift).1
        ⟨i, j, hij⟩)

/-- Intrinsic affine dimension is independent of the prime used for the first valuation. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_prime_invariant
    {N : ℕ} (shift : Fin N → ℕ) (p q : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) =
      gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift q) := by
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_classification,
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_classification]

/-- **Hilbert/collision-matroid dimension bridge.**  Intrinsic affine dimension one is exactly
collision-matroid rank at least two, with no injectivity or bandwidth premise. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_collisionRank_two_le
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      (2 : ℕ∞) ≤
        (affineCollisionMatroid shift).eRk Set.univ := by
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card,
    ← Finset.coe_univ,
    affineCollisionMatroid_eRk_finset]
  norm_cast

/-- **Hilbert/base-differential dimension bridge.**  Intrinsic affine dimension one is exactly
augmented rational-base differential rank at least two; the augmentation restores the unique zero
loop omitted by transverse differential geometry. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_baseDifferentialRankWithZero_two_le
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      (2 : ℕ∞) ≤
        (differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
            if 0 ∈ Finset.univ.image shift then 1 else 0 := by
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_collisionRank_two_le,
    ← Finset.coe_univ,
    xiTransverseGaussianCollisionMatroid_eRk_eq_baseDifferential_eRk_add_zero]

/-- The intrinsic/differential dimension bridge survives adjoining every scalar prime-valuation
layer to the coefficient field. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_allValuationDifferentialRankWithZero_two_le
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      (2 : ℕ∞) ≤
        (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
            if 0 ∈ Finset.univ.image shift then 1 else 0 := by
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_collisionRank_two_le,
    ← Finset.coe_univ,
    xiTransverseGaussianCollisionMatroid_eRk_eq_allValuationDifferential_eRk_add_zero]

/-- Under collision freedom, intrinsic affine dimension one is exactly packet rank at least two.
This is the converse completion of the existing dimension-one construction. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_two_le_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 ↔
      2 ≤ N := by
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card,
    Finset.card_image_of_injective _ hinjective,
    Finset.card_univ,
    Fintype.card_fin]

/-- Cross-prime equivalence chain joining strict Gaussian curvature, operator nonnormality,
intrinsic affine dimension, and zero-augmented differential rank over both coefficient fields. -/
def XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
    {N : ℕ} (shift : Fin N → ℕ)
    (curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (curvatureScale operatorScale : ℝ) : Prop :=
  (deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          shift curvaturePrime s).det)) curvatureScale < 0 ↔
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        shift operatorPrime operatorScale) ≠ 0) ∧
  (matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        shift operatorPrime operatorScale) ≠ 0 ↔
    gaussianAffineDimension
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
        shift intrinsicPrime) = 1) ∧
  (gaussianAffineDimension
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
        shift intrinsicPrime) = 1 ↔
    (2 : ℕ∞) ≤
      (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
          if 0 ∈ Finset.univ.image shift then 1 else 0) ∧
  (((2 : ℕ∞) ≤
      ((differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
          (if 0 ∈ Finset.univ.image shift then 1 else 0))) ↔
    ((2 : ℕ∞) ≤
      ((differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
          (if 0 ∈ Finset.univ.image shift then 1 else 0))))

/-- **Cross-prime Gaussian/HTGeometry phase universality.**  For a collision-free packet,
strict curvature and nonnormality at independently chosen primes and nonnegative scales are
equivalent; nonnormality is exactly intrinsic dimension one at any third prime; and intrinsic
dimension is exactly the zero-augmented differential rank threshold over both coefficient
fields. -/
theorem
    xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    {N : ℕ} (shift : Fin N → ℕ)
    (curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hinjective : Function.Injective shift) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift curvaturePrime operatorPrime intrinsicPrime
        curvatureScale operatorScale := by
  unfold
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
  have hcurvature :=
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_injective
      shift curvaturePrime hinjective curvatureScale hcurvatureScale
  have hnonnormal :=
    xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_injective
      shift operatorPrime hinjective operatorScale hoperatorScale
  have hdimension :=
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_two_le_of_injective
      shift intrinsicPrime hinjective
  have hbase :=
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_baseDifferentialRankWithZero_two_le
      shift intrinsicPrime
  have hall :=
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_allValuationDifferentialRankWithZero_two_le
      shift intrinsicPrime
  exact ⟨
    hcurvature.trans hnonnormal.symm,
    hnonnormal.trans hdimension.symm,
    hbase,
    hbase.symm.trans hall⟩

/-- One positive coherent Gram at an arbitrary prime and logarithmic scale discharges the
collision-freedom premise in the full cross-prime curvature/operator/intrinsic/differential
universality chain. -/
theorem
    xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_coherentGram_posDef
    {N : ℕ} (shift : Fin N → ℕ)
    (coherentPrime curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (coherentScale curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hcoherent :
      (xiTransversePrimeValuationCoherentLogScaleGram
        shift coherentPrime coherentScale).PosDef) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift curvaturePrime operatorPrime intrinsicPrime
        curvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    shift curvaturePrime operatorPrime intrinsicPrime
    curvatureScale operatorScale hcurvatureScale hoperatorScale
    ((xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
      shift coherentPrime coherentScale).1 hcoherent)

/-- One positive-bandwidth first-valuation Gaussian Gram at an arbitrary prime discharges the
entire cross-prime universality chain, with zero retained as an ordinary separated label. -/
theorem
    xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_firstValuationGaussianGram_posDef
    {N : ℕ} (shift : Fin N → ℕ)
    (gramPrime curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth)
    (curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hGram :
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt
        shift gramPrime bandwidth).PosDef) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift curvaturePrime operatorPrime intrinsicPrime
        curvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    shift curvaturePrime operatorPrime intrinsicPrime
    curvatureScale operatorScale hcurvatureScale hoperatorScale
    ((xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
      shift gramPrime hbandwidth).1 hGram)

/-- Whole-packet independence in the HTGeometry collision matroid also discharges the complete
cross-prime Gaussian/intrinsic/differential universality chain. -/
theorem
    xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_collisionMatroid_indep
    {N : ℕ} (shift : Fin N → ℕ)
    (curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hcollision :
      (affineCollisionMatroid shift).Indep Set.univ) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift curvaturePrime operatorPrime intrinsicPrime
        curvatureScale operatorScale := by
  apply
    xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
      shift curvaturePrime operatorPrime intrinsicPrime
      curvatureScale operatorScale hcurvatureScale hoperatorScale
  have hinjOn : Set.InjOn shift Set.univ :=
    (affineCollisionMatroid_indep_iff shift Set.univ).1 hcollision
  intro i j hij
  exact hinjOn (Set.mem_univ i) (Set.mem_univ j) hij

/-- Collision sign duality at one prime proves the full equivalence chain at every independently
chosen operator and intrinsic prime. -/
theorem
    xiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase_of_collisionSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ)
    (curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift curvaturePrime operatorPrime intrinsicPrime
        curvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    shift curvaturePrime operatorPrime intrinsicPrime
    curvatureScale operatorScale hcurvatureScale hoperatorScale
    hcertificate.injective

/-- **Active cross-prime consequences of sign duality.**  A collision sign-duality certificate
forces nonnormality at every independently chosen nonnegative operator scale, intrinsic dimension
one at every prime, and both zero-augmented differential-rank thresholds. -/
theorem
    xiTransversePrimeValuationGaussian_nonnormal_intrinsicDimension_differentialRanks_of_collisionSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ)
    (curvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (curvatureScale operatorScale : ℝ)
    (hcurvatureScale : 0 ≤ curvatureScale)
    (hoperatorScale : 0 ≤ operatorScale)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale) :
    matrixSelfCommutator
        (xiTransversePrimeValuationRankOneGaussianSimilarity
          shift operatorPrime operatorScale) ≠ 0 ∧
      gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
          shift intrinsicPrime) = 1 ∧
      ((2 : ℕ∞) ≤
        (differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
            (if 0 ∈ Finset.univ.image shift then 1 else 0)) ∧
      ((2 : ℕ∞) ≤
        (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun i => xiTransverseShiftUpperEndCarrier (shift i))).eRk Set.univ +
            (if 0 ∈ Finset.univ.image shift then 1 else 0)) := by
  have htwo : 2 ≤ N := hcertificate.rankTwo hcurvatureScale
  have hdimension :
      gaussianAffineDimension
          (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
            shift intrinsicPrime) = 1 :=
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_two_le_of_injective
      shift intrinsicPrime hcertificate.injective).2 htwo
  exact ⟨
    (xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_injective
      shift operatorPrime hcertificate.injective operatorScale hoperatorScale).2 htwo,
    hdimension,
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_baseDifferentialRankWithZero_two_le
      shift intrinsicPrime).1 hdimension,
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_allValuationDifferentialRankWithZero_two_le
      shift intrinsicPrime).1 hdimension⟩

/-- **Exact intrinsic dimension.**  A collision-free transverse valuation packet with at least
two entries has affine dimension exactly one at every prime. -/
theorem
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N) :
    gaussianAffineDimension
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1 := by
  apply
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card
      shift p).2
  rw [
    Finset.card_image_of_injective _ hinjective,
    Finset.card_univ,
    Fintype.card_fin]
  exact htwo

/-- In intrinsic dimension one, the Gaussian dimension-power coordinate is exactly logarithmic
reparametrization, with no residual exponent. -/
theorem
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_log
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N) (u : ℝ) :
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p u =
      xiTransversePrimeValuationCorrectedGaussianLogScale shift p (Real.log u) := by
  unfold xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet
    xiTransversePrimeValuationCorrectedGaussianLogScale
    gaussianCorrectedDimensionPowerLogDet
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one
      shift p hinjective htwo]
  simp

/-- In intrinsic dimension one, the HilbertMetric power coordinate is the literal corrected
Gaussian log determinant at bandwidth `u > 0`. -/
theorem
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N)
    {u : ℝ} (hu : 0 < u) :
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p u =
      xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet shift p u := by
  unfold xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet
    xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet
  rw [gaussianCorrectedDimensionPowerLogDet_eq_rpow _ hu]
  rw [
    xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one
      shift p hinjective htwo]
  simp

/-- **Literal bandwidth concavity.**  A collision-free transverse valuation packet with at least
two entries has concave corrected Gaussian log determinant on every positive bandwidth. -/
theorem xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet shift p) := by
  have hx :
      Function.Injective
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) :=
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_injective_iff
      shift p).2 hinjective
  have hconcave :
      ConcaveOn ℝ (Set.Ioi 0)
        (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p) := by
    simpa [xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet] using
      (gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p)
        hx (by omega)).2
  apply hconcave.congr
  intro u hu
  exact
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
      shift p hinjective htwo hu

/-- Minimal certificate for complete intrinsic one-dimensional Gaussian geometry.  Injectivity
records collision freedom, while affine dimension one supplies nontrivial packet rank.  Coherent
Gram positivity, convexity, concavity, and coordinate-collapse laws are derived below rather than
storing an infinite family of redundant Prop data. -/
structure XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Prop where
  injective : Function.Injective shift
  affineDimensionOne :
    gaussianAffineDimension
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) = 1

namespace XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate

/-- Collision freedom supplies coherent Gram positivity at every logarithmic scale. -/
theorem coherentGramPositive
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ∀ s, (xiTransversePrimeValuationCoherentLogScaleGram shift p s).PosDef :=
  fun s =>
    (xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
      shift p s).2 hcertificate.injective

/-- Affine dimension one discharges the former explicit packet-rank field. -/
theorem rankTwo
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    2 ≤ N := by
  calc
    2 ≤ (Finset.univ.image shift).card :=
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one_iff_image_card
        shift p).1 hcertificate.affineDimensionOne
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = N := by simp

/-- The full corrected Gaussian dimension sandwich follows from the two-field certificate. -/
theorem correctedLogScaleConvex_and_dimensionPowerConcave
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ConvexOn ℝ Set.univ
        (xiTransversePrimeValuationCorrectedGaussianLogScale shift p) ∧
      ConcaveOn ℝ (Set.Ioi 0)
        (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p) := by
  have hx :
      Function.Injective
        (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p) :=
    (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_injective_iff
      shift p).2 hcertificate.injective
  have htwo : 2 ≤ N := hcertificate.rankTwo
  simpa [xiTransversePrimeValuationCorrectedGaussianLogScale,
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet] using
    (gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration shift p)
      hx (by omega))

/-- Corrected logarithmic metric scale is convex, derived from the two-field certificate. -/
theorem correctedLogScaleConvex
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ConvexOn ℝ Set.univ
      (xiTransversePrimeValuationCorrectedGaussianLogScale shift p) :=
  hcertificate.correctedLogScaleConvex_and_dimensionPowerConcave.1

/-- Corrected affine-dimension power scale is concave, with rank discharged internally. -/
theorem correctedDimensionPowerConcave
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p) :=
  hcertificate.correctedLogScaleConvex_and_dimensionPowerConcave.2

/-- Literal positive-bandwidth concavity follows from the minimal intrinsic certificate. -/
theorem correctedBandwidthLogDetConcave
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet shift p) :=
  xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
    shift p hcertificate.injective hcertificate.rankTwo

/-- The dimension-power coordinate collapses to literal bandwidth on the positive half-line. -/
theorem dimensionPowerBandwidthCollapse
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    Set.EqOn
      (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p)
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet shift p)
      (Set.Ioi 0) :=
  fun _ hu =>
    xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
      shift p hcertificate.injective hcertificate.rankTwo hu

/-- The dimension-power coordinate globally collapses to logarithmic reparametrization. -/
theorem dimensionPowerCollapse
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes}
    (hcertificate :
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p) :
    ∀ u,
      xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet shift p u =
        xiTransversePrimeValuationCorrectedGaussianLogScale shift p (Real.log u) :=
  xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_log
    shift p hcertificate.injective hcertificate.rankTwo

end XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate

/-- **Exact intrinsic-dimension phase law.**  Collision freedom and packet rank two are exactly
the phase of positive coherent geometry, intrinsic dimension one, and the corrected Gaussian
dimension sandwich. -/
theorem
    xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (Function.Injective shift ∧ 2 ≤ N) ↔
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p := by
  constructor
  · rintro ⟨hinjective, htwo⟩
    exact {
      injective := hinjective
      affineDimensionOne :=
        xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one
          shift p hinjective htwo }
  · intro hcertificate
    exact ⟨hcertificate.injective, hcertificate.rankTwo⟩

/-- **Curvature/intrinsic-dimension connector.**  At every nonnegative curvature scale, collision
sign duality at one prime is exactly the intrinsic one-dimensional Gaussian sandwich at any other
prime. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_intrinsicDimensionCertificate
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime intrinsicPrime : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime t ↔
      XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
        shift intrinsicPrime :=
  (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
    shift curvaturePrime t ht).symm.trans
      (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
        shift intrinsicPrime)

/-- Reconstruction sign duality factors exactly into cofinite reconstruction and the intrinsic
one-dimensional Gaussian dimension sandwich. -/
theorem
    xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_intrinsicDimensionCertificate
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ)
    (curvaturePrime intrinsicPrime : Nat.Primes) (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m curvaturePrime t ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
          shift intrinsicPrime := by
  calc
    _ ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
          XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
            shift curvaturePrime t :=
      xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_collisionCertificate
        shift m curvaturePrime t
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_intrinsicDimensionCertificate
          shift curvaturePrime intrinsicPrime t ht)

/-- **Prime-universal intrinsic-dimension law.**  Collision freedom and packet rank two are
equivalent to intrinsic one-dimensional Gaussian geometry at every prime. -/
theorem
    xiTransversePrimeShift_injective_and_two_le_iff_every_gaussianIntrinsicDimensionCertificate
    {N : ℕ} (shift : Fin N → ℕ) :
    (Function.Injective shift ∧ 2 ≤ N) ↔
      ∀ p : Nat.Primes,
        XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate shift p := by
  constructor
  · intro hcondition p
    exact
      (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
        shift p).1 hcondition
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    exact
      (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
        shift p).2 (hall p)

/-- Collision-only Gaussian sign duality forces literal positive-bandwidth concavity of the
intrinsic corrected determinant, independently of the prime used for the two geometries. -/
theorem
    xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_collisionSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime intrinsicPrime : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime t) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet
        shift intrinsicPrime) :=
  ((xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_intrinsicDimensionCertificate
    shift curvaturePrime intrinsicPrime t ht).1 hcertificate).correctedBandwidthLogDetConcave

/-- Full reconstruction sign duality also forces literal corrected-determinant bandwidth
concavity at every independently chosen intrinsic prime. -/
theorem
    xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ)
    (curvaturePrime intrinsicPrime : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t)
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m curvaturePrime t) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet
        shift intrinsicPrime) := by
  apply
    xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_collisionSignDuality
      shift curvaturePrime intrinsicPrime t ht
  exact
    (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_collisionCertificate
      shift m curvaturePrime t).1 hcertificate |>.2

/-- Collision freedom and packet rank two give literal corrected-determinant bandwidth concavity
simultaneously at every prime. -/
theorem
    xiTransversePrimeShift_correctedGaussianBandwidthLogDet_concaveOn_every_prime
    {N : ℕ} (shift : Fin N → ℕ)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N) :
    ∀ p : Nat.Primes,
      ConcaveOn ℝ (Set.Ioi 0)
        (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet shift p) :=
  fun p =>
    xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
      shift p hinjective htwo

end

end RHTower
