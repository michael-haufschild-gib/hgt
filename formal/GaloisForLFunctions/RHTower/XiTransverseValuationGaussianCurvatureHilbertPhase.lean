import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianRadicalConnector

/-!
# Transverse Xi valuation Gaussian curvature and exact Hilbert recovery

The first transverse valuation increment embeds every integral Xi shift into one real Hilbert
coordinate.  Existing cofinite prime-jet reconstruction is exactly injectivity together with
exclusion of the zero shift, so it discharges the abstract injective-background premise in the
HilbertMetric rank-one Gaussian curvature law.

Appending the integral shift itself as one metric feature gives a globally concave Gaussian
log-volume.  Inside the exact reconstruction phase its curvature is flat precisely for packets of
size at most one and strictly negative precisely from size two onward.  Thus deletion-robust
coefficient recovery, completed Szegő positivity, differential independence, and strict metric
curvature form one exact phase.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped ComplexOrder Differential

local instance xiValuationCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiValuationCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiValuationCurvatureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiValuationCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiValuationCurvatureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiValuationCurvatureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiValuationCurvatureAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiValuationCurvatureAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Gaussian metric path obtained by appending the actual integral shift to its first transverse
valuation coordinate. -/
def xiTransversePrimeValuationRankOneGaussianMetricGram
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  gaussianMetricRankOneExtensionGram
    (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
    (fun j => (shift j : ℝ)) t

/-- Square-root similarity whose self-commutator measures transverse valuation Gaussian
curvature. -/
def xiTransversePrimeValuationRankOneGaussianSimilarity
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  matrixSqrtSimilarity
    (rankOneSchurExponentialPath
      (finiteGaussianDistanceGram
        (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) 1)
      (fun j => (shift j : ℝ)) (2 * t))
    (rankOneLabelDiagonal (fun j => (shift j : ℝ)))

/-- Exact cofinite reconstruction supplies the injective Euclidean background required by the
Gaussian curvature law. -/
theorem
    xiTransversePrimeFirstValuationGaussianFeature_injective_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m) :
    Function.Injective
      (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) :=
  (xiTransversePrimeFirstValuationGaussianFeature_injective p).comp
    ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
      shift m).1 hrec).1

/-- **Exact reconstruction/commutator curvature identity.**  Cofinite Hilbert reconstruction
discharges the only injectivity premise in the universal HilbertMetric identity: transverse
Gaussian curvature is exactly minus twice the self-commutator energy. -/
theorem
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_selfCommutatorEnergy_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t =
      -2 * matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t)) := by
  change deriv (deriv (fun s =>
    Real.log
      (gaussianMetricRankOneExtensionGram
        (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
        (fun j => (shift j : ℝ)) s).det)) t = _
  change _ =
    -2 * matrixHilbertSchmidtEnergy
      (matrixSelfCommutator
        (matrixSqrtSimilarity
          (rankOneSchurExponentialPath
            (finiteGaussianDistanceGram
              (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) 1)
            (fun j => (shift j : ℝ)) (2 * t))
          (rankOneLabelDiagonal (fun j => (shift j : ℝ)))))
  exact gaussianMetricRankOneExtension_logDet_secondDerivative_eq
    (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
    (fun j => (shift j : ℝ))
    (xiTransversePrimeFirstValuationGaussianFeature_injective_of_cofiniteHilbertReconstruction
      shift m p hrec)
    t ht

/-- For an injective integral shift packet, its real-valued shift feature is constant exactly
when the packet has at most one element. -/
theorem xiTransversePrimeShift_cast_constant_iff_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (hinjective : Function.Injective shift) :
    (∀ i j : Fin N, (shift i : ℝ) = (shift j : ℝ)) ↔ N ≤ 1 := by
  constructor
  · intro hconstant
    by_contra hN
    have htwo : 2 ≤ N := by omega
    let i : Fin N := ⟨0, by omega⟩
    let j : Fin N := ⟨1, by omega⟩
    have hshift : shift i = shift j := by
      exact_mod_cast hconstant i j
    have hij := hinjective hshift
    have hval := congrArg Fin.val hij
    simp [i, j] at hval
  · intro hN i j
    have hij : i = j := Fin.ext (by omega)
    exact congrArg (fun k : Fin N => (shift k : ℝ)) hij

/-- **Reconstruction-discharge flatness law.**  Once exact cofinite prime-jet recovery is known,
Gaussian log-volume curvature vanishes exactly for empty and singleton shift packets. -/
theorem
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t = 0 ↔
      N ≤ 1 := by
  have hcondition :=
    (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
      shift m).1 hrec
  change deriv (deriv (fun s =>
    Real.log
      (gaussianMetricRankOneExtensionGram
        (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
        (fun j => (shift j : ℝ)) s).det)) t = 0 ↔ N ≤ 1
  rw [gaussianMetricRankOneExtension_logDet_secondDerivative_eq_zero_iff_constant
    (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
    (fun j => (shift j : ℝ))
    (xiTransversePrimeFirstValuationGaussianFeature_injective_of_cofiniteHilbertReconstruction
      shift m p hrec)
    t ht]
  exact xiTransversePrimeShift_cast_constant_iff_of_injective shift hcondition.1

/-- Flat transverse Gaussian curvature is exactly real normality of its square-root similarity. -/
theorem
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_normal_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t = 0 ↔
      matrixSelfCommutator
        (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) = 0 := by
  have hcurvature :=
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_selfCommutatorEnergy_of_cofiniteHilbertReconstruction
      shift m p hrec t ht
  constructor
  · intro hflat
    have henergy :
        matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t)) = 0 := by
      rw [hcurvature] at hflat
      linarith
    exact (matrixHilbertSchmidtEnergy_eq_zero_iff _).1 henergy
  · intro hnormal
    rw [hcurvature, hnormal]
    simp [matrixHilbertSchmidtEnergy]

/-- **Reconstruction-discharge normality classification.**  The transverse valuation Gaussian
similarity is normal exactly for empty and singleton shift packets. -/
theorem
    xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_eq_zero_iff_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator
        (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) = 0 ↔
      N ≤ 1 := by
  rw [←
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_normal_of_cofiniteHilbertReconstruction
      shift m p hrec t ht]
  exact
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_of_cofiniteHilbertReconstruction
      shift m p hrec t ht

/-- The transverse valuation Gaussian similarity is nonnormal exactly from packet rank two
onward. -/
theorem
    xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator
        (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ≠ 0 ↔
      2 ≤ N := by
  rw [ne_eq,
    xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_eq_zero_iff_of_cofiniteHilbertReconstruction
      shift m p hrec t ht]
  omega

/-- **Reconstruction-discharge strict-curvature law.**  Inside the exact cofinite Hilbert phase,
Gaussian log-volume curvature is strictly negative exactly from packet rank two onward. -/
theorem
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t < 0 ↔
      2 ≤ N := by
  have hcondition :=
    (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
      shift m).1 hrec
  constructor
  · intro hnegative
    by_contra hN
    have hNle : N ≤ 1 := by omega
    have hzero :=
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).2 hNle
    linarith
  · intro htwo
    let i : Fin N := ⟨0, by omega⟩
    let j : Fin N := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i, j] at hval
    have hshift : shift i ≠ shift j := fun h => hij (hcondition.1 h)
    change deriv (deriv (fun s =>
      Real.log
        (gaussianMetricRankOneExtensionGram
          (fun k => xiTransversePrimeFirstValuationGaussianFeature (shift k) p)
          (fun k => (shift k : ℝ)) s).det)) t < 0
    apply gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero
      (fun k => xiTransversePrimeFirstValuationGaussianFeature (shift k) p)
      (fun k => (shift k : ℝ))
      (xiTransversePrimeFirstValuationGaussianFeature_injective_of_cofiniteHilbertReconstruction
        shift m p hrec)
      t ht
    exact ⟨i, j, fun hcast => hshift (by exact_mod_cast hcast)⟩

/-- Strict transverse Gaussian curvature is exactly nonnormality of the reconstruction-induced
square-root similarity. -/
theorem
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_nonnormal_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t < 0 ↔
      matrixSelfCommutator
        (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ≠ 0 := by
  rw [
    xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
      shift m p hrec t ht,
    xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_cofiniteHilbertReconstruction
      shift m p hrec t ht]

/-- Exact cofinite recovery makes the transverse valuation Gaussian log-volume globally concave
on the complete nonnegative metric ray. -/
theorem xiTransversePrimeValuationRankOneGaussianMetric_logDet_concaveOn_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m) :
    ConcaveOn ℝ (Set.Ici 0) (fun t =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p t).det) := by
  simpa only [xiTransversePrimeValuationRankOneGaussianMetricGram] using
    gaussianMetricRankOneExtension_logDet_concaveOn
      (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p)
      (fun j => (shift j : ℝ))
      (xiTransversePrimeFirstValuationGaussianFeature_injective_of_cofiniteHilbertReconstruction
        shift m p hrec)

/-- Exact cofinite recovery together with strict transverse Gaussian metric curvature. -/
def XiTransversePrimeJetApertureGaussianCurvaturePhase
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) (t : ℝ) : Prop :=
  XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t < 0

/-- **Exact cofinite-Hilbert/Gaussian-curvature phase law.**  The joint phase is precisely exact
cofinite reconstruction of a packet containing at least two shifts. -/
theorem xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        2 ≤ N := by
  constructor
  · rintro ⟨hrec, hcurvature⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).1 hcurvature⟩
  · rintro ⟨hrec, htwo⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).2 htwo⟩

/-- **Exact reconstruction/operator-normality phase law.**  The strict-curvature phase is
equivalently cofinite Hilbert reconstruction together with nonnormality of the induced
square-root similarity. -/
theorem xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_nonnormal
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ≠ 0 := by
  constructor
  · rintro ⟨hrec, hcurvature⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_nonnormal_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).1 hcurvature⟩
  · rintro ⟨hrec, hnonnormal⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_nonnormal_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).2 hnonnormal⟩

/-- **Differential-matroid/operator-normality connector.**  Strict transverse Gaussian
curvature is exactly all-valuation differential independence together with nonnormality of the
reconstruction-induced square-root similarity. -/
theorem
    xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_differentialIndependent_and_nonnormal
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ∧
        matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ≠ 0 :=
  (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_nonnormal
    shift m p t ht).trans
      (and_congr
        (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_cofiniteApertureHilbertReconstruction
          shift m).symm
        Iff.rfl)

/-- **Completed-Szegő/operator-normality connector.**  The strict transverse Gaussian phase is
equivalently positivity of the completed one-prime valuation metric together with nonnormality
of the associated square-root similarity. -/
theorem
    xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_completedSzegoGram_posDef_and_nonnormal
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ∧
        matrixSelfCommutator
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ≠ 0 :=
  (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_nonnormal
    shift m p t ht).trans
      (and_congr
        (xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureHilbertReconstruction
          shift m p).symm
        Iff.rfl)

/-- The complementary reconstructed flat phase consists exactly of empty and singleton packets. -/
theorem
    cofiniteHilbertReconstruction_and_gaussianCurvature_eq_zero_iff_reconstruction_and_le_one
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        deriv (deriv (fun s =>
          Real.log
            (xiTransversePrimeValuationRankOneGaussianMetricGram shift p s).det)) t = 0) ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        N ≤ 1 := by
  constructor
  · rintro ⟨hrec, hflat⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).1 hflat⟩
  · rintro ⟨hrec, hsmall⟩
    exact ⟨hrec,
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_eq_zero_iff_of_cofiniteHilbertReconstruction
        shift m p hrec t ht).2 hsmall⟩

/-- **Analytic-matroid/metric-curvature connector.**  Strict Gaussian curvature with exact
recovery is exactly differential independence over all scalar valuation layers for a packet of
size at least two. -/
theorem xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_differentialIndependent_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ∧
        2 ≤ N :=
  (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
    shift m p t ht).trans
      (and_congr
        (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_cofiniteApertureHilbertReconstruction
          shift m).symm
        Iff.rfl)

/-- **Completed-Szegő/metric-curvature connector.**  The same strict-curvature phase is exactly
strict positivity of the completed one-prime valuation metric for a packet of size at least two. -/
theorem xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_completedSzegoGram_posDef_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ∧
        2 ≤ N :=
  (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
    shift m p t ht).trans
      (and_congr
        (xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureHilbertReconstruction
          shift m p).symm
        Iff.rfl)

end

end RHTower
