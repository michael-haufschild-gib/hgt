import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import GaloisForLFunctions.RHTower.XiTransverseGaussianDifferentialMatroidConnector
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Transverse Xi Gaussian curvature sign duality

The first transverse valuation coordinate of an integral Xi shift packet supports two different
Gaussian geometries.  Appending the shift label to the Gaussian distance Gram gives the existing
rank-one extension, whose log-determinant curvature is strictly negative from packet rank two
onward.  Treating the same valuation coordinate as a coherent-state configuration gives a
logarithmic-scale Gram whose curvature is a CCR number variance and is therefore nonnegative.

Collision freedom alone supplies every hypothesis in both HilbertMetric theories, while exact
cofinite prime-jet reconstruction adds only zero-exclusion.  This file records the exact
mean/variance identities, global coherent positivity and curvature bounds, the collision-only
sign phase, and its precise factorization from reconstruction without adding an analytic
assumption.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped ComplexOrder Differential Matroid

open scoped UpperEndDifferentialInstances

/-- One-dimensional coherent configuration supplied by the first transverse valuation
coordinate of each integral Xi shift. -/
def xiTransversePrimeFirstValuationCoherentConfiguration
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Fin N → Fin 1 → ℝ :=
  fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p

/-- Coherent Gaussian Gram of the first transverse valuation coordinates along logarithmic
metric scale. -/
def xiTransversePrimeValuationCoherentLogScaleGram
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  gaussianCoherentLogScaleGram
    (xiTransversePrimeFirstValuationCoherentConfiguration shift p) s

/-- The coherent configuration remembers exactly the shift-collision relation; zero remains an
ordinary separated label. -/
theorem xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Function.Injective
        (xiTransversePrimeFirstValuationCoherentConfiguration shift p) ↔
      Function.Injective shift := by
  constructor
  · intro hconfiguration i j hij
    apply hconfiguration
    simp [xiTransversePrimeFirstValuationCoherentConfiguration, hij]
  · intro hshift
    exact (xiTransversePrimeFirstValuationGaussianFeature_injective p).comp hshift

/-- **Exact coherent Gaussian radical classification.**  At every logarithmic scale, strict
positivity of the coherent first-valuation Gram detects precisely shift collisions and imposes no
nonzero-label condition. -/
theorem xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (s : ℝ) :
    (xiTransversePrimeValuationCoherentLogScaleGram shift p s).PosDef ↔
      Function.Injective shift := by
  let y := xiTransversePrimeFirstValuationCoherentConfiguration shift p
  let z := gaussianLogScaleRescaledConfiguration y s
  have hGram :
      xiTransversePrimeValuationCoherentLogScaleGram shift p s =
        gaussianCoherentGram z := by
    change gaussianCoherentLogScaleGram y s = gaussianCoherentGram z
    simpa [z] using (gaussianCoherentLogScaleGram_rescaled y s 0).symm
  rw [hGram, gaussianCoherentGram_posDef_iff_injective]
  constructor
  · intro hz
    apply (xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
      shift p).1
    intro i j hij
    apply hz
    have hyij : y i = y j := by
      simpa [y] using hij
    funext a
    exact congrArg (fun v : Fin 1 → ℝ =>
      Real.sqrt (Real.exp s) * v a) hyij
  · intro hshift
    exact gaussianLogScaleRescaledConfiguration_injective y
      ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
        shift p).2 hshift)
      s

/-- **Distance/coherent Gaussian radical connector.**  Positive-bandwidth distance Grams and
coherent log-scale Grams at arbitrary primes and scales have exactly the same collision radical. -/
theorem
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_coherentLogScaleGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (distancePrime coherentPrime : Nat.Primes)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth) (s : ℝ) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt
        shift distancePrime bandwidth).PosDef ↔
      (xiTransversePrimeValuationCoherentLogScaleGram
        shift coherentPrime s).PosDef :=
  (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
    shift distancePrime hbandwidth).trans
      (xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
        shift coherentPrime s).symm

/-- Cofinite Xi reconstruction discharges injectivity of the coherent-state configuration. -/
theorem
    xiTransversePrimeFirstValuationCoherentConfiguration_injective_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m) :
    Function.Injective
      (xiTransversePrimeFirstValuationCoherentConfiguration shift p) := by
  exact (xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
    shift p).2
      ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift m).1 hrec).1

/-- Collision freedom alone, without nonzero labels or a reconstruction interface, suffices for
the exact coherent CCR mean identity. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) :
    deriv (fun s => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p s).det) 0 =
      ccrMeanEnergy
        (gaussianCoherentCompression
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p)) := by
  exact gaussianCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy
    (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
    ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
      shift p).2 hinjective)

/-- Collision freedom alone also gives the exact CCR variance identity. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) :
    deriv (deriv (fun s => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p s).det)) 0 =
      ccrNumberVariance
        (gaussianCoherentCompression
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p))
        (gaussianCoherentInjectiveLeakage
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
          ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
            shift p).2 hinjective)) := by
  exact gaussianCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance
    (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
    ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
      shift p).2 hinjective)

/-- Coherent valuation curvature is globally nonnegative on the minimal collision-free phase. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_nonneg_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (s : ℝ) :
    0 ≤ deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s := by
  exact gaussianCoherentLogScale_logDet_secondDerivative_nonneg_at
    (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
    ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
      shift p).2 hinjective)
    s

/-- The dimension-one coherent curvature upper bound also needs only collision freedom. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_le_derivative_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (s : ℝ) :
    deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s ≤
      deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det) s := by
  simpa [xiTransversePrimeValuationCoherentLogScaleGram] using
    gaussianCoherentLogScale_logDet_secondDerivative_le_dim_mul_derivative_at
      (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
      ((xiTransversePrimeFirstValuationCoherentConfiguration_injective_iff
        shift p).2 hinjective)
      s

/-- Exact reconstruction makes the coherent valuation Gram strictly positive at every
logarithmic scale. -/
theorem
    xiTransversePrimeValuationCoherentLogScaleGram_posDef_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (s : ℝ) :
    (xiTransversePrimeValuationCoherentLogScaleGram shift p s).PosDef := by
  exact
    (xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
      shift p s).2
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1

/-- The unit-scale coherent log-slope is exactly the CCR mean energy of the reconstructed
valuation configuration. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m) :
    deriv (fun s => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p s).det) 0 =
      ccrMeanEnergy
        (gaussianCoherentCompression
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p)) := by
  exact
    xiTransversePrimeValuationCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy_of_injective
      shift p
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1

/-- The unit-scale coherent log-curvature is exactly its canonical CCR number variance. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m) :
    deriv (deriv (fun s => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p s).det)) 0 =
      ccrNumberVariance
        (gaussianCoherentCompression
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p))
        (gaussianCoherentInjectiveLeakage
          (xiTransversePrimeFirstValuationCoherentConfiguration shift p)
          (xiTransversePrimeFirstValuationCoherentConfiguration_injective_of_cofiniteHilbertReconstruction
            shift m p hrec)) := by
  exact
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance_of_injective
      shift p
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1

/-- Reconstructed coherent valuation log-curvature is nonnegative at every logarithmic scale. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_nonneg_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (s : ℝ) :
    0 ≤ deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s := by
  exact
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_nonneg_of_injective
      shift p
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1
      s

/-- In coherent dimension one, reconstructed log-curvature is bounded above by log-slope at every
scale. -/
theorem
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_le_derivative_of_cofiniteHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (s : ℝ) :
    deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s ≤
      deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det) s := by
  exact
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_le_derivative_of_injective
      shift p
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1
      s

/-- Every collision-free rank-two Xi packet exhibits opposite curvature signs in the
distance-extension and coherent-state Gaussian geometries. -/
theorem
    xiTransversePrimeValuationGaussianMetric_strictNegative_and_coherentLogScale_nonnegative_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (htwo : 2 ≤ N)
    (t : ℝ) (ht : 0 ≤ t) (s : ℝ) :
    deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p u).det)) t < 0 ∧
      0 ≤ deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s := by
  exact ⟨
    (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_injective
      shift p hinjective t ht).2 htwo,
    xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_nonneg_of_injective
      shift p hinjective s⟩

/-- Reconstructed rank-two Xi packets exhibit opposite curvature signs in the distance-extension
and coherent-state Gaussian geometries. -/
theorem
    xiTransversePrimeValuationGaussianMetric_strictNegative_and_coherentLogScale_nonnegative
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (hrec : XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m)
    (htwo : 2 ≤ N) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) :
    deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram shift p u).det)) t < 0 ∧
      0 ≤ deriv (deriv (fun u => Real.log
        (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s := by
  exact
    xiTransversePrimeValuationGaussianMetric_strictNegative_and_coherentLogScale_nonnegative_of_injective
      shift p
        ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
          shift m).1 hrec).1
      htwo t ht s

/-- Minimal collision-only certificate for Gaussian sign duality.  Strict negative distance
curvature records nontrivial rank, while injectivity records collision freedom.  Coherent Gram
positivity and global coherent-curvature inequalities are derived below instead of storing an
infinite family of redundant Prop data.  Unlike exact reconstruction, this phase permits zero as
a shift label. -/
structure XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) : Prop where
  injective : Function.Injective shift
  rankOneLogDetCurvatureNegative :
    deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationRankOneGaussianMetricGram shift p u).det)) t < 0

namespace XiTransversePrimeValuationGaussianCollisionSignDualityCertificate

/-- Collision freedom supplies coherent Gram positivity at every logarithmic scale. -/
theorem coherentGramPositive
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t) :
    ∀ s, (xiTransversePrimeValuationCoherentLogScaleGram shift p s).PosDef :=
  fun s =>
    (xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
      shift p s).2 hcertificate.injective

/-- Nonnegative coherent log-determinant curvature is forced by coherent positivity. -/
theorem coherentLogDetCurvatureNonnegative
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t) :
    ∀ s, 0 ≤ deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s :=
  xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_nonneg_of_injective
    shift p hcertificate.injective

/-- The coherent curvature upper bound by its slope is likewise forced by collision freedom. -/
theorem coherentLogDetCurvatureLeSlope
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t) :
    ∀ s,
      deriv (deriv (fun u => Real.log
          (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s ≤
        deriv (fun u => Real.log
          (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det) s :=
  xiTransversePrimeValuationCoherentLogScale_logDet_secondDerivative_le_derivative_of_injective
    shift p hcertificate.injective

/-- At nonnegative distance scale, strict negative curvature discharges packet rank at least
two. -/
theorem rankTwo
    {N : ℕ} {shift : Fin N → ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t)
    (ht : 0 ≤ t) :
    2 ≤ N :=
  (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_injective
    shift p hcertificate.injective t ht).1
      hcertificate.rankOneLogDetCurvatureNegative

end XiTransversePrimeValuationGaussianCollisionSignDualityCertificate

/-- **Exact collision-only Xi Gaussian sign-duality phase law.**  At nonnegative distance scale,
the simultaneous strict-negative distance curvature and positive coherent geometry detect exactly
collision freedom and packet rank at least two; no nonzero or reconstruction condition survives. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (Function.Injective shift ∧ 2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift p t := by
  constructor
  · rintro ⟨hinjective, htwo⟩
    exact {
      injective := hinjective
      rankOneLogDetCurvatureNegative :=
        (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_injective
          shift p hinjective t ht).2 htwo }
  · intro hcertificate
    exact ⟨hcertificate.injective, hcertificate.rankTwo ht⟩

/-- **HTGeometry collision-matroid classification of sign duality.**  The geometric phase is
exactly whole-packet independence in the affine collision matroid together with packet rank at
least two. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_collisionMatroid_indep_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t ↔
      (affineCollisionMatroid shift).Indep Set.univ ∧ 2 ≤ N := by
  constructor
  · intro hcertificate
    have hcondition :=
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).2 hcertificate
    refine ⟨?_, hcondition.2⟩
    rw [affineCollisionMatroid_indep_iff]
    intro i _ j _ hij
    exact hcondition.1 hij
  · rintro ⟨hindependent, htwo⟩
    apply
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).1
    refine ⟨?_, htwo⟩
    intro i j hij
    exact
      ((affineCollisionMatroid_indep_iff shift Set.univ).1
        hindependent) trivial trivial hij

/-- **Principal-Gram/curvature connector.**  At any independently chosen prime and positive
bandwidth, positivity of the whole Gaussian principal matrix together with packet rank two is
exactly the collision-only sign-duality phase. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_principalGram_posDef_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime gramPrime : Nat.Primes)
    (curvatureScale : ℝ) (hcurvatureScale : 0 ≤ curvatureScale)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale ↔
      (xiTransversePrimeFirstValuationGaussianPrincipalGramMatrix
        shift gramPrime bandwidth Finset.univ).PosDef ∧
        2 ≤ N := by
  constructor
  · intro hcertificate
    have hphase :=
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_collisionMatroid_indep_and_two_le
        shift curvaturePrime curvatureScale hcurvatureScale).1 hcertificate
    refine ⟨?_, hphase.2⟩
    apply
      (xiTransverseGaussianCollisionMatroid_indep_iff_principalGram_posDef
        shift gramPrime hbandwidth Finset.univ).1
    simpa using hphase.1
  · rintro ⟨hGram, htwo⟩
    apply
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_collisionMatroid_indep_and_two_le
        shift curvaturePrime curvatureScale hcurvatureScale).2
    refine ⟨?_, htwo⟩
    have hindependent :=
      (xiTransverseGaussianCollisionMatroid_indep_iff_principalGram_posDef
        shift gramPrime hbandwidth Finset.univ).2 hGram
    simpa using hindependent

/-- **Zero-loop discharge inside the metric phase.**  Once collision sign duality holds,
differential independence over all scalar valuation layers is equivalent to the sole remaining
condition that zero is absent from the shift packet. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_ne_zero_of_gaussianCollisionSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      ∀ j, shift j ≠ 0 := by
  have hinjective :=
    ((xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
      shift p t ht).2 hcertificate).1
  rw [
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_firstValuationGaussian_posDef_and_ne_zero]
  exact and_iff_right
    ((xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective
      shift p).2 hinjective)

/-- **Differential/metric phase connector.**  Collision sign duality plus zero-exclusion is
exactly all-valuation differential independence for a packet of rank at least two. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_and_ne_zero_iff_allValuation_differentialIndependent_and_two_le
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t ∧
        ∀ j, shift j ≠ 0) ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ∧
        2 ≤ N := by
  constructor
  · rintro ⟨hcertificate, hne⟩
    have hcondition :=
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).2 hcertificate
    exact ⟨
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_ne_zero_of_gaussianCollisionSignDualityCertificate
        shift p t ht hcertificate).2 hne,
      hcondition.2⟩
  · rintro ⟨hindependent, htwo⟩
    have hgaussian :=
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_firstValuationGaussian_posDef_and_ne_zero
        shift p).1 hindependent
    have hinjective :=
      (xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective
        shift p).1 hgaussian.1
    exact ⟨
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).1 ⟨hinjective, htwo⟩,
      hgaussian.2⟩

/-- **Sign-duality rank fracture.**  At every independently chosen positive Gaussian bandwidth,
collision sign duality forces literal Gaussian rank `N`; rational-base and all-valuation
differential ranks agree, and their only deficit is the exact zero-loop indicator. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_rank_fracture
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime rankPrime : Nat.Primes)
    (curvatureScale : ℝ) (hcurvatureScale : 0 ≤ curvatureScale)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt
        shift rankPrime bandwidth).rank = N ∧
      (differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ =
        (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ ∧
      (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ +
          (if 0 ∈ Finset.univ.image shift then 1 else 0) =
        (N : ℕ∞) := by
  have hinjective :=
    ((xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
      shift curvaturePrime curvatureScale hcurvatureScale).2 hcertificate).1
  have hGram :
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt
        shift rankPrime bandwidth).rank = N := by
    rw [
      xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_image_card
        shift rankPrime hbandwidth,
      Finset.card_image_of_injective _ hinjective,
      Finset.card_univ,
      Fintype.card_fin]
  refine ⟨hGram,
    xiTransverseShiftUpperEndCarrier_differentialRank_base_eq_allValuation
      shift Set.univ,
    ?_⟩
  rw [←
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_allValuationDifferential_eRk_add_zero
      shift rankPrime hbandwidth]
  exact_mod_cast hGram

/-- In the zero-free collision sign-duality phase, both differential bases have full rank `N`. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_differentialRank_eq_card_of_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime rankPrime : Nat.Primes)
    (curvatureScale : ℝ) (hcurvatureScale : 0 ≤ curvatureScale)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale)
    (hne : ∀ j, shift j ≠ 0) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ =
        (N : ℕ∞) ∧
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ =
        (N : ℕ∞) := by
  have hrank :=
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_rank_fracture
      shift curvaturePrime rankPrime curvatureScale hcurvatureScale
        hbandwidth hcertificate
  have hzero : 0 ∉ Finset.univ.image shift := by
    intro hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    exact hne j hj
  have hall :
      (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ =
        (N : ℕ∞) := by
    simpa [hzero] using hrank.2.2
  exact ⟨hrank.2.1.trans hall, hall⟩

/-- If zero occurs in the collision sign-duality phase, it is the unique differential loop and
both differential ranks are exactly one below the Gaussian rank, expressed without subtraction. -/
theorem
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_differentialRank_add_one_eq_card_of_zero
    {N : ℕ} (shift : Fin N → ℕ) (curvaturePrime rankPrime : Nat.Primes)
    (curvatureScale : ℝ) (hcurvatureScale : 0 ≤ curvatureScale)
    {bandwidth : ℝ} (hbandwidth : 0 < bandwidth)
    (hcertificate :
      XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
        shift curvaturePrime curvatureScale)
    (hzero : ∃ j, shift j = 0) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ + 1 =
        (N : ℕ∞) ∧
      (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ + 1 =
        (N : ℕ∞) := by
  have hrank :=
    xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_rank_fracture
      shift curvaturePrime rankPrime curvatureScale hcurvatureScale
        hbandwidth hcertificate
  have hmem : 0 ∈ Finset.univ.image shift := by
    obtain ⟨j, hj⟩ := hzero
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
  have hall :
      (differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (fun j => xiTransverseShiftUpperEndCarrier (shift j))).eRk Set.univ + 1 =
        (N : ℕ∞) := by
    simpa [hmem] using hrank.2.2
  exact ⟨by simpa [hrank.2.1] using hall, hall⟩

/-- Minimal reconstruction certificate for Gaussian sign duality.  Cofinite reconstruction
already forces collision freedom and hence all coherent Gaussian geometry; only strict negative
distance curvature remains independent. -/
structure XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) (t : ℝ) : Prop where
  cofiniteReconstruction :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m
  rankOneLogDetCurvatureNegative :
    deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationRankOneGaussianMetricGram shift p u).det)) t < 0

namespace XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate

/-- Reconstruction discharges collision freedom. -/
theorem injective
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t) :
    Function.Injective shift :=
  ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
    shift m).1 hcertificate.cofiniteReconstruction).1

/-- Reconstruction supplies coherent Gram positivity at every logarithmic scale. -/
theorem coherentGramPositive
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t) :
    ∀ s, (xiTransversePrimeValuationCoherentLogScaleGram shift p s).PosDef :=
  fun s =>
    (xiTransversePrimeValuationCoherentLogScaleGram_posDef_iff_injective
      shift p s).2 hcertificate.injective

/-- Forgetting reconstruction yields the minimal collision-only sign-duality certificate. -/
theorem collisionCertificate
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate shift p t where
  injective := hcertificate.injective
  rankOneLogDetCurvatureNegative :=
    hcertificate.rankOneLogDetCurvatureNegative

/-- Coherent log-determinant curvature is nonnegative, derived rather than stored. -/
theorem coherentLogDetCurvatureNonnegative
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t) :
    ∀ s, 0 ≤ deriv (deriv (fun u => Real.log
      (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s :=
  hcertificate.collisionCertificate.coherentLogDetCurvatureNonnegative

/-- Coherent curvature is bounded by its slope, derived rather than stored. -/
theorem coherentLogDetCurvatureLeSlope
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t) :
    ∀ s,
      deriv (deriv (fun u => Real.log
          (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det)) s ≤
        deriv (fun u => Real.log
          (xiTransversePrimeValuationCoherentLogScaleGram shift p u).det) s :=
  hcertificate.collisionCertificate.coherentLogDetCurvatureLeSlope

/-- At nonnegative distance scale, reconstruction sign duality discharges packet rank two. -/
theorem rankTwo
    {N : ℕ} {shift : Fin N → ℕ} {m : ℕ} {p : Nat.Primes} {t : ℝ}
    (hcertificate :
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t)
    (ht : 0 ≤ t) :
    2 ≤ N :=
  hcertificate.collisionCertificate.rankTwo ht

end XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate

/-- **Curvature-phase interface discharge.**  The cofinite Gaussian-curvature phase and the
reconstruction sign-duality certificate contain exactly the same reconstruction and strict
curvature data.  Their equivalence is unconditional in the metric scale. -/
theorem
    xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase shift m p t ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m p t := by
  constructor
  · rintro ⟨hreconstruction, hcurvature⟩
    exact {
      cofiniteReconstruction := hreconstruction
      rankOneLogDetCurvatureNegative := hcurvature }
  · intro hcertificate
    exact ⟨hcertificate.cofiniteReconstruction,
      hcertificate.rankOneLogDetCurvatureNegative⟩

/-- **Reconstruction/metric phase separation.**  The original reconstruction certificate is
exactly cofinite reconstruction together with the collision-only Gaussian sign-duality
certificate.  Thus zero-exclusion belongs solely to the reconstruction factor. -/
theorem
    xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_collisionCertificate
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate shift m p t ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
          shift p t := by
  constructor
  · intro hcertificate
    exact ⟨hcertificate.cofiniteReconstruction, hcertificate.collisionCertificate⟩
  · rintro ⟨hrec, hcollision⟩
    exact {
      cofiniteReconstruction := hrec
      rankOneLogDetCurvatureNegative :=
        hcollision.rankOneLogDetCurvatureNegative }

/-- **Exact Xi Gaussian sign-duality phase law.**  Cofinite reconstruction and packet rank at
least two are exactly the simultaneous strict-negative distance curvature and globally
nonnegative coherent curvature phase. -/
theorem xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        2 ≤ N) ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        shift m p t := by
  constructor
  · rintro ⟨hrec, htwo⟩
    apply
      (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_collisionCertificate
        shift m p t).2
    refine ⟨hrec, ?_⟩
    exact
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).1 ⟨
          ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
            shift m).1 hrec).1,
          htwo⟩
  · intro hcertificate
    have hsplit :=
      (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff_reconstruction_and_collisionCertificate
        shift m p t).1 hcertificate
    exact ⟨hsplit.1,
      ((xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).2 hsplit.2).2⟩

/-- **Universal collision-only Gaussian sign-duality law.**  Collision freedom and packet rank
two are equivalent to the geometric sign-duality certificate simultaneously at every prime and
every nonnegative distance-metric scale. -/
theorem
    xiTransversePrimeShift_injective_and_two_le_iff_every_gaussianCollisionSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) :
    (Function.Injective shift ∧ 2 ≤ N) ↔
      ∀ (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
          shift p t := by
  constructor
  · intro hcondition p t ht
    exact
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p t ht).1 hcondition
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    exact
      (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff
        shift p 0 le_rfl).2 (hall p 0 le_rfl)

/-- **Universal Xi Gaussian sign-duality law.**  One exact reconstruction phase and rank two are
equivalent to the sign-duality certificate at every target depth, prime, and nonnegative
distance-metric scale. -/
theorem
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_two_le_iff_every_gaussianCurvatureSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ) (sourceDepth : ℕ) :
    (XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift sourceDepth ∧
        2 ≤ N) ↔
      ∀ (m : ℕ) (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift m p t := by
  constructor
  · rintro ⟨hsource, htwo⟩ m p t ht
    have hcondition :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift sourceDepth).1 hsource
    have htarget :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift m).2 hcondition
    exact
      (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
        shift m p t ht).1 ⟨htarget, htwo⟩
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall sourceDepth p 0 le_rfl
    exact
      (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
        shift sourceDepth p 0 le_rfl).2 hcertificate

/-- **Universal curvature-phase/sign-duality law.**  One Gaussian-curvature phase at a
nonnegative source scale is exactly reconstruction sign duality at every depth, prime, and
nonnegative target scale. -/
theorem
    xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
    {N : ℕ} (shift : Fin N → ℕ)
    (sourceDepth : ℕ) (sourcePrime : Nat.Primes)
    (sourceScale : ℝ) (hsourceScale : 0 ≤ sourceScale) :
    XiTransversePrimeJetApertureGaussianCurvaturePhase
        shift sourceDepth sourcePrime sourceScale ↔
      ∀ (m : ℕ) (p : Nat.Primes) (t : ℝ), 0 ≤ t →
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift m p t := by
  calc
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            shift sourceDepth ∧
          2 ≤ N :=
      xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        shift sourceDepth sourcePrime sourceScale hsourceScale
    _ ↔ _ :=
      xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_two_le_iff_every_gaussianCurvatureSignDualityCertificate
        shift sourceDepth

end

end RHTower
