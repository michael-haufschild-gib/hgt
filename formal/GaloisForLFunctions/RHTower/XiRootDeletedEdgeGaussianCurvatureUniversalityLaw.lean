import GaloisForLFunctions.RHTower.XiRootDeletedDyadicCofiniteHilbertUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedIncidenceGaussianCurvatureUniversalityLaw

/-!
# Root-deleted Xi edge independence and Gaussian curvature

For a zero-rooted integral shift packet, existing root-deleted dyadic recovery detects full vertex
injectivity.  Jointly with corrected or raw pair-difference recovery, it detects independence of
the chosen edge family in the rooted incidence matroid, equivalently Kirchhoff rigidity.

The nonroot Gaussian curvature phase already contains dyadic recovery and the sharp rank-two
condition.  Therefore the joint vertex/edge Hilbert phase collapses to a smaller exact interface:
rooted-incidence independence (or vertex conservation) together with strict Gaussian curvature.
No separate injectivity or dyadic-recovery premise remains on that side.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexOrder Differential

/-- **Corrected edge-independence/curvature law.**  Root-deleted dyadic vertex recovery,
corrected Xi edge recovery, and retained rank two are exactly rooted-incidence independence
together with strict nonroot Gaussian curvature. -/
theorem
    xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  have hphase :=
    xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
      root shift hroot sourcePrime metricPrime m t ht
  have hedge :=
    xiMobiusRootDeletedDyadicPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
      root shift hroot sourcePrime metricPrime tail head
  constructor
  · rintro ⟨hdyadic, hpairs, htwo⟩
    exact ⟨(hedge.1 ⟨hdyadic, hpairs⟩).2,
      hphase.1 ⟨hdyadic, htwo⟩⟩
  · rintro ⟨hindep, hcurvature⟩
    have hdyadicTwo := hphase.2 hcurvature
    have hinjective :=
      (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
        root shift hroot sourcePrime).1 hdyadicTwo.1
    have hdyadicPairs := hedge.2 ⟨hinjective, hindep⟩
    exact ⟨hdyadicPairs.1, hdyadicPairs.2, hdyadicTwo.2⟩

/-- **Raw edge-independence/curvature law.**  The same exact phase holds for raw even-Xi
pair-difference recovery. -/
theorem
    xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  have hphase :=
    xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
      root shift hroot sourcePrime metricPrime m t ht
  have hedge :=
    xiMobiusRootDeletedDyadicRawPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
      root shift hroot sourcePrime metricPrime tail head
  constructor
  · rintro ⟨hdyadic, hpairs, htwo⟩
    exact ⟨(hedge.1 ⟨hdyadic, hpairs⟩).2,
      hphase.1 ⟨hdyadic, htwo⟩⟩
  · rintro ⟨hindep, hcurvature⟩
    have hdyadicTwo := hphase.2 hcurvature
    have hinjective :=
      (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
        root shift hroot sourcePrime).1 hdyadicTwo.1
    have hdyadicPairs := hedge.2 ⟨hinjective, hindep⟩
    exact ⟨hdyadicPairs.1, hdyadicPairs.2, hdyadicTwo.2⟩

/-- **Kirchhoff/curvature law.**  Corrected edge recovery and retained rank two are equivalently
triviality of every conserved complex edge flow together with strict nonroot Gaussian curvature. -/
theorem
    xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_vertexConservation_and_gaussianCurvature
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (∀ weight : Fin d → ℂ,
          (∀ v : Fin (N + 1),
            (∑ e, if head e = v then weight e else 0) =
              ∑ e, if tail e = v then weight e else 0) →
            ∀ e, weight e = 0) ∧
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  have hphase :=
    xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
      root shift hroot sourcePrime metricPrime m t ht
  have hedge :=
    xiMobiusRootDeletedDyadicPairDifferenceCofiniteHilbertPhase_iff_vertexConservation
      root shift hroot sourcePrime metricPrime tail head
  constructor
  · rintro ⟨hdyadic, hpairs, htwo⟩
    exact ⟨(hedge.1 ⟨hdyadic, hpairs⟩).2,
      hphase.1 ⟨hdyadic, htwo⟩⟩
  · rintro ⟨hconservation, hcurvature⟩
    have hdyadicTwo := hphase.2 hcurvature
    have hinjective :=
      (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
        root shift hroot sourcePrime).1 hdyadicTwo.1
    have hdyadicPairs := hedge.2 ⟨hinjective, hconservation⟩
    exact ⟨hdyadicPairs.1, hdyadicPairs.2, hdyadicTwo.2⟩

/-- Canonical incidence volume one can replace dyadic recovery in the corrected
edge-independence/curvature law. -/
theorem
    xiMobiusRootDeletedIncidenceVolumePairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (xiTransverseRootDeletedShift root shift))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  calc
    _ ↔ XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N :=
      and_congr
        (by
          exact
            (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_one
              root shift hroot sourcePrime).symm)
        Iff.rfl
    _ ↔ _ :=
      xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head m t ht

/-- **Universal corrected edge/curvature phase.**  One root-deleted vertex/edge recovery phase
with retained rank two holds exactly when rooted-incidence independence accompanies strict
Gaussian curvature at every target prime, depth, and nonnegative scale. -/
theorem
    xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_every_rootedIncidence_and_gaussianCurvature
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  constructor
  · intro h metricPrime m t ht
    exact
      (xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head m t ht).1 h
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hphase := hall metricPrime 0 0 (by norm_num)
    exact
      (xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head 0 0 (by norm_num)).2
          hphase

/-- **Corrected edge/sign-duality factorization.**  Root-deleted dyadic vertex recovery,
corrected edge recovery, and retained rank two are exactly rooted-incidence independence
together with nonroot reconstruction sign duality at any independently chosen target. -/
theorem
    xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_curvatureSignDuality
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1))
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (xiTransverseRootDeletedShift root shift)
            jetDepth valuationPrime valuationScale :=
      xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime valuationPrime tail head
        jetDepth valuationScale hvaluationScale
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale)

/-- **Universal corrected edge/sign-duality factorization.**  The same vertex/edge recovery
phase is exactly rooted-incidence independence together with nonroot sign duality at every
depth, prime, and nonnegative scale. -/
theorem
    xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_every_curvatureSignDuality
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiTransverseRootDeletedShift root shift)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 :=
      xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime sourcePrime tail head 0 0 le_rfl
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 le_rfl)

/-- **Raw edge/sign-duality factorization.**  Root-deleted dyadic vertex recovery, literal raw
edge recovery, and retained rank two are exactly rooted-incidence independence together with
nonroot reconstruction sign duality at any independently chosen target. -/
theorem
    xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_curvatureSignDuality
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1))
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (xiTransverseRootDeletedShift root shift)
            jetDepth valuationPrime valuationScale :=
      xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime valuationPrime tail head
        jetDepth valuationScale hvaluationScale
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_gaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale)

/-- **Universal raw edge/sign-duality factorization.**  The literal raw vertex/edge recovery
phase is exactly rooted-incidence independence together with nonroot sign duality at every
depth, prime, and nonnegative scale. -/
theorem
    xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_every_curvatureSignDuality
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    (XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift sourcePrime ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        2 ≤ N) ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiTransverseRootDeletedShift root shift)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
          XiTransversePrimeJetApertureGaussianCurvaturePhase
            (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 :=
      xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime sourcePrime tail head 0 0 le_rfl
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_every_gaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift) 0 sourcePrime 0 le_rfl)

end

end RHTower
