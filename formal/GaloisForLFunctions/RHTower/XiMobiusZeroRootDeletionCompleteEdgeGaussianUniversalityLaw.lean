import GaloisForLFunctions.RHTower.XiMobiusZeroRootDeletionGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedEdgeGaussianCurvatureUniversalityLaw

/-!
# Xi--Möbius zero-root deletion complete edge/Gaussian universality

The zero-root curvature certificate already combines failure of every full loop-sensitive
recovery interface with successful root-deleted dyadic, canonical, Gaussian, differential
graphic, strict-curvature, and nonnormal phases.  The edge-curvature laws separately classify
corrected and raw pair-difference recovery by rooted-incidence independence and Kirchhoff
conservation.

One corrected root-deleted edge-recovery phase is therefore equivalent to the complete zero-root
certificate together with raw edge recovery, rooted-incidence independence, and triviality of
every conserved complex edge flow, uniformly at every metric prime, depth, and nonnegative
Gaussian scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexOrder Differential

/-- **Xi--Möbius zero-root deletion complete edge/Gaussian universality law.**  Corrected
root-deleted vertex/edge recovery and the sharp rank threshold are exactly the universal complete
zero-root failure/success certificate, raw edge recovery, rooted-incidence independence, and
Kirchhoff rigidity. -/
theorem xiMobiusZeroRootDeletion_completeEdgeGaussianUniversality
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
        XiMobiusZeroRootDeletionGaussianCurvatureUniversalityCertificate
          root shift tail head sourcePrime metricPrime m t ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          shift tail head ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ ∧
        (∀ weight : Fin d → ℂ,
          (∀ v : Fin (N + 1),
            (∑ e, if head e = v then weight e else 0) =
              ∑ e, if tail e = v then weight e else 0) →
            ∀ e, weight e = 0) := by
  constructor
  · intro h metricPrime m t ht
    have hcertificate :=
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime m t ht).1
          ⟨h.1, h.2.2⟩
    have hedge :=
      (xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head m t ht).1 h
    have hraw :=
      (xiMobiusRootDeletedDyadicRawPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head m t ht).2 hedge
    have hconservation :=
      (xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_vertexConservation_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head m t ht).1 h
    exact ⟨hcertificate, hraw.2.1, hedge.1, hconservation.1⟩
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have h := hall metricPrime 0 0 (by norm_num)
    have hbase :=
      (xiMobius_zeroRootDeletion_rootDeletedDyadic_and_two_le_iff_curvatureUniversalityCertificate
        root shift hroot tail head sourcePrime metricPrime 0 0 (by norm_num)).2 h.1
    have hphase :=
      (xiMobiusRootDeletedDyadic_and_two_le_iff_gaussianCurvaturePhase
        root shift hroot sourcePrime metricPrime 0 0 (by norm_num)).1 hbase
    exact
      (xiMobiusRootDeletedDyadicPairDifference_and_two_le_iff_rootedIncidence_and_gaussianCurvature
        root shift hroot sourcePrime metricPrime tail head 0 0 (by norm_num)).2
          ⟨h.2.2.1, hphase⟩

end

end RHTower
