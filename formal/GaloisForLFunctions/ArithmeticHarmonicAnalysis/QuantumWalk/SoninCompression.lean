import GaloisForLFunctions.HilbertMetric.QuantumWalk.Compression
import GaloisForLFunctions.RHTower.SoninProjectionQuantumWalk

/-!
# All-time Sonin walk compression

The physical/Fourier cutoff walk has the same Chebyshev compression law
as a Grover walk. Every return operator on the Fourier cutoff is determined
by the existing prolate block, with no spectral or positivity assumption.
-/

noncomputable section
namespace RHTower
open Polynomial

/-- Every compressed Sonin walk power is a Chebyshev polynomial of its prolate block. -/
theorem centralSonin_walk_compression (a : ℝ) (n : ℕ) :
    (centralFourierForbidden a).starProjection *
        centralSoninProjectionQuantumWalk a ^ n *
        (centralFourierForbidden a).starProjection =
      aeval (2 * soninAlternatingBlock
          (centralPhysicalForbidden a) (centralFourierForbidden a) -
          (centralFourierForbidden a).starProjection)
        (Chebyshev.T ℂ (n : ℤ)) * (centralFourierForbidden a).starProjection := by
  have hQ := (centralFourierForbidden a).isIdempotentElem_starProjection
  have hsignal :
      (centralFourierForbidden a).starProjection *
        HTGeometry.projectionReflection (centralPhysicalForbidden a).starProjection *
        (centralFourierForbidden a).starProjection =
      2 * soninAlternatingBlock
          (centralPhysicalForbidden a) (centralFourierForbidden a) -
          (centralFourierForbidden a).starProjection := by
    dsimp [HTGeometry.projectionReflection, soninAlternatingBlock]
    noncomm_ring [show (centralFourierForbidden a).starProjection *
      (centralFourierForbidden a).starProjection =
      (centralFourierForbidden a).starProjection from hQ]
  simpa only [centralSoninProjectionQuantumWalk, hsignal] using
    GaloisForLFunctions.HilbertMetric.QuantumWalk.starProjection_walk_pow
      (centralPhysicalForbidden a) (centralFourierForbidden a) n

/-- Reversing the two cutoffs gives the corresponding physical-sector return law. -/
theorem centralSonin_reverse_walk_compression (a : ℝ) (n : ℕ) :
    (centralPhysicalForbidden a).starProjection *
        HTGeometry.twoProjectionQuantumWalk
          (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection ^ n *
        (centralPhysicalForbidden a).starProjection =
      aeval ((centralPhysicalForbidden a).starProjection *
          HTGeometry.projectionReflection (centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection)
        (Chebyshev.T ℂ (n : ℤ)) * (centralPhysicalForbidden a).starProjection :=
  GaloisForLFunctions.HilbertMetric.QuantumWalk.starProjection_walk_pow
    (centralFourierForbidden a) (centralPhysicalForbidden a) n

end RHTower

#print axioms RHTower.centralSonin_walk_compression
#print axioms RHTower.centralSonin_reverse_walk_compression
