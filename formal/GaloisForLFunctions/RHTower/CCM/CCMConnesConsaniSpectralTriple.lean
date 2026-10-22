import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniSmoothAlgebra

/-!
# Exact Connes--Consani finite-compression spectral triple

This module packages every clause of Proposition `propDpert` from Connes--Consani's 2021 paper.
The represented algebra is the full star algebra of smooth periodic functions, the operator is
literally `(1 - Π) D₀ (1 - Π)`, and the commutator is represented by an explicit bounded
operator.  Self-adjointness and compact resolvent are proved rather than assumed.
-/

open Module Topology Filter
open MeasureTheory
open scoped InnerProductSpace

namespace RHTower

open HilbertSchmidt GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance (L : CCMCircleLength) : Fact (0 < (L : ℝ)) := ⟨L.property⟩

/-- All analytic and representation-theoretic clauses of the Connes--Consani spectral triple,
with the source algebra and compressed Dirac operator fixed in the type. -/
structure CCMConnesConsaniSpectralTripleCertificate
    (L : CCMCircleLength) {k : ℕ} (v : CCMCircleSmoothPacket L k) : Prop where
  faithful : Function.Injective (ccmSmoothPeriodicAlgebraRepresentation L)
  compressionFormula :
    ∀ x : (ccmConnesConsaniCompressedDirac L v).domain,
      ccmConnesConsaniCompressedDirac L v x =
        (1 - ccmConnesConsaniProjection L v)
          (ccmCircleDirac (L : ℝ)
            ⟨(1 - ccmConnesConsaniProjection L v) (x : DiagonalL2 ℤ), by
              have hx : (x : DiagonalL2 ℤ) ∈ (ccmCircleDirac (L : ℝ)).domain := x.property
              exact (ccmCircleDirac (L : ℝ)).domain.sub_mem hx
                (smoothPacketProjection_mem_domain (ccmCircleDirac (L : ℝ)) v x)⟩)
  selfAdjoint : IsSelfAdjoint (ccmConnesConsaniCompressedDirac L v)
  compactResolventAtI :
    LinearPMap.HasCompactResolventAt
      (ccmConnesConsaniCompressedDirac L v) Complex.I
  preservesDomain :
    ∀ (a : CCMSmoothPeriodicAlgebra (L : ℝ))
      (x : (ccmConnesConsaniCompressedDirac L v).domain),
      ccmSmoothPeriodicAlgebraRepresentation L a (x : DiagonalL2 ℤ) ∈
        (ccmConnesConsaniCompressedDirac L v).domain
  commutatorIdentity :
    ∀ (a : CCMSmoothPeriodicAlgebra (L : ℝ))
      (x : (ccmConnesConsaniCompressedDirac L v).domain),
      ccmConnesConsaniCompressedDirac L v
          ⟨ccmSmoothPeriodicAlgebraRepresentation L a (x : DiagonalL2 ℤ),
            preservesDomain a x⟩ =
        ccmSmoothPeriodicAlgebraRepresentation L a
            (ccmConnesConsaniCompressedDirac L v x) +
          ccmConnesConsaniSmoothCommutator L v
            (ccmSmoothPeriodicAlgebraToDeninger a) (x : DiagonalL2 ℤ)

/-- **Connes--Consani 2021, Proposition `propDpert` (complete exact form).**

For every positive circle length and every finite packet in the smooth Dirac domain, multiplication
by the full algebra of smooth periodic functions is a faithful unital star representation, the
source compression `(1-Π)D₀(1-Π)` is self-adjoint with compact resolvent, and every represented
function preserves its domain with an explicit bounded commutator.  No spectral or analytic premise
is added. -/
theorem connesConsani_propDpert
    (L : CCMCircleLength) {k : ℕ} (v : CCMCircleSmoothPacket L k) :
    CCMConnesConsaniSpectralTripleCertificate L v where
  faithful := ccmSmoothPeriodicAlgebraRepresentation_injective L
  compressionFormula := ccmConnesConsaniCompressedDirac_apply L v
  selfAdjoint := connesConsani_propDpert_isSelfAdjoint L v
  compactResolventAtI := connesConsani_propDpert_hasCompactResolventAt_I L v
  preservesDomain := fun a x =>
    ccmSmoothCircleMultiplier_mem_compressedDomain L v
      (ccmSmoothPeriodicAlgebraToDeninger a) x
  commutatorIdentity := fun a x =>
    connesConsani_propDpert_boundedCommutator L v
      (ccmSmoothPeriodicAlgebraToDeninger a) x

end

end RHTower
