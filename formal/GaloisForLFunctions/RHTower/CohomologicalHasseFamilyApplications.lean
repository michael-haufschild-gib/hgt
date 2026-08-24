import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.OmegaHasseExactSequence

/-!
# Cohomological Hasse-family applications

Closed local two-cocycles modulo globally induced coboundaries are completely measured by their
second constraint-cohomology obstruction.  This packages a route-neutral local--global principle
for section defects.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Second constraint cohomology is a complete coordinate for closed local cocycles modulo global
coboundaries. -/
noncomputable def omegaCocycleObstructionHasseFamily :=
  GaloisForLFunctions.HTGeometry.HasseFamily.ofEquivSingle
    (omegaHasseCocycleQuotientEquivObstruction (G := G) (A := A)).toEquiv

end
end GaloisForLFunctions.RHTower
