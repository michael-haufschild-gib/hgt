import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.OmegaHasseExactSequence

/-!
# Hasse classification of section-defect cocycles

Obstruction equality is congruence modulo globally induced coboundaries, and every obstruction
class has a cocycle representative unique modulo those coboundaries.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Two local section-defect cocycles have the same obstruction exactly when their difference is a
global coboundary. -/
theorem omegaCocycle_congr_hasse_iff
    (omega eta : twoCocycles (G := G) (A := A)) :
    omega - eta ∈ (twoCoboundaryCocycleAddHom (G := G) (A := A)).range ↔
      obstructionClass omega = obstructionClass eta :=
  addHasse_congr_iff
    (twoCoboundaryCocycleAddHom (G := G) (A := A))
    (obstructionClassAddHom (G := G) (A := A))
    twoCoboundaryCocycle_obstructionClass_exact omega eta

/-- Every obstruction class has a local cocycle representative, unique modulo globally induced
coboundaries. -/
theorem omegaObstruction_exists_unique_cocycle_mod_coboundary
    (o : secondConstraintCohomology (G := G) (A := A)) :
    ∃ omega : twoCocycles (G := G) (A := A), obstructionClass omega = o ∧
      ∀ eta : twoCocycles (G := G) (A := A), obstructionClass eta = o ↔
        eta - omega ∈
          (twoCoboundaryCocycleAddHom (G := G) (A := A)).range :=
  addHasse_exists_unique_mod_global
    (twoCoboundaryCocycleAddHom (G := G) (A := A))
    (obstructionClassAddHom (G := G) (A := A))
    twoCoboundaryCocycle_obstructionClass_exact
    obstructionClassAddHom_surjective o

end GaloisForLFunctions.RHTower
