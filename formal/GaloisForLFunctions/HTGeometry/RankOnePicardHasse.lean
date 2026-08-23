import GaloisForLFunctions.HTGeometry.RankOneCohomology

/-!
# Hasse classification for the rank-one Picard skeleton

Rank-one scalar difference cocycles modulo global scalar coboundaries form the Picard skeleton.
This module records the quotient as a local--global congruence principle: two cocycles represent the
same class exactly when their ratio is a coboundary, and a class is globally trivial exactly when
its cocycle is a coboundary.
-/

namespace GaloisForLFunctions

noncomputable section

variable {ι G : Type*} [CommGroup G] {act : ι → G →* G}

/-- Canonical class map from rank-one cocycles to the Picard quotient. -/
def rankOnePicardClass (hcomm : commutingActions act) :
    rankOneCocycles act →* rankOnePicard hcomm :=
  QuotientGroup.mk' (rankOneCoboundaries hcomm)

/-- Every rank-one Picard class has a scalar-cocycle representative. -/
theorem rankOnePicardClass_surjective (hcomm : commutingActions act) :
    Function.Surjective (rankOnePicardClass hcomm) :=
  QuotientGroup.mk'_surjective _

/-- Two rank-one cocycles define the same Picard class exactly when their ratio is a global scalar
coboundary. -/
theorem rankOnePicard_congr_hasse_iff
    (hcomm : commutingActions act) (a b : rankOneCocycles act) :
    a / b ∈ rankOneCoboundaries hcomm ↔
      rankOnePicardClass hcomm a = rankOnePicardClass hcomm b :=
  QuotientGroup.eq_iff_div_mem.symm

/-- A rank-one Picard class is trivial exactly when its cocycle is a global scalar coboundary. -/
theorem rankOnePicardClass_eq_one_iff_coboundary
    (hcomm : commutingActions act) (a : rankOneCocycles act) :
    rankOnePicardClass hcomm a = 1 ↔ a ∈ rankOneCoboundaries hcomm :=
  QuotientGroup.eq_one_iff _

/-- Every rank-one Picard class has a cocycle representative, unique modulo global scalar
coboundaries. -/
theorem rankOnePicard_exists_unique_mod_coboundary
    (hcomm : commutingActions act) (z : rankOnePicard hcomm) :
    ∃ a : rankOneCocycles act, rankOnePicardClass hcomm a = z ∧
      ∀ b, rankOnePicardClass hcomm b = z ↔
        b / a ∈ rankOneCoboundaries hcomm := by
  obtain ⟨a, ha⟩ := rankOnePicardClass_surjective hcomm z
  refine ⟨a, ha, fun b => ?_⟩
  rw [← ha]
  exact (rankOnePicard_congr_hasse_iff hcomm b a).symm

end

end GaloisForLFunctions
