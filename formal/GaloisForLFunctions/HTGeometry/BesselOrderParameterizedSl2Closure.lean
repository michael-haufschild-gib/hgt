import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedGaloisDichotomy

/-!
# Full Bessel parameterized Galois closure for every concrete PPV quotient

The tangent-density dichotomy is uniform in the chosen parameterized Picard--Vessiot quotient.
For positive physical scale its isomonodromy branch is impossible, so every such quotient admits
a comparison-jet presentation whose determinant-one Galois monoid is Kolchin dense in `SL₂`.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

local instance besselOrderParameterizedSl2ClosureBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderParameterizedSl2ClosurePPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderParameterizedSl2ClosurePPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

/-- Every concrete positive-scale Bessel PPV quotient has full determinant-one closure. -/
theorem modifiedBesselOrder_sl2_galoisClosure_for_data
    (s : ℝ) (hs : 0 < s) (data : BesselOrderParameterizedPVData s) :
    ∃ comparison : data.ComparisonJetData,
      ∀ g : Matrix (Fin 2) (Fin 2) Constants, g.det = 1 →
        g ∈ matrixZeroSet (C := Constants) (A := Constants)
          (matrixVanishingIdeal
            {h ∈ galoisMonoid
                (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                comparison.Z
                (fun i j => mem_comparisonJetAlgebra_entry comparison.Z comparison.w i j)
                (tensorDifferentialPoints
                  (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                  comparison.deriv_stable) |
              h.det = 1}) := by
  obtain ⟨comparison⟩ := data.comparisonJetData_nonempty
  refine ⟨comparison, ?_⟩
  rcases comparison.sl2_or_isomonodromy_of_tangentDensity data hs with hsl2 | hiso
  · exact hsl2
  · exact (modifiedBesselOrder_no_isomonodromy_in_differentialClosure s hs hiso).elim

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
