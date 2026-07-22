import GaloisForLFunctions.HTGeometry.FermatCubicWeylRepresentation
import GaloisForLFunctions.HTGeometry.HeisenbergHorizonRepresentation

/-!
# Fermat cubic Heisenberg maximal horizon

The explicit three-state Weyl realization and the canonical Heisenberg representation fit
without loss: nested operator-commutator symbols recover the Fermat cubic dependence horizon, and
the faithful operator embedding preserves maximal exterior commutator rank.  Thus scalar
dependence and noncommutative bivector information survive simultaneously at operator level.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Fermat cubic Heisenberg maximal-horizon law.**  The canonical Heisenberg symbols of the
explicit Weyl differential field are dependent exactly on the Fermat cubic, while their law
commutator map remains injective on every bivector. -/
theorem fermatCubicWeyl_heisenbergMaximalHorizon
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    let ρ := generalizedCliffordShiftFieldDerivationLaw
      (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
        (fermatCubicThird ω))
    let x := generalizedCliffordShiftFieldRoot fermatCubicWeylRoot
    {c : Fin 3 → K |
        ¬ AlgebraicIndependent K (heisenbergDirectionalJetSymbol ρ x c)} =
        {c : Fin 3 → K | fermatCubicPotential c = 0} ∧
      Function.Injective (heisenbergLawCommutatorMap ρ) := by
  dsimp only
  have hmax := fermatCubicWeyl_maximalHorizon ω hω
  constructor
  · exact (heisenbergDependenceHorizon_eq
      (generalizedCliffordShiftFieldDerivationLaw
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω)))
      (generalizedCliffordShiftFieldRoot fermatCubicWeylRoot)).trans hmax.1
  · exact (heisenbergLawCommutatorMap_injective_iff
      (generalizedCliffordShiftFieldDerivationLaw
        (fermatCubicSymbol (fermatCubicClock ω) fermatCubicShift
          (fermatCubicThird ω)))).2 hmax.2

end

end GaloisForLFunctions.HTGeometry
