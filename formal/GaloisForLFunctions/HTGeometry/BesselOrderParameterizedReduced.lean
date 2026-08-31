import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedPicardVessiot
import GaloisForLFunctions.HTGeometry.SigmaDeltaSimpleReduced

/-!
# Reducedness of the concrete Bessel parameterized PV quotient

The constructed Bessel quotient is nontrivial and `σ`-`δ`-simple.  Characteristic-zero
nilradical stability therefore supplies reducedness without retaining it as PPV data.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

/-- Every constructed Bessel PPV datum has a reduced quotient. -/
theorem BesselOrderParameterizedPVData.isReduced {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    IsReduced ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) := by
  letI : Differential (RatFunc Constants) := coordinateTotalDifferential
  letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    quotientDifferential data.M data.isSigmaDeltaIdeal.2
  letI : Nontrivial ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  exact isReduced_of_isSigmaDeltaSimple data.isSigmaDeltaSimple

/-- Unconditional existence of a reduced concrete Bessel PPV quotient at every real slope. -/
theorem besselOrder_parameterizedPicardVessiot_reduced :
    ∀ s : ℝ, ∃ data : BesselOrderParameterizedPVData s,
      IsReduced ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) := by
  intro s
  obtain ⟨data⟩ := besselOrder_parameterizedPicardVessiot_exists s
  exact ⟨data, data.isReduced⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
