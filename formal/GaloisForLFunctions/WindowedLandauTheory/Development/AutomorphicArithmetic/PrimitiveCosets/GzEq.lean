import GaloisForLFunctions.WindowedLandauTheory.StatementOC
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

namespace UpperTheory.Comparison₂

open WindowedLandauTheory

/-- On the range of summation, the principal Cesàro ramp is already nonnegative. -/
theorem Gz_eq (y : ℝ) : Gz y = HC.An.G y :=
  (MainNotions.GlobalTheoryTheory.G_eq_Gfun y).symm

end UpperTheory.Comparison₂
