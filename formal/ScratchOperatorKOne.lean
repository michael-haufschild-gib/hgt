import GaloisForLFunctions.RHTower.PrimeAFMatrixDeterminantSplit
import GaloisForLFunctions.RHTower.PrimeAFChargeDirectLimit
import Mathlib.Algebra.Colimit.Module

open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

#check AddEquiv.ofBijective
#check LinearEquiv.ofBijective
#check AddEquiv.toIntLinearEquiv
#check AddMonoidHom.toIntLinearMap
#check LinearEquiv.toLinearMap
#check Module.DirectLimit.lift
#check Additive.ofMul
#check Additive.toMul
#check Multiplicative.ofAdd
#check Multiplicative.toAdd
#check Module.DirectLimit.induction_on
#print FundamentalGroup.map
#print finiteMatrixDeterminantKOneHom

noncomputable local instance {n : ℕ} : CommGroup
    (FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :=
  fundamentalGroupCommGroup

noncomputable local instance : CommGroup (FundamentalGroup (Units ℂ) 1) :=
  fundamentalGroupCommGroup

theorem finiteMatrixDeterminantKOneHom_apply (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    finiteMatrixDeterminantKOneHom (iota := Fin (n + 1))
        (Additive.ofMul q) =
      Additive.ofMul (finiteUnitaryDeterminantKOneMap n q) := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      simp [finiteMatrixDeterminantKOneHom, FundamentalGroup.map,
        FundamentalGroupoid.map, finiteUnitaryDeterminantKOneMap,
        finiteUnitaryDeterminantPath, basedMapPath]

end

end PrimeQuasiLocalCharge
