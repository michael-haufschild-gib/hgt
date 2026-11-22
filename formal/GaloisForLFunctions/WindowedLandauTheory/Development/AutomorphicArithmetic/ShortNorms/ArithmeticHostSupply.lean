import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.CharacterHostSupply
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.ShortNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.SmallOne
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.Supply

/-! The short-interval and least-prime theorems supply the arithmetic hosts. -/

open WindowedLandauTheory.HC GlobalTheory.EX UpperTheory.Top

namespace UpperTheory.T3

theorem host_ex_one : HostEx := hostExOf shortNorm small_one

theorem supplyChi (ψ : PChar) (h : VWinAt ψ 401) : HostExW (3 / 2) (GChi ψ).req :=
  supplyChiOf shortNorm small_one ψ h

end UpperTheory.T3
