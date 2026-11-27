import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.ArithmeticHostSupply
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZeroFreeCorollaries

/-! The Selmer window estimate supplies hosts of width 3/2.
The connected-family theorem then gives the primitive zero-free
half-plane and the Euler factors extend it to all characters. -/

namespace UpperTheory.Top

open WindowedLandauTheory.HC

theorem zero_free_all_of_topG_v_win (hG : TopG) (hV : VWin) : ZeroFreeAll :=
  zeroFreeAll_of_topG (la := 3 / 2) (by norm_num) hG fun ψ => UpperTheory.T3.supplyChi ψ (hV ψ)

theorem every_character_of_topG_v_win (hG : TopG) (hV : VWin) : DirichletLNonvanishingRightOfHalf :=
  allChi_of_zeroFreeAll (zero_free_all_of_topG_v_win hG hV)

end UpperTheory.Top
