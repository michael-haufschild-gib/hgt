import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.GlobalSchurBounds.TieGlobal
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

/-! The host reciprocity map in additive sign and orbit coordinates. -/

noncomputable section

namespace UpperTheory.Comparison₂

open WindowedLandauTheory WindowedLandauTheory.HC WindowedLandauTheory.D5 WindowedLandauTheory.LFunctionChainParameters.characterSumData WindowedLandauTheory.LFunctionChainParameters.LHost

def toE (φ : Frame) : φ.GG →* Multiplicative (E0 × φ.A) where
  toFun g := Multiplicative.ofAdd ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)), φ.iotaInv g.2)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, map_one]
    rfl
  map_mul' g h := by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    rfl

variable {φ : Frame}

abbrev recH (H : HostRaw φ) : (ZMod H.condN)ˣ →* Multiplicative (E0 × φ.A) :=
  WindowedLandauTheory.MainNotions.recOf H

abbrev arith (H : HostRaw φ) : ArithData φ.A :=
  WindowedLandauTheory.MainNotions.arithOf H

end UpperTheory.Comparison₂

end
