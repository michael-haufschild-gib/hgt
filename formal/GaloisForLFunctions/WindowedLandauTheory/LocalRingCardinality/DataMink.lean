import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import GaloisForLFunctions.WindowedLandauTheory.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

namespace WindowedLandauTheory.BasicNotions

abbrev minkM (n : ℕ) : ℕ := WindowedLandauTheory.HermitianLatticeCounting.S6.minkowskiM n

def DGamMink (D : D7) : Prop := (D.mem D.u₀).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m)

end WindowedLandauTheory.BasicNotions
