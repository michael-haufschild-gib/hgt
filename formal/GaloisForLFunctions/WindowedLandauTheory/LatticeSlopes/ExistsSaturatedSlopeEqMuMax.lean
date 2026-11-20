import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.CovolEqGram
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.CovolPos
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.CovolEqCovolume
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.GramDetLe
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.SlopesBdd
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.SlopeLeMuMaxOf
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.SlopeInequality
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.DegQuot
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.SaturationProperties
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.ShortVector
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.FiniteSaturated
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.MuMaxAttained
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.MuMaxLeMin
import GaloisForLFunctions.WindowedLandauTheory.LatticeSlopes.OrthSum

namespace WindowedLandauTheory.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem muMaxMono : MuMaxMono := muMaxMono_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem muMax_mono {L N : Submodule ℤ E} [DiscreteTopology L] (hN : N ≤ L) (hN0 : N ≠ ⊥) :
    muMax N ≤ muMax L :=
  muMaxMono E L N ‹_› hN hN0

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end WindowedLandauTheory.F
