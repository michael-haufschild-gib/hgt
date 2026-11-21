import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.TwoAdic
import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.Groups
import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral


namespace WindowedLandauTheory

namespace TwoAdicCyclotomicDecomposition

theorem tower_group_foundations :
    UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
    GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
    NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian :=
  ⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel,
   gamEModel, ggModel, centralExtAbelian, commGen, rankBound,
   normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩

end TwoAdicCyclotomicDecomposition

