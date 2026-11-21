import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockHerm
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockPos
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DomPow
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf



namespace WindowedLandauTheory.GradedWeylDivisibility

theorem bidetMem : BideterminantMem := bideterminantMem
theorem hwMem : HWMem := highestWeightVectorMem
theorem hwNe : HWNe := highestWeightVectorNeZero
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
theorem bidetDominance : BideterminantDominance := bideterminantDominance
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
theorem hwRaise : HWRaise := highestWeightVectorRaising
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
theorem rowNuSum : RowNuSum := rowPartSum
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
theorem fockPos : FockPos := fischerInnerPos
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
theorem domPow : DomPow := dominancePowerProduct_holds
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end WindowedLandauTheory.GradedWeylDivisibility

