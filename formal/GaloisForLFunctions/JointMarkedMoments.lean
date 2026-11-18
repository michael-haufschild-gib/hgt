import GaloisForLFunctions.JointMarkedMoments.Detection.TheTwoBranchMinimax
import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheLimitingImprovement
import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheMomentRecursionStaysBelowTheLimit
import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheCeilingOfEarlierMomentRanges
import GaloisForLFunctions.JointMarkedMoments.Comparison.TheComparisonBoundary
import GaloisForLFunctions.JointMarkedMoments.Comparison.TheNecessaryComparisonPlanes
import GaloisForLFunctions.JointMarkedMoments.Induction.TheLargeValueExponents
import GaloisForLFunctions.JointMarkedMoments.Arithmetic.GaussSumPowersOfOrderThreeAndSix
import GaloisForLFunctions.JointMarkedMoments.Arithmetic.InjectiveMarks
import GaloisForLFunctions.JointMarkedMoments.Archimedean.TheAngularHankelMultiplier
import GaloisForLFunctions.JointMarkedMoments.Archimedean.NormScaledFourierHomogeneity

/-!
# Joint marked moments and the optimized zero-free half-plane

The scalar, finite-field and archimedean mathematics of the joint marked moment method for the
half-plane `Re s > B∗ = (99r∗ − 14)/(12(9r∗ − 1)) ≈ 0.8733458561`.

* `Detection`: the two-branch minimax of zero detection and the improved count of an affine
  supporting line.
* `LimitingRange`: the limiting improvement `G`, its differential equation and convexity, the
  stability of the moment recursion below `G`, and the ceiling of all earlier moment ranges.
* `Comparison`: the optimizing point `r∗`, the boundary `B∗`, its tangent line, and the exact
  plane identities behind the lower bound of the comparison.
* `Induction`: the exponent algebra of complete-factor selection, large values, sixth-power
  cofactors and the reference ordinary moment.
* `Arithmetic`: cubic and sextic Gauss sum powers and injective marks.
* `Archimedean`: the angular Hankel multiplier and norm-scaled Fourier homogeneity.
-/
