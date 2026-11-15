import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheWallOfTheFrameIsAPhaseLFunction
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheAverageRowIsBlindToTheTarget
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.ResidueTargetProjection
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.TheNonprincipalRowRetainsTheTarget
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheNonprincipalFilterRecoversTheTarget
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.ShortColumnsAreIncoherent
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberCarriesTheMoebiusSign
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.ShortColumnsOfTheEisensteinLatticeAreIncoherent
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheWallIsThePriceOfCompletion
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsAnAngularTwist
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheGramOfTwoRowsIsACompletedSum
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheShortSexticGramIsDiagonal
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheRowRootNumberIsTheSquareOfTheThetaCoefficient
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheReflectedGramIsTwistedByTheRowRootNumbers
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.IncompleteReciprocityRetainsPhasesWithSubcubicSaving
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.FamilyContinuationRestoresTheGaussWallsUnderTruncation

/-!
# Coherence Theory of Reciprocity Families

Umbrella for the phases between the amplitudes of a family of rows and the columns of a
reciprocity kernel: the wall of the two-estimate frame as a phase `L`-function and the price of
completion; doubly-incomplete cusp reciprocity transforms, which retain the Möbius target and all
local Gauss root-number phases with a uniform sub-cubic reflection-defect saving on the
super-conductor reflection box `N(c) ≤ X^{1 - δ}`, fail in the sub-conductor regime
`N(c) ≥ X^{1 + κ}`, and under row-family Poisson continuation restore the `2/3` uncoupled and `3/5`
coupled walls across every local and global cutoff; the average row of the cubic-theta probe, which
carries no reciprocal of the target; Poisson summation in the rows (short columns are incoherent,
over `ℤ^d` and over `ℤ[ω]`); the Gram entry of two rows as a completed sum, its reflection twisted
by the root numbers of the rows, and the diagonal short Gram; the root number of a row as a
phase of bounded conductor times the square of the theta coefficient, whose cube is the Möbius sign
times the angular character. See `CoherenceTheoryOfReciprocityFamilies/README.md`.
-/
