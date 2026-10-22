/-
# Monodromy blocks of the critical horizon and their normalizations

Bundles the block-cover argument for primitivity of the critical geometric monodromy. For a
monodromy block containing the canonical sheet, the block-stabilizer fixed field lies inside the
critical source field, and it is a nontrivial extension of the observation field when the block is
proper. Its integral closure over the observation chart (the block normalization) is module-finite,
embeds in the source chart, and is a linear retract of it via normalized trace, so it inherits
flatness. Schur inertia stabilizes every non-singleton block, so the normalization is unramified at
every Schur valuation; it is also unramified away from the Schur divisor, and purity makes it finite
etale. On complex points it is a proper, surjective, path-connected covering of the observation chart,
and the two explicit source meridians force its fibre to be a singleton.
-/

import GaloisForLFunctions.HTGeometry.Critical.Block.AwaySchurUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.ConjugateInertia
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldAllSchurUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldNontrivial
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldNormalization
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldSourceDescent
import GaloisForLFunctions.HTGeometry.Critical.Block.FieldUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationChart
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationEtaleCover
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationFinitePresentation
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationPathConnected
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationPurity
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationTrace
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationTraceCoercion
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationTraceEvaluation
import GaloisForLFunctions.HTGeometry.Critical.Block.NormalizationTraceRetract
import GaloisForLFunctions.HTGeometry.Critical.Block.SchurAtPrimeUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.SchurLocalizationUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.SchurNormalizationRamification
import GaloisForLFunctions.HTGeometry.Critical.Block.SchurNormalizationUnramified
import GaloisForLFunctions.HTGeometry.Critical.Block.SourceExplicitMeridianElimination
import GaloisForLFunctions.HTGeometry.Critical.Block.SourceMeridianElimination
