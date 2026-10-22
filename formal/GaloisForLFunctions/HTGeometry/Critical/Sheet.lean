/-
# Geometric sheets at the Schur place

Bundles the sheet-by-sheet analysis at the chosen normal-closure Schur valuation: every geometric
sheet keeps the chart algebra and Schur coordinates integral, the source scale is a unit, and sheets
with the same reduced Schur label have the same residues and cut out the same place. Singular sheets
pull the Schur place back to the Schur place, their reduced Jacobian has corank one with one fixed
conormal line, and their collision tangents are singular with nonzero constant term. The stabilizer of
a sheet is an inertia group, the canonical label fibre is one inertia orbit, orbit size equals the
ramification index of the sheet's place, and ramification is concentrated on the collision support.
-/

import GaloisForLFunctions.HTGeometry.Critical.Sheet.ChartIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Sheet.CollisionTangent
import GaloisForLFunctions.HTGeometry.Critical.Sheet.ConormalVector
import GaloisForLFunctions.HTGeometry.Critical.Sheet.CoordRingResidue
import GaloisForLFunctions.HTGeometry.Critical.Sheet.FixedConormal
import GaloisForLFunctions.HTGeometry.Critical.Sheet.JacobianCorankOne
import GaloisForLFunctions.HTGeometry.Critical.Sheet.JetUnit
import GaloisForLFunctions.HTGeometry.Critical.Sheet.LabelInertiaOrbit
import GaloisForLFunctions.HTGeometry.Critical.Sheet.OrbitRamification
import GaloisForLFunctions.HTGeometry.Critical.Sheet.PlaceRamificationIndex
import GaloisForLFunctions.HTGeometry.Critical.Sheet.ReducedJacobian
import GaloisForLFunctions.HTGeometry.Critical.Sheet.ResidueCongruence
import GaloisForLFunctions.HTGeometry.Critical.Sheet.ScaleUnit
import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurCoordinateIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurCoordinateResidue
import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurPlacePullback
import GaloisForLFunctions.HTGeometry.Critical.Sheet.SchurPullback
import GaloisForLFunctions.HTGeometry.Critical.Sheet.Singularity
import GaloisForLFunctions.HTGeometry.Critical.Sheet.StabilizerInertia
import GaloisForLFunctions.HTGeometry.Critical.Sheet.UnramifiedOutsideCollision
