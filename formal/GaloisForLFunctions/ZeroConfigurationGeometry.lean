import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.ZeroConfigurationGeometry.TheSquaredGapIsReadAtSecondOrder
import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture
import GaloisForLFunctions.ZeroConfigurationGeometry.HidingNeedsNearCollisions
import GaloisForLFunctions.ZeroConfigurationGeometry.TiltedInghamInequality
import GaloisForLFunctions.ZeroConfigurationGeometry.DifferentialWindowsInvertTheCamera
import GaloisForLFunctions.ZeroConfigurationGeometry.TheInverseWindowsAreStable
import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimesPinEveryFinitePieceOfZeta
import GaloisForLFunctions.ZeroConfigurationGeometry.TheArithmeticPinningIsStable
import GaloisForLFunctions.ZeroConfigurationGeometry.TheHeightCurvatureOfThePrimeChannel
import GaloisForLFunctions.ZeroConfigurationGeometry.IdentificationIsCheaperThanSign
import GaloisForLFunctions.ZeroConfigurationGeometry.RamanujanIsRealityOfAnEulerColumn
import GaloisForLFunctions.ZeroConfigurationGeometry.EulerColumnsAreSeenJustAboveTheirPrime
import GaloisForLFunctions.ZeroConfigurationGeometry.TheSquareRootThresholdIdentifiesColumns
import GaloisForLFunctions.ZeroConfigurationGeometry.RealityLeavesOnlyThroughCollision
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatTimeSpreadsTheConfiguration
import GaloisForLFunctions.ZeroConfigurationGeometry.LaguerreStepsNeverDeepenTheConfiguration
import GaloisForLFunctions.ZeroConfigurationGeometry.ShiftAveragesContractTheDepth
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCosineCameraHasOnlyRealKernelZeros
import GaloisForLFunctions.ZeroConfigurationGeometry.WindowsBlindToALattice
import GaloisForLFunctions.ZeroConfigurationGeometry.ShallowPairsAreNearCollisions
import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsAtTheDensityAperture
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh

/-!
# Zero Configuration Geometry

Umbrella for the explicit formula read as a camera.

* The camera: depth as tilt, the pair and depth signals, the second-order law of the squared gap.
* Identification: finite modifications are seen at every aperture, with an explicit and stable
  inverse by differential windows; the primes pin every finite piece of the zeros of `ζ`.
* Hiding: on-line mimics need near-collisions; Ingham's inequality with tilts and its block form
  for FE pairs; shallow pairs are near-collisions (the tilted near-collision constraint).
* The function-field camera: identification at lag `g log q`, mimic classification, sharpness.
* Euler columns: the Ramanujan bound as reality, separation of columns just above their prime,
  the square-root threshold for columns of Riemann–von Mangoldt density.
* Deformations: the collision exit theorem, the heat-time spread law and the bounded backward
  exit, Laguerre steps never deepen, heat steps never shrink the mesh, shift averages contract the
  depth.
* Window design: real kernel zeros of the cosine camera, windows blind to a real lattice, to
  finite unions of lattices at the density aperture and to zero sets of exponential polynomials.

See `ZeroConfigurationGeometry/README.md`.
-/
