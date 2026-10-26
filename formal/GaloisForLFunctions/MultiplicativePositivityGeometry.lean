import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteFunctions
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity
import GaloisForLFunctions.MultiplicativePositivityGeometry.SimplePoleClassification
import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor
import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteProfiles
import GaloisForLFunctions.MultiplicativePositivityGeometry.ProfileCharacterization
import GaloisForLFunctions.MultiplicativePositivityGeometry.ProgressionModels
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryCompleteness
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryCalculus
import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass
import GaloisForLFunctions.MultiplicativePositivityGeometry.ExactFejerBarrier
import GaloisForLFunctions.MultiplicativePositivityGeometry.GrowthToForcing
import GaloisForLFunctions.MultiplicativePositivityGeometry.MultiFrequencyCap
import GaloisForLFunctions.MultiplicativePositivityGeometry.ZeroFreeRegionCalibration
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.FiniteBoundaryDivisors
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryZeroCapacity
import GaloisForLFunctions.MultiplicativePositivityGeometry.PositivityMargin
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryDivisorRange
import GaloisForLFunctions.MultiplicativePositivityGeometry.CharacterFamilies
import GaloisForLFunctions.MultiplicativePositivityGeometry.RankinSelbergBessel
import GaloisForLFunctions.MultiplicativePositivityGeometry.AbelianZeroMass
import GaloisForLFunctions.MultiplicativePositivityGeometry.DecayMassLaw
import GaloisForLFunctions.MultiplicativePositivityGeometry.BeurlingThreshold
import GaloisForLFunctions.MultiplicativePositivityGeometry.SiegelException
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralLatticeRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.FamilyCapacity
import GaloisForLFunctions.MultiplicativePositivityGeometry.LocallyFiniteBochner
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryRegularity
import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticBochner
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralLocallyFinite
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundarySummation

/-!
# Multiplicative Positivity Geometry

Umbrella for the positive-definite geometry of Euler log-coefficients.

* Boundary: even positive-definite functions on additive groups and the boundary positivity
  theorem; the simple-pole classification; the boundary divisor of ζ; realization by ζ-twists and
  one-prime factors; completeness and minimality of the four boundary invariants; the total zero
  mass law; the calculus of boundary data and the invisibility of the interior.
* Interior: the exact Fejér barrier, the two-sided growth-to-forcing law, the multi-frequency
  purchase cap and the de la Vallée Poussin calibration.
* Realization and range: integral Euler products (finite configurations and the lattice divisors
  over the rational primes), Bochner's theorem for finite and for locally finite configurations
  and its arithmetic form (one Dirichlet series over the integers),
  the zero capacity of a pole of order `k`, the positivity margin, the range of the boundary map
  and its Baire regularity (the simple-pole classification without local finiteness).
* Further mechanisms: families over finite abelian groups, the two-torsion exception, protected
  points and the exact family capacity; Rankin–Selberg Bessel forcing, the zero-mass law on abelian
  groups, the decay-exponent law and Beurling's threshold.

See `MultiplicativePositivityGeometry/README.md`.
-/
