import GaloisForLFunctions.SmoothBernoulliPoleCalibration.HigherOrderKernelStatisticAndDualNorm
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.SmoothTaperedCrossScaleDispersion
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.EvenPoleCalibrationAndLogMomentPinning
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.MasterSmoothBernoulliPoleCalibrationTheorem

/-!
# Smooth-Tapered Higher-Order Bernoulli Elimination and Even-Pole Calibration

Umbrella module for `GaloisForLFunctions.SmoothBernoulliPoleCalibration`, formalizing Mechanism 2
of Project Argon (`docs/reports/review-2110/argon.md`, §1.3): higher-order cross-scale dual-norm
attainment, smooth-tapered elimination of the polynomial Bernoulli tower beyond the sharp-cutoff
`θ = 4/3` barrier, simultaneous odd–even pole calibration for even-flip cofactor pairs, and
logarithmic moment pinning across the generalized Fermi horizon.

See `GaloisForLFunctions/SmoothBernoulliPoleCalibration/README.md` for the module ledger and
theorem summary.
-/
