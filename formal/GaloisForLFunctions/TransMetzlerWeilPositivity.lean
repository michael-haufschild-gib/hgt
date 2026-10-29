import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters
import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerDecomposition
import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerPositivity
import GaloisForLFunctions.TransMetzlerWeilPositivity.OptimizedTransMetzlerFloor
import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerReferenceFloor
import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerYoungOptimization
import GaloisForLFunctions.TransMetzlerWeilPositivity.LiouvilleTwinSelectivity
import GaloisForLFunctions.TransMetzlerWeilPositivity.ZeroSideStratum
import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth
import GaloisForLFunctions.TransMetzlerWeilPositivity.TheFixedProfileReachesAnIteratedLogEndpoint
import GaloisForLFunctions.TransMetzlerWeilPositivity.FixedOverlapHasLogarithmicDivisorRows
import GaloisForLFunctions.TransMetzlerWeilPositivity.CompleteWeilLengthHeight
import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyLengthHeight
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.ElevenFlipAtEveryHorizon
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.LogarithmicBandMass

/-!
# Trans-Metzler Complete Weil Positivity and the Overlap-Ratio Phase Diagram

Umbrella for the theory of atomic Weil positivity across and beyond the Metzler overlap threshold
`c = 1`:

* explicit plateau parameters, Lipschitz and variance-reserve bounds, completed Robin margin, and
  Robin–Euler threshold for `transMetzlerProfile = plateau (1 / 1000)` (`ExplicitPlateauParameters`);
* perturbative decomposition of `normalizedFullWeilHorizonMatrix` past touching into the Hermitian
  reference operator `transMetzlerMainMatrix` and top-collar archimedean and successor-prime
  perturbations (`TransMetzlerDecomposition`);
* unconditional complete Weil positive definiteness across `(0, cZero]` (`cZero = 1 + 10⁻¹⁸ > 1`)
  and simultaneous positive definiteness and unimodular Markov gauge frustration at
  `rhoZero * atomSpacing N` (`TransMetzlerPositivity`);
* optimal interpolation of the certified reference, coercivity and perturbation bounds, giving
  every strict floor below `1/25 - 2000 * 2150400040961 * δ` at overlap `1+δ`, positive for
  `δ < 1/107520002048050000` (`OptimizedTransMetzlerFloor`);
* exact conductor-one reference floor and full Young-parameter optimization: a unique zero of the
  certified floor characterizes this bound family's positive range; at `c = 1 + 10⁻¹⁶` the actual
  complete matrices eventually have floor `1/400` (`TransMetzlerYoungOptimization`);
* Fejér–Abel center floor, bounded-pole hyperplane witnesses, and breakdown of the Liouville twin
  above the Robin–Euler ratio `exp(β(φ)/‖φ‖₂²) / (2π) < 1/2` (`LiouvilleTwinSelectivity`);
* zero-side implications under `RiemannHypothesis` and finite off-line support, sharp linear-in-`c`
  single-zero lower bound, and the `isolatedPairConfig` countermodel at every overlap ratio
  (`ZeroSideStratum`);
* explicit Steklov infinite-convolution Denjoy–Carleman profile `steklovDCProfile` and RH
  equivalence at overlap ratio `(log log N) (log log log N)^β` (`β > 2`) strictly below all Gevrey
  power schedules (`SuperGevreyCriticalGrowth`).

See `TransMetzlerWeilPositivity/README.md`.
-/
