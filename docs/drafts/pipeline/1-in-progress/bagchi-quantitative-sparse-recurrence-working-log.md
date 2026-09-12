# Bagchi sparse recurrence — working log

Updated: 2026-09-12. Scope: facts and no-gos established during this research thread. No proposals.

## Facts

- **F01 — Receiver only.** `RecurrenceZeroDensity.lean` proves abstract zero transfer/counting
  contradiction from supplied recurrence and zero-count inequalities; it does not produce zeta
  recurrence.
- **F02 — Finite torus cost.** Finite prime-phase return volume is of order `epsilon^d`; available
  deterministic delay is `(Q+1)^d` at error `2*pi/(Q+1)`.
- **F03 — Current zero-density range.** Actual Lean strict-right zeta zero count begins at
  `sigma=7/10`, with exponent at most `(16/5)(1-sigma)`. No corpus theorem wires Huxley large values
  to a zeta zero count for every `sigma>1/2`.
- **F04 — Uniform winding gap.** One actual Xi circle around a critical-line zero has nonzero
  winding and a fixed positive sup-distance from every continuous periodic zero-winding loop.
  Evidence: `exists_xiBoundaryLoop_zeroWinding_uniformGap`.
- **F05 — Fixed-scale AFE bounds.** Available displaced Gaussian-AFE estimates give deep reflected
  tail `C*L^(-1)+D*(1+|tau|)^4*L^(-7/2)` and classical-head replacement error
  `E*|tau|^(-eta)*(1+L^(1/2+eta))`, `0<eta<=1/4`.
- **F06 — Phase-cell resonances survive.** Conditioned Bohr mean of every integer frequency
  supported on conditioned primes equals its positive Fejer multiplier
  `product_p(1-v_p(n)/(N_p+1))`, bounded below by `product_p(N_p+1)^(-1)`.
- **F07 — Exact dual target.** At fixed `x>0`, with direct edge `D`, dual edge `M`, pole residue `R`,
  `M(t)-(M(s)+R(s))=(D(t)-D(s))-(zeta(t)-zeta(s))-R(t)`. Direct recurrence plus `R(t)->0`
  makes zeta recurrence equivalent to synthesis of target `M(s)+R(s)`. Evidence:
  `RHTower.SmoothAFEZetaGeneralSelfRecurrenceDualNecessity`.
- **F08 — Terminal scale.** At `Re(s)=1/2+d`, fixed-`x` dual length is comparable to `T/x`;
  chi size `T^(-d)` times coefficient square mass `N^(2d)` gives order-one full-block variance.
  Any head `N=T^alpha`, `alpha<1`, has normalized variance `T^(-2d(1-alpha))`.
- **F09 — Prime-only shell.** Primes in `(N/2,N]` have total radius of square-root order divided by
  `log T`, but variance of order `1/log T`.
- **F10 — Exact largest-prime carrier decomposition.** For arbitrary complex `a` and `X<Y^2`,
  `sum_{n<=X} a_n X_n = B_Y + sum_{Y<p<=X} X_p C_p`, with
  `C_p=sum_{m<=X/p}a_(pm)X_m`. Every cofactor satisfies `m<Y`; `B_Y` and `C_p` read only phases at
  primes `<=Y`; channel prime `p` is outside that set. Evidence:
  `RHTower.SteinhausLargestPrimeDecomposition`.
- **F11 — Complex Steinhaus Parseval.** For finite nonzero support and arbitrary complex
  coefficients, `E|sum a_n X_n|^2=sum|a_n|^2`. Evidence:
  `RHTower.SteinhausComplexSecondMoment`.
- **F12 — Exact channel-energy partition.** Expected squared energies of all largest-prime channels
  equal coefficient square mass of the non-`Y`-smooth sector. Evidence:
  `steinhausCoefficientMass_eq_smooth_add_largePrimeChannelEnergy`.
- **F13 — Axiom audit.** F07, F10, F11, F12, F15, and F16 depend only on `propext`,
  `Classical.choice`, and `Quot.sound`; targeted builds pass.
- **F14 — Dense-support Gaussian warning.** arXiv:2605.21737 proves, in its random multiplicative
  setting, that its standard complex-Gaussian CLT forces sparse support; it does not exclude a
  Gaussian mixture or direct full-support law.
- **F15 — Variable-cofactor channel floor.** For `0<d<1/2`, prime `p` with `2p<=N`, and normalized
  model weight `N^(-2d)n^(-(1-2d))`, the dyadic cofactor block `N/(2p)<m<=N/p` contributes at least
  `((1/2)/2^(2d))/p`. Evidence: `normalized_power_channel_lower_recip`.
- **F16 — Positive ideal terminal mass.** Summing F15 over primes between the half- and
  two-thirds-power cuts gives an eventual positive normalized lower bound. Their reciprocal mass
  tends to `-log(1/2)+log(2/3)=log(4/3)>0`. Evidence:
  `eventually_normalized_power_terminal_channels_lower`.

## No-gos

- **N01 — Zero-free finite Euler carrier plus uniformly vanishing tail.** Impossible on a decisive
  zero-enclosing boundary by F04.
- **N02 — Ordinary universality with shrinking slit, current input.** Missing-arc winding control
  requires an exterior zero-free buffer; no uniform shrinking-compact density estimate is present.
- **N03 — Fixed-scale AFE power truncation.** `L=T^a` requires simultaneously `a>8/7` from deep tail
  and `a<eta/(1/2+eta)<=1/3` from conductor localization.
- **N04 — Fixed-`d` generalized recurrence then `d->0`, current input.** No uniform onset/count on
  intervals of length `O(1/|d|)`; fixed-parameter density does not supply required near-identity
  shift.
- **N05 — Whole-interval tail-good set plus phase-return set.** Separate positive-measure statements
  do not force intersection; any conclusion reducing to N01 is impossible.
- **N06 — Recent shrinking-target transfers inspected.** IID Haar thinning and mixing-map
  metastability do not apply to deterministic irrational prime flow or couple to zeta tails.
- **N07 — Vitali from available moments on phase cells.** Cell mass decays exponentially in prime
  dimension while right-half-plane truncation improves only polynomially; second/fourth moments do
  not yield local boundedness on selected cells.
- **N08 — Naive conditioned diagonal mean square.** False by F06: all smooth-ratio cross terms retain
  positive multipliers.
- **N09 — Coordinatewise terminal targeting at same height.** Polynomially many terminal phases
  give superpolynomial return delay; logarithmically many phases give vanishing total amplitude.
- **N10 — Prime-only terminal synthesis as order-one variance source.** False by F09; it is a
  moderate-deviation problem.
- **N11 — Standard dense-support complex-Gaussian CLT as default target.** Unsupported and contrary
  to F14 in the paper's setting; no general impossibility beyond that setting is claimed.
- **N12 — Fixed-cofactor subterminal channel.** At `Re(s)=1/2+d`, `d>0`, a channel with fixed
  cofactor and primes `p<=T^theta`, `theta<1`, has normalized square mass at most logarithmic factors
  times `T^(-2*d*(1-theta))`; it vanishes. Constant reciprocal-prime mass at `d=0` does not solve
  recurrence on a compact containing a zero with fixed positive displacement.
- **N13 — Marginal small-ball bounds as simultaneous boundary control.** False as a general
  principle: arXiv:2609.11795 constructs fixed-direction small-ball lower bounds with catastrophic
  failure after searching over a low-Gaussian-width family. C15 needs a joint finite-node law or a
  proved complexity/occupancy bound, not nodewise estimates alone.
- **N14 — Shifted anticoncentration as target recurrence.** arXiv:2609.06526 gives uniform *upper*
  small-interval bounds for a conditional Gaussian scale mixture by controlling inverse conditional
  variance. C15 needs a *lower* probability near its prescribed planar target; the theorem's model
  and inequality direction do not supply it.
