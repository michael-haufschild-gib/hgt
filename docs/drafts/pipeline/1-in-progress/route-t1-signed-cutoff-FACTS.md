# Route T1 signed-cutoff facts

Own fact log for Route T1. Facts and no-gos only; `rh-current-frontier-map.md` remains read-only.

## Facts

- Corpus frontier already has exact coefficient identity `included = full - omitted`, exact LCM
  expansions for omitted base/cross/derivative moments, `O(N⁻²)` boundary errors at
  `L=N^100, M=N^49`, included-energy limit `ρ²/12`, and full-energy limit `2ρ²/3`, with
  `ρ=49/100`. Corpus search found no omitted-energy limit or cutoff Pythagorean law.
- At reciprocal tuning `λ·ell=1`, omitted polynomial energy cancels all lower min-log channels
  and equals exactly `λ² * selbergOriginalTunedMinLogRemainder M / log(M)²`. Same nonnegative
  Gram remainder controls included minimum-log sector.
- Actual omitted long energy at `λ=ρ/log M`, `L=N^100`, `M=N^49` tends `7ρ²/12`.
- Consequently `full energy - included energy - omitted energy → 0`: detector cutoff is
  asymptotically Pythagorean. Included and omitted coefficient sectors become orthogonal in the
  harmonic-energy polarization, and `1/8 + 7/8 = 1` is an orthogonal mass split rather than an
  uncontrolled signed loss.
- Lean certificate:
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedTunedEnergy`.
- Retaining omitted pair endpoint `L * max(q,r)` replaces kernel error denominator `L` by
  `L * max(q,r)` and weakens pointwise scale assumption from `8*M² ≤ L` to `8*M ≤ L`.
  Absolute Barban--Vehov reciprocal-max mass satisfies
  `Σ_{q,r≤M}|w_q w_r|/max(q,r) ≤ M log(M)²(1+log M)`.
- Therefore omitted normalized base/cross/derivative moments at exact quadratic horizon
  `M=N^49`, `L=N^98=M²` have explicit common decay `(1+49 log N)/N^49`, with constants
  `3`, `19`, and `110`.
- Actual omitted long energy at exact quadratic-horizon reciprocal tuning
  `λ=(1/2)/(49 log N)` tends `7/48`. Thus seven-eighths sector remains controlled and retains
  full predicted mass at horizon; strict `M²/L` slack was an artifact of erasing moving lower
  endpoint, not an intrinsic omitted-sector barrier.
- Lean certificates:
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedQuadraticHorizonError` and
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedQuadraticHorizonEnergy`.
- Exact taper structure improves the corpus's crude `Σ|w_q| ≤ M log M` estimate to
  `Σ_{q≤M}|w_q| ≤ M`; consequently `Σ_{q,r≤M}|w_qw_r| ≤ M²`. This follows from
  `|w_q| ≤ log M-log q` and the Stirling lower bound for `Σ log q`.
- Splitting lcm fibres at `8*lcm(q,r) ≤ L` removes the uniform scale wall. Small fibres use the
  sharp continuous-kernel estimate; large fibres combine the unconditional exact-to-floor-main
  estimate with `1/lcm(q,r) ≤ 8/L`. Uniform errors through the full horizon `lcm(q,r) ≤ L`
  are `322/L`, `2000(1+log(U+1))²/L`, and `20000(1+log(U+1))²/L` for the base,
  first-log, and second-log kernels.
- Combining hybrid fibre bounds with exact linear weight mass gives full and included
  base/cross/derivative continuous approximations under the exact condition `M² ≤ L`, with no
  `8*M² ≤ L` slack.
- At `M=N^49`, `L=N^98=M²`, reciprocal tuning `λ=(1/2)/(49 log N)`, actual full,
  included, and omitted detector energies tend respectively `1/6=8/48`, `1/48`, and `7/48`.
  Thus the `1/8`--`7/8` orthogonal mass split survives exactly on the square-root boundary.
- Lean certificates:
  `GaloisForLFunctions.RHTower.Sieve.BarbanVehovLinearL1`,
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovQuadraticHorizonError`,
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovQuadraticHorizonEnergy`, and
  `GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedQuadraticHorizonEnergy`.
- Corpus already contains exact co-moving coordinate projection, prime-sieve operator, source
  residue normalization, summable nested sieve transitions, mass cone, and two-aperture prime
  secant after supplied true-prime projection. Missing object is not another abstract co-moving
  sieve but a source-native producer preserving signed ordinary/omitted interference through
  moving Vaughan/AFE/layer-cake and fixed Weil landing.
- Every finite packet of legal moving true-prime cone depths has one scalar invariant modulo
  uniformly bounded vertical families: its total coefficient charge `sum alpha`. Relative to any
  legal reference depth, the packet differs from `(sum alpha)` times that reference cone by a
  uniformly bounded family. Zero charge is therefore unconditionally bounded; nonzero charge is
  equivalent to RH boundedness.
- For reciprocal Levinson aperture families, rough-tail prime correctness forces the affine
  intercept to vanish, and that intercept is exactly `sum alpha`. Hence any finite co-moving depth
  realization using the same detector coefficients is automatically zero-charge and
  unconditionally bounded. Prime extraction and retention of the RH-bearing cone class are
  incompatible inside this entire finite architecture.
- Lean certificate:
  `GaloisForLFunctions.RHTower.XiMassLevinsonComovingDepthChargeNoGo`.
- True-prime filtering is unnecessary for fixed-Weil landing. Set the Levinson differential
  parameter to zero, restore its `log M` normalization, and co-move `M` with the rounded Xi-mass
  cone cutoff. On every active index `n≤M`, the Barban--Vehov coefficient is exactly `Λ(n)`;
  therefore the literal unprojected detector packet equals the moving prime-power atom cone at
  every height. Its line bound is exactly equivalent to the fixed critical half-density Weil
  pairing line bound, hence to RH.
- This closes T1's coefficient-faithful source-to-fixed-Weil landing gate without a supplied
  true-prime projection, prime-power subtraction, growing log-symbol type, or singular filter.
  Remaining hard gate is to derive the zero-jet packet's eventual uniform vertical bound from an
  unconditional signed full-minus-omitted source estimate; the existing reciprocal-tuned energy
  asymptotics do not supply that bound.
- Lean certificate:
  `GaloisForLFunctions.RHTower.XiMassLevinsonComovingZeroJetLanding`.
- Opposite reciprocal Levinson jets recover the zero-jet value channel exactly, coefficient by
  coefficient and before applying any moving cutoff:
  `(log M / 2) * (D_(1/(2 log M)) + D_(-1/(2 log M))) = log M * D_0`.
  The same polarization identity holds separately for full head, omitted head, and their exact
  finite-product difference. Thus reciprocal differentiation, signed full-minus-omitted structure,
  and fixed-Weil landing are compatible; no sector is discarded to obtain the landing.
- At the Xi-mass co-moving aperture, this paired reciprocal packet equals the zero-jet packet and
  hence the critical prime-power atom cone at every height. Its eventual line bound is equivalent
  to RH. T1's remaining obstruction is therefore not source/receiver mismatch: it is the
  unconditional, phase-sensitive vertical bound for this exact paired packet.
- Lean certificate:
  `GaloisForLFunctions.RHTower.XiMassLevinsonSymmetricReciprocalLanding`.
- The fixed-Weil-normalized opposite reciprocal pair has short coefficient energy exactly
  `Σ_{2≤n≤M} Λ(n)²/n`. Its ratio to `log(M)²` tends to `1/2`; consequently the energy
  tends to infinity and admits no aperture-independent upper bound.
- This rules out the whole class of coefficient-blind positive-`L²` transfers for the exact T1
  packet. The surviving bound mechanism must retain vertical phases/covariance (or an equivalent
  analytic cancellation); improving separate full/omitted positive energies cannot close RH.
- Lean certificate:
  `GaloisForLFunctions.RHTower.XiMassLevinsonSymmetricReciprocalEnergyNoGo`.

## No-gos

- Treating omitted head as a small error is false: it carries asymptotic mass `7ρ²/12`, seven
  eighths of full energy.
- Triangle/Cauchy on `full - omitted` destroys the decisive projection geometry. Any T1 transfer
  using only separate nonnegative full/omitted upper bounds cannot recover the sharp included
  receiver; it must transport the signed projection or equivalent orthogonality law.
- Prime-zeta/Möbius exponent inversion is already formalized and does not remove this obstacle:
  corpus already has true-prime projection, while unresolved step is moving the orthogonal cutoff
  sector into source-faithful AFE/Weil pairing.
- A direct scale-free full-sector estimate through `Σ|w_qw_r|/lcm(q,r)` remains too large under
  known absolute bounds. It is not an intrinsic horizon obstruction: the hybrid small/large-fibre
  split plus exact linear weight mass bypasses it and closes normalized full/included errors at
  `L=M²`.
- Naive cofinal prime sieve collapses source residue to zero; density renormalization recovers only
  original residue. Fixed finite aperture/order/type remains killed by rough-tail prime-square
  leakage. Exact quadratic-horizon omitted control does not itself supply prime-power subtraction,
  growing/singular analytic type, or coefficient-faithful fixed Weil landing. Exact quadratic-
  horizon control for all three sectors does not remove this source-to-Weil transport obstacle.
- Cutoff differentiation, aperture secants, and every other finite prime-correct co-moving depth
  combination have zero total cone charge. Their quadratic-horizon prime annulus is a bounded
  coboundary, not an RH carrier. A viable T1 producer must break the finite charge/intercept
  identification: e.g. a singular or non-absolutely-summable aperture limit whose coboundary
  budgets do not sum, or a separate nonzero-charge source channel plus bounded composite removal.
- One-sided reciprocal-tuned coefficient-energy limits do not bound the paired source: after
  polarization the normalization changes to the zero-jet/prime-power channel. Separate nonnegative
  energy bounds also lose the cross-phase term, and mean-square control alone cannot imply the
  required uniform vertical line bound. Any successful transfer must retain signed covariance or
  exploit analytic propagation with a quantitatively adequate bandwidth cost.
