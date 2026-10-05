# BAG exact critical physical cubic atom identity

- ID: C28.56ag.3, continuation01a7.
- Route: complete signed physical BAG cubic.
- Status: three production leaves and all24 public declaration axiom audits
  passed. Global lint has33 unrelated unreachable-module errors.
- Paper: ../2-fully-proven/bag-critical-physical-cubic-atom-identity.md.
- Parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.

## Exact advance

For EVERY real N>=1 the original `primeGaussianCubicOffDiagonal N` equals
the full critical rational atom tensor acting on an explicit finite Fourier
test with both literal contraction projectors. The capstone is
`RHTower.BAGTrace.primeGaussianCubicOffDiagonal_eq_criticalAtomAction` in
ChiPrimeGaussianCubicCriticalAtoms.

At P=range(floor(2N)+1), the source is the convolution of the literal
critical divisor atoms -mu(d)*log(d)/d at a/d with the square-divisor atoms
mu(d)/d^2 at b/d^2. Every pair and every rational node remains. Its Fourier
coefficient on each covered integer above one is EXACTLY the prime
logarithm; there is no damping parameter or composite approximation.

The test contains every integer triple in the actual band and the complete
`primeGaussianCubicMainEntry`, divided by its three logarithms. It contains
no prime mask or equality mask. Rational translations by (a/D,0,-a/D) and
(0,b/D,-b/D), D=floor(2N)+1, project exactly onto p=r and q=r on this band.
Their complementary composition removes both families and restores their
intersection. Logarithms cancel only on primes, where they are nonzero.
Every physical W/V factor, conjugation, reciprocal r and phase remains.

The complete dual phase identity and mixed double-translation term are
also formalized. With delta=z-x*y, the latter is
delta-(1+y)*a-(1+x)*b-a*b; the mixed term is retained.

## Files and audits

- ChiRamanujanCriticalFiniteAtoms: 6 public declarations, audit23109 exit0.
- ChiRamanujanFiniteContractionProjectors: 11 declarations, audit69239 exit0.
- ChiPrimeGaussianCubicCriticalAtoms: 7 declarations, audit21647 exit0.

Every final command was `lake --old env lean <leaf> -o <olean>`, one owned
foreground Lean process at a time. Final logs have no diagnostics. All24
declarations passed /tmp axiom audit90494: only propext, Classical.choice
and Quot.sound, no diagnostics. Concrete new mathlib APIs were probed in
/tmp; universe-inference and deprecated-name probe failures were corrected.

Index19426 exited0; every public name is present in LEAN_API. Each of the
three umbrella imports occurs exactly once. Lint43522 exited1 with33
unrelated unreachable modules and no proof-debt or reachability finding for
these leaves. Global lint is not clean. All owned jobs are terminal;
completed scratch sources were removed, with logs and search JSON retained.
No numerical experiment, new axiom, heartbeat increase, full/umbrella build,
subagent, commit or push occurred.

## What remains hard

This closes the complete ADDITIVE finite physical matching step, including
literal contractions. It does not identify these finite translation
projectors with the axes of the multiplicative six-zeta trace, and it does
not prove any signed asymptotic saving.

The next target is the actual normalized growing atom action at
o(N/log(N)^2), using its full phase, every integer lift, the entire
finite-height near-cone neighborhood and all tails. The smooth-edge corpus
is available for a complete Poisson/stationary analysis; fixed-test
convergence or generic energy/flatness estimates do not prove this target.
Growing moments, moving cofactors, positive common-height self-return and
RH remain open. Overall goal ACTIVE.
