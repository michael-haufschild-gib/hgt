# PM uniform negative prime-square source

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeSquareSign.lean`.
- **Frontier effect:** the previously unresolved paired core is uniformly negative on the actual square slab. Complete signed-energy compensation remains open.

## Exact theorem

For every sufficiently small positive epsilon, some c>0 satisfies, for
every sufficiently large natural P and every `3/2<=y<=7/4`,

`Re F_<P,epsilon(1/(y*P^2)) <= -c*(y*P^2)^(1-epsilon)/log(y*P^2)^2`.

The theorem is eventual in the right neighborhood of zero; all estimates
refer to the literal canonical finite-prime source. No RH, zero-free-strip
or L2-admission premise is used.

## Proof

The exact square-scale decomposition has three terms. The full source is
negligible under normalization by `log(X)^2/X^(1-epsilon)`. The actual
prime convolution tends uniformly to `-Re(D_epsilon)`, using lower cutoff
P-1 so that a prime P is retained. For the square-inclusive composite mass,
the endpoint-correct theta comparison gives

`J*log(P)/P <= y-1+delta*(y+1)+1/P`.

The unordered-pair bound, including its diagonal, then gives normalized
limsup at most `(7/4)^epsilon*9/14`, uniformly on the slab. The exact
polynomial inequality `2*(y-1)^2 <= (9/14)*y` supplies this coefficient.
Finally `D_epsilon -> log(2)` and `log(2)>2/3` give the strict gap.
The proof uses the existing Lean log-two inequality, no numerical experiment.
Counting, convolution and remainder errors are all retained and absorbed
inside the gap.

## Audit

- Three exports: endpoint-correct interval count, uniform rough-mass upper bound, actual negative core.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSquareSign:olean` passed; only this leaf newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeSquareSign.lean` passed with empty output.
- All exports have only `propext`, `Classical.choice`, `Quot.sound` in the separate `/tmp` axiom audit.
- Wired once, indexed; no umbrella build. Global lint reports nineteen unrelated unreachable modules and no PM failure, not a global lint pass.
- No new axiom, placeholder, resource-limit increase, commit or push.

## Remaining hard problem

The paired first-band factor is positive, so the mixed update has a
negative contribution on this slab. Quantifying its integrated mass is
next. The global lower bound for `M_epsilon(N)-Q_epsilon(N)/2`, or a
suitable complete signed subpower estimate, remains unresolved.
