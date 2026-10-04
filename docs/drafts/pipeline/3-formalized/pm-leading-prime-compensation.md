# PM leading compensation of the complete signed prime current

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; complete signed compensation.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeCompensation.lean`.

## Exact results

For every 0<epsilon<1/2, the actual full-source truncated energy satisfies

`E_epsilon(N)*log(N)^4/N^(1-2*epsilon) -> 0`.

For every sufficiently small positive epsilon and every delta>0, eventually
in natural P,

`(1-delta)*Mminus_epsilon(8P^2) <= Mplus_epsilon(8P^2)`.

Both currents use the complete actual weighted prime mixed density and the
same physical horizon. No canonical L2 admission or RH premise is assumed.
This is a one-sided leading compensation law; it does not assert that the
ratio tends to one or that the difference is bounded.

## Proof

Exact inversion transports the finite physical energy to the integral of
`g(x)=norm(A_epsilon(1/x))^2/x^2` over 0<x<N. The previously audited source
envelope gives `g(x)<=C*x^(-2*epsilon)/log(x)^8` beyond a fixed R>=e.
For N>=R^2, retain the compact head and split the remaining integral at
sqrt(N). With a=1-2*epsilon>0 this gives

`E(N)<=E(R)+(C/a)*N^(a/2)+(256*C/a)*N^a/log(N)^8`.

Logarithms versus positive powers prove the normalized limit. At N=8P^2,
the audited negative-current lower bound is
`Mminus(N)>=c*(2P)^(2-4*epsilon)/log(2P)^4`.
The exact scale identity N=2*(2P)^2 and log monotonicity make E(N) at most
2*delta*Mminus(N) eventually. The complete signed identity
`E=seed+Q-2*(Mplus-Mminus)`, together with seed>=0 and Q>=0, proves the law.

## Audit

- Two public exports; wired once into RHTower and both indexed.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeCompensation:olean` passed, only this leaf newly built (26s).
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeCompensation.lean` passed with empty output.
- Separate `/tmp` axiom audit: both exports use only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint reports twelve unrelated unreachable modules and no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, resource-limit increase, full build, umbrella build, commit or push.

## Remaining hard problem

The required lower bound for `Mplus-Mminus-Q/2` is still open. The proved
energy bound has a positive power of N for small epsilon and does not
establish subpower growth, canonical L2 admission, RH or its negation.
