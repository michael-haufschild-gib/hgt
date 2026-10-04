# The positive prime-update current escapes through its first band

- **ID:** pm-prime-update-positive-current
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); standard logical axioms only
- **Source:** Route PM; `pm-logarithmic-covariance-balance.md`; corpus searches195–199
- **Statement:** For fixed `0<epsilon<1/4`, the positive quadratic part of the literal prime-update energy grows at least as `P^(1-4*epsilon)/log(P)^3` at horizon `8*P^2`. On the first band beyond a prime aperture, the aperture source equals the full source plus an explicit positive prime sum, and the full source is uniformly negligible relative to that sum.

## Goal

Determine which cancellation a prime-update proof of PM admission must retain. This is an obstruction to a separate bound on the positive update current, not to the full signed current or RH. No source admission assumption is used.

## Gates

- [x] 0 → 1: actual coefficients, physical cutoff retained.
- [x] 1 → 2: dependency-closed paper proof below, using existing unconditional remainder and prime-window bounds.
- [x] 2 → 3: exact first-band survivor and quantitative current escape formalized and audited.
- [ ] 3 → 4: standalone exposition.

## Definitions

Fix `0<epsilon<1/2`. Write `A(t)` for `pmPowerDampedFermiSource epsilon t`. For a prime `p`, write `F_<p(t)` for `pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) epsilon t`. Define

`B_p(x) = sum_(q prime, p<=q<=x) q^(-epsilon)`

and `E_<p(X)=integral_(1/X,infinity) |F_<p(t)|^2 dt`, for `X>0`.

The positive quadratic prime-update current is

`Q_epsilon(N) = sum_(p prime<=N) p^(-2*epsilon) integral_(1/N,infinity) |F_<p(p*t)|^2 dt`

`              = sum_(p prime<=N) p^(-1-2*epsilon) E_<p(N/p)`.

Use `Q` here to distinguish this current from the divisor covariance in the logarithmic balance card.

## Paper proof [PROVED HERE]

### Exact first-band identity

For `p<=x<2*p`,

`F_<p(1/x) = A(1/x) + B_p(x)`.

Indeed, a positive integer `d<=x` with a prime factor `q>=p` must equal `q`: any proper multiple is at least `2*q>=2*p>x`. All coefficients other than the missing primes therefore agree. Each missing prime contributes `-q^(-epsilon)` to the full source, since `mu(q)=-1`, the Fermi indicator is `-1` on `q<=x<2*q`, and the source carries an outer minus sign. Subtracting those contributions gives the displayed identity. The same proof works for every integer aperture threshold `P>=1`, without assuming `P` prime.

### Uniform first-band cancellation

Existing `pmPowerDampedDivisorRemainder_eventually_log_four` gives

`|R_epsilon(n)| <= 1+C*n^(1-epsilon)/log(n)^4`

for all sufficiently large integers `n`. At real `x>=0`, the defining floor sum gives the exact identity

`R_epsilon(x)=R_epsilon(floor(x))-alpha_epsilon*(x-floor(x))`.

The correction is bounded, and powers and logarithms at `floor(x)` and `x` are comparable for sufficiently large `x`. Thus the same upper bound, with another constant, holds for all sufficiently large real `x`. The centered-difference identity

`A(1/x)=R_epsilon(x)-2*R_epsilon(x/2)`

implies uniformly for `3*p/2<=x<=7*p/4` that

`|A(1/x)| <= C_epsilon*p^(1-epsilon)/log(p)^4`.

The unconditional theta-window lower bound (`Sieve.exists_theta_window_lower`) and `primeShellCard_bounds` give, for all sufficiently large integers `p`, at least `c*p/log(p)` primes in `(p,3*p/2]`. To apply the window theorem take `x=p`, `h=p/2`, and exponent `3/4`; `(3*p/2)^(3/4)<=p/4` eventually. Each prime has weight at least `(3*p/2)^(-epsilon)`. Therefore throughout the same slab,

`B_p(x) >= c_epsilon*p^(1-epsilon)/log(p)`.

It follows that `|A(1/x)|/B_p(x) <= C'_epsilon/log(p)^3`, uniformly on the slab. In particular,

`F_<p(1/x)/B_p(x) -> 1`, `A(1/x)/B_p(x) -> 0`

uniformly, and `F_<p(1/x)>=B_p(x)/2>0` eventually. These sources are real: their definitions are finite sums of real coefficients and real Fermi indicators.

On the physical slab `I_p=[4/(7*p),2/(3*p)]`, let `b_p(t)=B_p(1/t)`. The pointwise relative bound implies, by integration,

`||F_<p||_(L2(I_p))^2 / ||b_p||_(L2(I_p))^2 -> 1`,

`||A||_(L2(I_p))^2 / ||b_p||_(L2(I_p))^2 -> 0`,

`Re <F_<p,-b_p>_(I_p) / ||b_p||_(L2(I_p))^2 -> -1`.

This is actual complete cancellation, retaining the mixed pairing. The slab length is `2/(21*p)` and lies above `1/(2*p)`. Hence

`E_<p(2*p) >= c''_epsilon*p^(1-2*epsilon)/log(p)^2`.

### Power escape of the actual positive update current

Put `N=8*P^2`. For primes `P<p<=2*P`, `N/p>=2*p`, so monotonicity in the integration horizon and the preceding bound give

`Q_epsilon(8*P^2) >= c''_epsilon sum_(P<p<=2*P) p^(-4*epsilon)/log(p)^2`.

The same theta-window lower bound supplies at least `c*P/log(P)` such primes. Since `p<=2*P`, all their weights are at least `(2*P)^(-4*epsilon)/log(2*P)^2`. Absorbing fixed constants yields

`Q_epsilon(8*P^2) >= c'''_epsilon*P^(1-4*epsilon)/log(P)^3`.

For `0<epsilon<1/4` and `0<=eta<1/2-2*epsilon`, division by `(8*P^2)^eta` leaves a positive power of `P` divided by `log(P)^3`, which tends to infinity. Thus neither a uniform budget nor a budget by every positive power can hold for this positive current separately.

### What the signed update must still prove

Insertion of `p` gives the exact finite-source update

`F_new(t)=F_old(t)-p^(-epsilon)*F_old(p*t)`.

At horizon `N`, successive insertion of all primes through `N` telescopes to

`integral_(1/N,infinity)|A(t)|^2 dt = seed_energy(N)+Q_epsilon(N)-2*M_epsilon(N)`,

where

`M_epsilon(N)=sum_(p prime<=N) p^(-epsilon) integral_(1/N,infinity) Re(F_<p(t)*conj(F_<p(p*t))) dt`.

The initial source is minus the parameter-one Fermi indicator, whose full energy is `log(2)`. The final finite source agrees with `A` above `1/N`. Thus the mixed current must cancel the positive current to the required accuracy. The lower bound for `Q` alone supplies no upper bound for the signed combination and no RH conclusion.

## No-go closure

- **Exact obstruction:** the preceding positive-power lower bound contradicts separate subpower control of `Q_epsilon` when `epsilon<1/4`.
- **Strongest positive survivor:** uniform asymptotic first-band cancellation, its exact source decomposition, and the resulting localized energy floor for the literal canonical prime core.
- **New insight:** the divergent positive update current is already forced by a physical prime slab. A successful proof must pay its mixed cancellation in the complete horizon-dependent update, rather than treating the quadratic increment as a summable cost.
- **Status:** exact decomposition, uniform relative cancellation, localized energy floor and current escape audited in Lean. The separate-current no-go is closed in `../5-failed/pm-separate-positive-prime-current-budget.md`. The strongest exported survivor is uniform pointwise relative approximation on the slab; the three integrated ratio corollaries above are paper consequences, not separate Lean exports. The full PM energy bound remains open.

## Lean certificate

All modules are under `formal/GaloisForLFunctions/RHTower/`.

- `PMPowerDampedMobiusPrimeSlab.lean`: `pm_primeFactors_aperture_first_band`, `pm_finitePrime_coefficient_first_band`, `pmFinitePrimePowerDampedFermiSource_eq_sum`, `pmFinitePrimePowerDampedFermiSource_first_band`.
- `PMPowerDampedMobiusPrimeSlabBounds.lean`: `pmPowerDampedFermiSource_prime_slab_bound`, `pmPrimeSlabMass_eventually_lower`, `pmPowerDampedFermiSource_prime_slab_relative_small`, `pmFinitePrimePowerDampedFermiSource_prime_slab_relative`, `pmFinitePrimePowerDampedFermiSource_prime_slab_eventually_lower`.
- `PMPowerDampedMobiusPrimeCurrent.lean`: `pmFinitePrimePowerDampedFermiSource_insert`, `pmPrimeCoreTruncatedEnergy_eventually_lower`, `pmPrimeUpdateQuadraticCurrent_eq_scaled_energy`, `pmPrimeUpdateQuadraticCurrent_eventually_lower`, `pmPrimeUpdateQuadraticCurrent_div_rpow_tendsto_atTop`.

The last theorem proves, for `0<epsilon`, `0<=kappa<1/2-2*epsilon`,

`Q_epsilon(8*P^2)/(8*P^2)^kappa -> infinity`.

Each module passed `lake env lean GaloisForLFunctions/RHTower/<module>.lean` with exit0 and empty diagnostics after its final source edit. Each targeted `lake --old build GaloisForLFunctions.RHTower.<module>` passed (leaf compile times142s,88s,164s respectively). No full or umbrella build ran. All eighteen exported theorems were audited via `/tmp` `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur. No new axioms, placeholders, numerical experiments or heartbeat overrides.

Each module is imported once by the RHTower umbrella. `scripts/formal_tools.py index` completed and registered the new exports. The final `scripts/formal_tools.py lint` reports thirteen unrelated unreachable modules, including the twelve previously recorded and `SuzukiMixedApertureMetricProfile`; none of the new PM modules is reported. This is not a global lint pass.

## Log

- 2026-10-04 — Derived from searches195–198 and direct source inspection. No numerical experiments. Created before Lean implementation. Search199 completed without a partial flag (inventory65228); all candidate and source statements inspected. Its useful hits cover finite-support extension and floor-source identification; no exact first-band identity was returned. The proposed ingredient group also included an unrelated cusp differential equation and was rejected. Compiler freshness remains mixed, semantic coverage unmeasured, background index refresh incomplete.
- 2026-10-04 — Formalization and audits completed. Search200 explores the unresolved paired square scale; it supplies no mixed-current estimate. Goal remains active: neither RH nor its negation is proved.
