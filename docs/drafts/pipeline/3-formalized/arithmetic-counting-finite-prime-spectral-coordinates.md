# Finite-prime counts determine actual conductor coordinates

- **ID:** ACP-FINITE-PRIME-SPECTRAL-COORDINATES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean audited)
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Statement:** For every finite set of primes and every positive conductor, exact signed harmonic counts determine the limiting squared coordinate on the corresponding actual simple prime eigenline.

## Data and endpoints

Let F be a finite prime set, omega_F its sign, c_F its product harmonic density,
b_F=mu*omega_F its Möbius transform on positive integers, and
`a_F(m)=c_F b_F(m)/sqrt(phi(m))`. At horizon N define

`C_(F,m)(N)=sum_(n in [1,N]) omega_F(n)c_m(n)/n`,
`v_(F,N)(n)=omega_F(n)/(sqrt(n)*sqrt(H_N))`.

The normalized Ramanujan mode u_(m,N) uses the same factor sqrt(H_N).
For every positive m the conclusions are

`C_(F,m)(N)/H_N -> c_F b_F(m)`,
`<v_(F,N),u_(m,N)> -> a_F(m)`.

There is an isolating energy window about the actual adjunction energy E_m
which has exactly one eigenline eventually. Uniformly over its index i,

`|<v_(F,N),e_i>|^2 -> a_F(m)^2`.

In particular an actual eigenline sequence on horizons N+1 has energy
converging to E_m and squared constraint coordinate converging to a_F(m)^2.
Every endpoint quantifies a fixed finite F and fixed conductor m; no horizon
uniformity in growing F or m is assumed or asserted.

## Closed proof

### 1. Exact count and decimation

Möbius inversion gives `c_m(n)=sum_(d|m) mu(m/d)d 1_(d|n)`.
Interchanging the two finite sums is exact. Multiplicativity on the fibre
n=dr gives

`sum_(n<=N) omega_F(n)d 1_(d|n)/n
 = omega_F(d) S_F(floor(N/d))`.

Therefore

`C_(F,m)(N)=sum_(d|m) mu(m/d)omega_F(d) S_F(floor(N/d))`.

The finite-prime density theorem supplies K>=0 with
`|S_F(M)-c_F H_M|<=K` for all M. For fixed d>0 the harmonic shell satisfies
`0<=H_N-H_floor(N/d)<=1+log d`. Since c_F>0,

`|S_F(floor(N/d))-c_F H_N|<=K+c_F(1+log d)`.

Division by H_N, which tends to infinity, proves the decimated limit c_F.
Taking the finite divisor sum yields the first endpoint, using the literal
Möbius divisor formula for b_F.

### 2. Harmonic normalization

The signs square to one, so v_(F,N) has norm one for every N>=1. The existing
normalized Ramanujan profile is `c_m(n)/(sqrt(phi(m))*sqrt(n))` before harmonic
normalization. Multiplying its coordinates by those of v_(F,N) gives exactly

`<v_(F,N),u_(m,N)>=C_(F,m)(N)/(H_N sqrt(phi(m)))`.

The first endpoint therefore gives the inner-product limit a_F(m). This
identity remains literal at each finite horizon; no limiting operator is used.

### 3. The actual spectral projection

Fix any positive window radius delta about E_m and let P_(m,N,delta) be the
actual prime-matrix spectral projection of u_(m,N) into that window.
The previously proved harmonic Ramanujan residual estimates give

`||u_(m,N)-P_(m,N,delta)||^2 -> 0`,
`||P_(m,N,delta)||^2 -> 1`.

Cauchy–Schwarz and ||v_(F,N)||=1 show that replacing u by P changes the
mixed inner product by a quantity tending to zero. Hence

`<v_(F,N),P_(m,N,delta)>^2 / ||P_(m,N,delta)||^2 -> a_F(m)^2`.

The actual simple-spectrum theorem supplies delta>0 such that this window
has one eigenline eventually and every eigenvalue in it tends to E_m.
If e_i spans this line, then P=<u,e_i>e_i. Its squared norm tends to one,
so its coefficient is nonzero eventually. Cancelling that coefficient shows
that the preceding quotient is exactly `<v_(F,N),e_i>^2`. This identifies
the actual squared coordinate without making an orientation choice.

### 4. A concrete eigenline sequence

Use horizons N+1, whose index types contain 1. At every horizon with a
nonempty isolating window choose an index in it; at the remaining horizons
choose 1. The singleton count makes the first choice apply eventually.
The uniform energy and coordinate estimates inside the window then give
the two limits for this concrete sequence. The arbitrary early choices
have no effect on either limit.

## Scope

The proof extends the existing single-prime counting bridge, reusing its
gauge-independent quasimode and projection theorems. The coefficients come
from an unconditional finite-prime count. The separate unit-mass theorem
will control omitted conductors in the later full resolvent transfer;
this fixed-conductor result does not itself assert the joint optimal gap.
No approximation of a full spectrum by one selected eigenline is assumed.

## Formalization

Source: `formal/GaloisForLFunctions/ArithmeticCountingPositivity/FinitePrimeCountsDetermineTheConductorCoordinates.lean`.

Eight public endpoints:

- `finiteFlipRamanujanSum_eq`
- `finiteFlipRamanujanSum_tendsto`
- `finiteFlipHorizonVector_norm_sq`
- `finiteFlipHorizonVector_inner`
- `tendsto_finiteFlipHorizonVector_inner`
- `tendsto_finiteFlipWindowCoordinateSq`
- `exists_finiteFlip_eigenline_coordinates`
- `exists_finiteFlip_conductor_eigenline`

Scratch check 44835 and canonical source check 96499 exited zero without
diagnostics. Every transitive axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`. Exact commands, source hash and actual
output are in the adjacent audit. The umbrella and foundational README are
wired; no umbrella was compiled. Owned scratch/check logs are cleaned.

- [x] Dependency-complete paper proof.
- [x] Eight Lean endpoints and transitive axiom audit.
- [x] Canonical source audit, wiring, durable evidence and cleanup.
