# Q6.2 -- both-disconnected quadratic Bottcher independence

- **ID:** q62-both-disconnected
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / bridge subcase
- **Parent theorem:** `q62-bottcher-independence-n2-all-parameters.md`

## Statement

Let `f_c(z)=z^2+c`. For `c notin M`, let `phi_c` be Nguyen's Bottcher
coordinate `psi_c^-1`, normalized by

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`.

If `c1 != c2` and both parameters lie outside the Mandelbrot set, then
`phi_c1(z)` and `phi_c2(z)` are algebraically independent over `C(z)`.

## Proof

Assume a nonzero relation

`P(z,phi_c1(z),phi_c2(z))=0`

for the common germ near infinity.

### Separation

For `c notin M`, `K_c=J_c` is a Cantor compactum and has logarithmic capacity
`1`. We first show `K_c1 notsubset K_c2`.

If `K_c1 subset K_c2`, then the equilibrium measure of `K_c1` is a probability
measure on `K_c2` with minimal logarithmic energy `0`, because both compacta
have capacity `1`. By uniqueness of equilibrium measure, `mu_c1=mu_c2`. Since
the equilibrium measures have full support on the Cantor Julia sets, this gives
`K_c1=K_c2`. The normalized exterior Bottcher map is then the same for both
parameters, and its Laurent coefficient `c/(2z)` recovers `c`, so `c1=c2`, a
contradiction.

Choose `z0 in K_c1\K_c2` and a disk `D subset Omega_c2=C\K_c2` around `z0`.
Since `K_c1` is a hyperbolic Cantor repeller, symbolic cylinders shrink to
points. For arbitrarily large `n`, choose a depth-`n` cylinder

`C_w subset K_c1 cap D`.

### One-coordinate monodromy

The exact monodromy theorem `bottcher-exact-pruefer-monodromy.md` gives a based
loop `gamma` in `D\K_c1` whose continuation sends

`phi_c1 -> exp(2*pi*i/2^n) phi_c1`.

The same loop fixes `phi_c2`: it lies in the disk `D subset Omega_c2`, so its
winding-number integral against the equilibrium measure `mu_c2` is zero.

The loop is reachable from the infinity germ inside

`C \ (K_c1 union K_c2)`,

because a finite union of compact zero-dimensional plane sets is
zero-dimensional and does not separate the plane.

### Degree contradiction

Choose `n` with `2^n > deg_Y P`. Continuing the relation around the iterates of
`gamma` gives

`P(z, exp(2*pi*i*k/2^n) phi_c1(z), phi_c2(z))=0`

for `k=0,...,2^n-1` on a common test neighborhood. A degree-`deg_Y P`
polynomial in `Y` cannot have these many distinct roots unless all its
`Y`-coefficients vanish after substituting `W=phi_c2(z)`.

The fixed coordinate `phi_c2` is transcendental over `C(z)` by
Becker--Bergweiler/Fernandes, equivalently by its own unbounded cylinder
monodromy. Hence all coefficients of `P` are zero, contradicting the choice of
`P`.

Therefore `phi_c1` and `phi_c2` are algebraically independent over `C(z)`.

## Retired Route

The proof is not the older local-branch-point argument around escaping
precritical points. For the direct Bottcher convention used here, the
load-bearing continuation is the period of `d log phi_c` around clopen Cantor
cylinders. Earlier small-loop wording is retained only in backlog logs as a
failed route.

## Source Boundary

- De Marco's shift-locus notes give the full two-shift model on disconnected
  quadratic Julia sets.
- Brolin-Lyubich theory identifies the equilibrium measure with harmonic and
  maximal-entropy measure, giving mass `2^-n` to depth-`n` cylinders.
- The reachability step uses the classical Mazurkiewicz no-cut theorem:
  zero-dimensional compact plane sets do not separate plane regions.
- Schmidt's Compositio paper independently supports high-order root-of-unity
  monodromy in the disconnected case.
- The cross-parameter relation `P(z,phi_c1,phi_c2)=0` is not stated in those
  sources.

## Grade

This is the both-disconnected subcase of the all-parameter quadratic
Nguyen-Q6.2 theorem. Its independent HGT value is the exact obstruction pattern:
one coordinate can carry arbitrarily high dyadic monodromy while the other is
fixed, which no finite algebraic relation can absorb.
