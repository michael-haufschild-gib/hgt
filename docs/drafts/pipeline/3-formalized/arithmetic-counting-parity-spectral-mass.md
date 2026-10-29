# The parity constraint is exhausted by its prime-power Ramanujan tower

- **ID:** ACP-PARITY-SPECTRAL-MASS
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Source:** ../3-formalized/arithmetic-counting-harmonic-spectral-coordinates.md
- **Statement:** The normalized prime-parity constraint has an explicit Ramanujan expansion on conductors `1,p,p^2,...`, with geometric squared tail `4p/(p+1)^2 * p^(-K)` after conductor `p^K`.

## Goal

Upgrade individual limiting coordinates to a mass-preserving exhaustion.
This provides the spectral information needed for exact constrained-gap
laws, beyond the two-mode upper bound and the large-prime lower bound.
The construction uses the integer parity count and arithmetic modes, not
zeros or an assumed positive representation of the complete Weil form.

## Statement

For a prime `p`, put `c=(p-1)/(p+1)` and let `u_(m,N)` denote the
harmonically normalized Ramanujan vector. Set

`v_(p,N)(n)=omega_p(n)/sqrt(n H_N)`,

`a_0=c`,

`a_k=2c(-1)^k/sqrt(phi(p^k))` for `k>=1`,

`z_(K,N)=sum_(0<=k<=K) a_k u_(p^k,N)`.

The target is the exact limit

`||v_(p,N)-z_(K,N)||^2 -> 4p/(p+1)^2 * p^(-K)`.

In particular, the order `K -> infinity` after `N -> infinity` exhausts
the unit constraint in norm. Its squared limiting coordinates are
`c^2` at conductor one and `4c^2/phi(p^k)` at `p^k`, summing to one.
This is a statement about the normalized constraint and prime matrix;
it asserts no positivity of the complete continuous Weil form.

## Closed paper proof

An exact finite-horizon argument is available, stronger than the initial
Gram-limit approach. Let `L_m(n)=c_m(n)/phi(m)` be the existing
`sieveLagMultiplier`, and put

`A_K(n)=c+sum_(1<=k<=K) 2c(-1)^k L_(p^k)(n)`.

The proved prime-power multiplier trichotomy gives, for every positive n,

`A_K(n) = c(-1)^K` if `p^K | n`, and `A_K(n)=omega_p(n)` otherwise.

Induct on K. Outside the preceding divisibility fibre the next multiplier
is zero. Inside its deeper fibre it is one and changes `c(-1)^K` to
`c(-1)^(K+1)`. On the intervening shell it is `-1/(p-1)`, and
`c+2c/(p-1)=1` restores the exact parity sign. Thus no Gram convergence
or exchange of infinite sums is needed for this identity.

After harmonic normalization, `A_K` is exactly the vector `z_(K,N)` above.
Expanding the squared error only on the divisibility fibre and applying
the exact harmonic multiples count gives

`||v_(p,N)-z_(K,N)||^2`
`= ((1+c^2) H_floor(N/p^K)-2c S_p(floor(N/p^K)))/(p^K H_N)`.

The existing parity count satisfies `S_p(M)>=c H_M` even at `M=0`.
Consequently the error is at most

`(1-c^2) H_floor(N/p^K)/(p^K H_N) <= 4p/(p+1)^2 * p^(-K)`

for every positive horizon N. This gives **uniform** geometric norm
exhaustion over all positive horizons. The bound is asymptotically attained
because both decimated harmonic and parity means have the stated limits.
For the limiting assertion, the harmonic shell
`0 <= H_N-H_floor(N/d) <= 1+log d` proves the decimated harmonic ratio tends
to one. The already proved decimated parity count tends to c. Applying
these two limits to the exact displayed error identity gives
`(1-c^2)/p^K=4p/(p+1)^2*p^(-K)`. Since `0<1/p<1`, the uniform geometric
bound tends to zero with K. This closes the proof without an exchange of
the two growing parameters. `[PROVED HERE]`

The coefficient mass is also exact:

`c^2+sum_(1<=k<=K) (2c(-1)^k/sqrt(phi(p^k)))^2`
`=1-4p/(p+1)^2*p^(-K)`.

For each positive k the summand is `4c^2/(p^(k-1)(p-1))`.
Its geometric partial sum gives the displayed remainder, or equivalently
one checks the initial value at K=0 and the exact increment. The partial
masses therefore tend to one. This identifies the full mass of the
arithmetic tower, in addition to its uniform approximation property.

Source audit: `sieveLagMultiplier_prime_pow_trichotomy` supplies all three
local cases; `ramanujanLagCoefficient_eq_totient_mul` identifies the
normalized profile with the finite Ramanujan sum;
`gaugeHarmonicSum_multiples` and `harmonicMass_multiples` supply the exact
fibre counts; `prime_parity_boundary_bounds` supplies `S_p(M)>=c H_M`;
`primeParity_decimation_tendsto` supplies its limiting mean. The existing
`tendsto_harmonic_natDiv_div_log` and harmonic normalization law also give
the harmonic ratio directly. All these source statements were inspected.

The later secular-gap classification is a separate target. It would also
need a proved finite-dimensional constrained-form criterion and uniform
control of the resolvent outside fixed spectral windows. These are not
assumed by this card.

## Corpus audit

Searches for finite-flip spectral measures and prime-parity spectral mass
found the individual mixed-count/eigenline limits, Ramanujan Gram laws,
and unrelated finite-prime Mobius amplitudes. No mass-exhaustion theorem
for this actual parity constraint was found. Existing generic constrained
secular theory is a lead for the later gap question, not an input here.

Literature scope: the classical Wintner--Delange theory already supplies
Ramanujan expansions from summability of Mobius-transform coefficients;
see the theorem and coefficient formula in
[Laporta, Section 1 (2024)](https://link.springer.com/article/10.1007/s12188-024-00282-4).
Expansion existence is therefore baseline. The contribution here is the
exact harmonic error on every integer horizon, its sharp uniform geometric
bound, and its identification with the actual prime constraint.

## Gates

- [x] 0 -> 1: exact arithmetic object, quantitative remainder and attack.
- [x] 1 -> 2: dependency-closed paper proof and source-name audit.
- [x] 2 -> 3: unconditional Lean proof, direct source check, transitive
  axiom audit, umbrella and foundational README integration.

## Formal closure

`PrimeParityIsExhaustedByItsRamanujanTower.lean` proves all eight endpoints:
`primeParityTowerProfile_value`, `primeParityTowerVector_eq_ramanujan`,
`primeParityTower_error_sq_eq`, `primeParityTower_error_sq_le`,
`tendsto_primeParityTower_error_sq`, `primeParityTower_coefficient_mass`,
`tendsto_primeParityTower_coefficient_mass`, and
`primeParityTower_uniform_exhaustion`.

The scratch check with transitive axiom queries and the canonical installed
source check both exited zero, without diagnostics. Each endpoint uses only
`propext`, `Classical.choice`, and `Quot.sound`. The adjacent audit file
preserves the source hash, commands and actual axiom output. The leaf is
wired into the programme umbrella and explained in its foundational README.
No umbrella was compiled. Its first olean was subsequently built because
the arithmetic secular-data leaf imports it; that exact-module build
exited zero without diagnostics.
