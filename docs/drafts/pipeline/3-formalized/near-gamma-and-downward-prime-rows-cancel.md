# Near Gamma and downward prime rows cancel

- **ID:** near-gamma-and-downward-prime-rows-cancel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Target

For every fixed overlap `c>0`, compact `C²` unit-supported profile of positive
square mass, and Ramanujan conductor, the near off-diagonal Gamma action
minus the interior downward non-ratio prime action has bounded squared
coefficient norm, uniformly in the horizon. Its logarithmically normalized
norm therefore tends to zero.

## Proof

Put `w=c/N`, `M=∫φ²`, and `G(t)=∫φ(u)φ(u+t)du`. Let `H_n` be the
off-diagonal Gamma row restricted to `|log j-log n|≤2w`, acting on
`c_m(j)/√j`. Let `P_n` be the downward prime row restricted to products
`kj≤N`, with the exact ratio products `kj=n` removed. Both use atom-mass
normalization `wM`.

Regrouping the literal product sum by `ell=kj` gives

`P_n = Σ_(ell≤N,ell≠n) [G(|log ell-log n|/w)/M]/√ell
          * Σ_(d|ell) Λ(d)c_m(ell/d)`.

This regrouping is the finite bijection `(k,j)↔(kj,k)`. Autocorrelation
vanishes outside `|log ell-log n|≤w`, so enlarging its range to the Gamma
near range adds only zeros. The exact divisor-jet identity gives

`Σ_(d|ell) Λ(d)c_m(ell/d)=log ell*c_m(ell)-J_m(ell)`.

The near Gamma pairing is `log(N/c)G(s/w)/M+O_φ(1)` uniformly for `w≤1/3`.
Set `B=2c exp(2c)`. For every distinct near pair, integer separation and
`exp(2c/N)-1≤(2c/N)exp(2c)` imply

`|j-n|≤B`, `N≤Bn`, and `N≤Bj`.

There are at most `2B` entries per row. Also
`0≤log N-log j≤B`, `|G/M|≤1`, `|c_m(j)|≤φ(m)`, and
`|J_m(j)|≤Σ_(d|m)|μ(m/d)d log d|`. Hence, after the shared logarithm is
subtracted, each numerator in `H_n-P_n` has absolute value at most a fixed
`E_(φ,c,m)`. Cauchy–Schwarz and `1/j≤B/N` give

`Σ_(n≤N)|H_n-P_n|²≤4B³ E_(φ,c,m)²`.

Division by `log N→∞` proves vanishing squared norm on logarithmically
normalized Ramanujan profiles. No prime distribution theorem is needed.

## Lean status and scope

Leaf: `CriticalArithmeticCorrelationTheory/TheNearGammaAndDownwardPrimeRowsCancel.lean`.

- `interiorDownwardPrimeRow_eq_divisors`: literal product regrouping;
- `nearGammaDownwardRow_eq_actual_difference`: exact signed source identity;
- `exists_nearGammaDownwardRow_sq_bound`: uniform squared row bound;
- `tendsto_normalizedNearGammaDownwardVector_norm`: normalized norm limit;
- `tendsto_tiltedUnitSpline_nearGammaDownward_norm`: explicit-profile application.

Final no-olean Lean check passed without warnings. The audited source
identities, bound, and explicit norm limit use only `propext`,
`Classical.choice`, and `Quot.sound`. CACT umbrella wired.
Exterior products are handled by the boundary theorem below. Upward affine
windows remain part of the full norm quasimode problem.

## Novelty boundary

`TheNearAtomsHaveALogarithmicPairing` proves the Gamma entry expansion;
`TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet` proves the arithmetic
identity. Neither bounds their signed combined action in coefficient norm.
No claim of full spectral identification follows from this interior bound.

## Full downward source

The exterior-product remainder is removed in
[the boundary theorem](exterior-downward-prime-products-have-bounded-row-mass.md).
`TheFullDownwardPrimeRowCancelsTheNearGammaRow` proves the full infinite
prime-power action has the same normalized cancellation, including the
explicit tilted spline. Counted with this contribution, not separately.
