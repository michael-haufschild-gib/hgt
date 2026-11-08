# Unweighted mixed spacing fails; conductor weights recover the prime row

- **ID:** hhac-mixed-spacing-prime-row
- **Stage:** 5-failed
- **Type:** SHARP OBSTRUCTION AND POSITIVE CLASSIFICATION

## Exact obstruction

Use the existing spacing radius `rε(m,n)=exp(−ε(1/m+1/n))`, with `ε>0`.
For each prime `p`, define the actual mixed error

`Eε(p)=twistedEnergy(rε(1,p),1,p)+log(p)/√p`.

There is no real constant `C` such that, for every finite prime set `S` and
real coefficients `x`,

`|Σ_{p∈S} x_p Eε(p)| ≤ C (Σ_{p∈S} x_p²)^(1/2)`.

In particular, the squared row errors have unbounded finite sums. Uniform
diagonal convergence therefore cannot be extended to an unweighted mixed
row estimate, even for one fixed positive regulator.

## Strongest proved positive survivor

For every real `δ` and every `ε>0`,

`Σ_p Eε(p)² p^(−δ)<∞ ⇔ δ>0`.

For every `δ>0`,

`lim_{ε→0+} Σ_p Eε(p)² p^(−δ)=0`.

This is an exact threshold and convergence theorem for the original mixed
energy. Positive conductor weights recover the entire prime row; they are
not an assumed analytic input.

The stronger [full weighted estimate](../3-formalized/hhac-weighted-mixed-spacing-convergence.md)
is also formalized: for `0<α≤1` and `δ>2α`, the sum of absolute mixed errors is
at most `Cδ,α ε^α Σ n^δ x_n²`, uniformly over finite positive supports.
For infinite probes of finite weighted square mass, the entire absolute error
series is summable, obeys the same bound and tends to zero.
`WeightedSpacingConvergence.lean` and `InfiniteSpacingConvergence.lean` pass
direct audits with the standard three axioms.

The [actual Hilbert completion](../3-formalized/hhac-weighted-torsion-form-completion.md)
further constructs all three original forms on every positive-weight carrier:
absolutely convergent symmetric pair series, positive raw form, exact ordinary
coefficient counterterm, and operator-norm convergence at the same power rate.
Its dependency-closed paper proof and five Lean modules are directly audited.

## Proof

The orbit of order one is a singleton. The norm identity
`|1−r conjugate(w)|=|r−w|` and the factorization of the cyclotomic polynomial
identify its torsion energy with `−log|Φ_n(r)|`. For prime `p`,
`Φ_p(r)=1+r+⋯+r^(p−1)` and the gcd twist is one. Consequently

`Eε(p)=(log p−log(1+r+⋯+r^(p−1)))/√p`, `r=rε(1,p)`.

For `0<r<1`, the geometric sum lies in `[1,p]`. Also `r≤exp(−ε)`, so that
sum is at most `1/(1−exp(−ε))`. Hence

`0≤Eε(p)≤log(p)/√p`,
`Eε(p)≥(log p−Cε)/√p`, `Cε=log(1/(1−exp(−ε)))`.

Eventually the last lower bound is at least `1/√p`. Euler's divergence of
`Σ_p 1/p` proves failure of unweighted square summability. Every nonpositive
weight increases these terms. A purported finite-probe bound, tested on
`x_p=Eε(p)`, would bound every finite squared row sum by `C²`, a contradiction.

For positive `δ`, the majorant `(log p)²/p^(1+δ)` is summable: logarithms grow
slower than any positive power, and the corresponding integer power series
converges. At each fixed prime the geometric sum tends to `p` as `ε→0+`.
Dominated convergence proves the weighted squared-norm limit.

## Lean and audit

[PrimeSpacingRow.lean](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimeSpacingRow.lean):

- `torsionEnergy_one_prime`, `primeSpacingError_eq`, `primeSpacingError_bounds`,
  `primeSpacingError_lower` identify the original kernel and its bounds.
- `not_summable_primeSpacingError_sq`, `primeSpacingError_square_sums_unbounded`,
  `primeSpacingError_no_unweighted_row_bound` prove the obstruction.
- `summable_primeSpacingError_weighted_iff` gives the exact threshold.
- `tendsto_tsum_primeSpacingError_weighted` proves weighted convergence.

The module passes a direct `lake --old env lean` audit. Printed capstones use
exactly `[propext, Classical.choice, Quot.sound]`.

## New insight and scope

The relevant distinction is between regulator convergence on fixed conductors
and convergence on an infinite arithmetic probe space. The actual product
spacing radius remains bounded away from one on the `(1,p)` row when the
regulator is fixed; its geometric sum stays bounded while the unregulated
cyclotomic value grows like `p`. A positive conductor weight absorbs exactly
this escape to large primes.

Cyclotomic factorization, Euler's divergence theorem and dominated convergence
are classical. The contribution is their sharp application to the actual
mixed spacing error; no priority claim is made for those ingredients.
The full weighted operator comparison strengthens the positive survivor.
It does not pay self-energy or make the indefinite limiting form nonnegative.
