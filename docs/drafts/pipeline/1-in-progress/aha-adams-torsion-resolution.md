# Adams torsion resolution and auxiliary cost

- **ID:** AHA-ADAMS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** arithmetic-harmonic-analysis-programme.md; obstacles summary Q2
- **Statement:** Restricting a finite Dirichlet polynomial to the order-`d` prime torsion grid groups its coefficients by prime valuations modulo `d`.

## Exact targets

For a finite set of primes `P`, sample all `d`-torsion phases independently.
Fourier inversion should recover, for each residue vector `r`, precisely
`Σ_{v_P(n) ≡ r mod d} a_n`. Plancherel is the sum of squared absolute values
of these fibre sums. Thus vanishing is equivalent to cancellation separately
inside every residue fibre.

If all prime factors in the support lie in `P` and `1 ≤ n < 2^d`, distinct
support integers have distinct residue vectors: every valuation is below `d`.
Consequently no nonzero auxiliary of that length vanishes on the entire
fixed locus. The boundary is attained by `χ(2^d)−1`.

The higher-multiplicity target is a length threshold `2^(dr)` for vanishing
of **all torus jets of total order below `r`** on the whole grid. Its
multivariate ideal and jet proof remain open here. Vertical derivatives alone
cannot give that threshold: at order one torsion,
`log(3)(z₂−1)−log(2)(z₃−1)` has zero value and zero vertical derivative at
the identity, but a nonzero transverse derivative. Its support ends at `3`,
below `2²`. This example uses real coefficients; it does not settle the
integer-coefficient auxiliary problem.

## Novelty and boundary

Finite Fourier inversion and grid vanishing are classical. The contribution
sought is their exact arithmetic support and Adams-fixed-locus interface,
including the sharp integer-length obstruction. Compare Alon's grid ideal
theorem, [Combinatorial Nullstellensatz, Theorem 1.1](https://www.tau.ac.il/~nogaa/PDFS/null2.pdf).
This is a calibration and support-length theorem, not a parity producer or
a lower bound on coefficient height or on an evaluated integer's size.

## Positive survivor

Complete coefficient reconstruction below the first collision, and exact
residue-fibre reconstruction at every length. These are the constructive
content of the vanishing obstruction. Formalization is in progress.
