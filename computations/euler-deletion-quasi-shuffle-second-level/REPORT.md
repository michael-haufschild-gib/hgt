# Euler-deletion chronological second-level diagnostics

## Scope

These computations test candidate behavior only. They are not used by any Lean theorem and give
no evidence about hypothetical off-critical zeros. Both scans used the supplied Runpod endpoint,
the first 12 `mpmath` zeta zeros, moduli `2, 3, 5, 7`, 15 geometric checkpoints through
`N = 2,000,000`, and vectorized NumPy chunks. The self-level scan used eight worker processes; the
cross-modulus scan used six.

Files:

- `scan.py`, `results.json`: endpoint, diagonal energy, and self chronological level.
- `scan_cross.py`, `cross-results.json`: all 16 ordered cross levels and their skew-Hermitian carry.

## Results

The finite quasi-shuffle identities were numerically preserved: maximum residual was
`2.53e-14` in the self scan and `4.27e-14` in the cross scan.

At `Re rho = 1/2`, diagonal energy has logarithmic slope `q - 1` as predicted by the periodic
coefficient square mean. Observed mean slopes were `0.9999982`, `1.9999981`, `3.9999945`, and
`5.9999792`. Endpoints at the final cutoff had norm at most `1.415e-3`; the real renormalization
`Re H2 + Q/2 = |endpoint|^2/2` had error at most `1.00e-6`.

Raw self-area imaginary values were nonzero and took both signs across the 12 zeros. Their maximum
fitted tail slope in `log N` was `8.27e-4`, and the largest change between the final two checkpoints
was `1.06e-4`. This is consistent with convergence, but does not prove it.

For every distinct modulus pair, the cross carry

`K(p,q) = H2(p,q) - conjugate(H2(q,p))`

was nonzero in general and took both signs in its real and imaginary coordinates across tested
zeros. Across all pairs and zeros, the maximum fitted tail slopes were `2.12e-5` in the real
coordinate and `3.26e-8` in the imaginary coordinate; the largest final-checkpoint change was
`4.37e-6`. No logarithmically growing cross-modulus anomaly was observed.

## Consequences

- Raw self-area sign or vanishing cannot be the missing RH producer.
- Raw cross-carry sign or vanishing cannot be the missing producer either.
- Data support existence of finite, zero-specific chronological carry values, not a universal
  positivity law.
- Any surviving depth-two mechanism must use an exact compatibility relation among canonical
  continuations or refinement maps. It cannot infer coherence from endpoint closure, numerical
  convergence, or a universal sign that the data already refute.

