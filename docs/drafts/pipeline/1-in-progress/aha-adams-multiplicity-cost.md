# Adams multiplicity and arithmetic length

- **ID:** AHA-JETS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** aha-adams-torsion-resolution.md
- **Statement:** An auxiliary vanishing to full torus order `r` on the order-`d` fixed locus needs integer support reaching `2^(dr)`, with equality attained by `(χ(2)^d−1)^r`.

## Exact coordinates

Write each prime exponent as `v_p(n)=r_p+d k_p`, `0≤r_p<d`.
Near the torsion locus use `Y_p=z_p^d−1`. Then

`z^v = z^r ∏_p (1+Y_p)^(k_p)`.

The coefficient at residue `r` and multiindex `α` is therefore

`J(r,α)=Σ_(v(n)≡r) a_n ∏_p binom(k_p(n),α_p)`.

These are Newton coordinates of the auxiliary. Fourier inversion separates
the residues. The finite binomial transform should recover every coefficient
from these coordinates; the local maps `z_p↦z_p^d−1` have nonzero derivative
at every torsion point over characteristic zero.

## Proof mechanism to formalize

Among nonzero coefficients in one residue fibre choose `n` maximizing
`Σ_p k_p(n)`. For `α=k(n)`, a nonzero binomial product from another term
requires `k(m)≥k(n)` coordinatewise. Maximality and equality of sums force
equality of quotient vectors; the residue then forces `m=n`. Thus this jet
equals `a_n` and cannot vanish.

If `n<2^(dr)`, unique factorization gives `Σ_p k_p(n)<r`. Hence some jet of
order below `r` detects every nonzero auxiliary of that length. The boundary
binomial has order exactly `r` in the coordinate `Y_2`.

## Boundaries

This is a support-length bound. It is not a bound on coefficient height or
integer evaluation size. Full-coordinate jets are essential: one vertical
derivative direction permits cancellations between different prime
coordinates. The analytic mixed-jet identification must be proved, not
folded into the definition of multiplicity.

## Positive survivor

Exact residue–jet reconstruction, including a nonzero detecting jet below
the arithmetic degree threshold. The classical grid-vanishing mechanism
alone is not claimed as a new theorem of number theory. Lean proof pending.
