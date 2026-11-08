# Spectrum of the weighted torsion limit

- **ID:** hhac-weighted-torsion-spectrum
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Status:** Paper, corpus and literature audits incomplete; no Lean claim

## Target

For every `δ>0`, the actual torsion-limit form on `Hδ` should represent a
compact self-adjoint operator with infinitely many positive and negative
directions. Its Hilbert–Schmidt threshold should be exactly `δ>1/2`.

This would distinguish infinite arithmetic rank from positivity and show
whether finitely many correction directions could repair the torsion limit.
It depends on the actual operator construction in
[weighted torsion completion](../3-formalized/hhac-weighted-torsion-form-completion.md).

## Candidate mechanisms to audit

The limit is bounded for every positive conductor weight. Factoring its form
through `Hδ → H_(δ/2)` should give compactness, since the coordinate inclusion
has diagonal entries tending to zero.

For distinct sufficiently large odd primes `q`, restrict to the arithmetic
coefficients supported on `{q,2q}`. Verify the exact matrix

`[[d(q), −log(2)/√2], [−log(2)/√2, d(q)+log(2)]]`,

where `d(q)=log(q)/(q−1)`. Different prime pairs have zero mixed entries.
The vector `(1,1)` then has value
`2d(q)−(√2−1)log(2)`, expected to be negative for all sufficiently large `q`.
The second coordinate has positive value. These are compressions; invariance
of their span under the full operator is not asserted.

In normalized Hilbert coordinates the prime entries are
`−P(m,n)/(mn)^(δ/2)`. Divisibility suggests the exact square-sum decomposition

`Σ_{m≠n} P(m,n)²/(mn)^δ`
`=2(Σ_m m^(−2δ))(Σ_{t≥2} Λ(t)²/t^(1+δ))`.

The diagonal contributes `Σ_n d(n)²/n^(2δ)`. Ratio-two entries should force
divergence at `δ≤1/2`; the logarithmic envelopes should give convergence
above that boundary. Reindexing, summability and the operator interpretation
all require proofs.

## Positive survivor required for any sign obstruction

If finite-rank sign repair fails, retain the exact arithmetic compressions,
compactness and sharp Hilbert–Schmidt classification, with their Lean status.
A renamed assertion of infinite negative index is not sufficient salvage.
No conclusion about the full Weil form or its archimedean payment follows
from the torsion limit alone.

## Existing spectral background

[Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323) prove compactness and
power eigenvalue asymptotics for the LCM matrices
`E(σ,τ)_(m,n)=(mn)^σ/lcm(m,n)^τ` in their stated parameter range.
Substitution `τ=1`, `σ=(1−δ)/2` identifies the positively weighted normalized
gcd majorant with this family, with exponent `τ−2σ=δ`. This algebraic
identification locates the compactness mechanism in established arithmetic
operator theory. The further novelty audit concerns the actual torsion
kernel, its prime-pair compressions and regulated comparison; no priority
claim follows from the preliminary search.
