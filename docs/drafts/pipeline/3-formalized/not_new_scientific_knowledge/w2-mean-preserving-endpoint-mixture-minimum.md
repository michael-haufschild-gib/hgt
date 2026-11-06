# Mean-preserving endpoint mixtures have a sharp variance cost

- **ID:** w2-mean-preserving-endpoint-mixture-minimum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W2 representation construction](../../1-in-progress/w2-representation-construction.md)
- **Statement:** A finite probability mixture with mean colors `Re α_q/M` has arithmetic transposition discrepancy exactly `E/M² + V`, where `E=Σ_q(Im α_q)²` and `V` is total color variance. Its minimum is attained precisely when every positive-mass component equals that mean alphabet.

## Proof

Write mixture weights `λ_i≥0`, `Σ_i λ_i=1`, and probability alphabets `w_i(q)≥0`.
Each square-mass series converges because `w_i(q)²≤w_i(q)`. Jensen's inequality makes the
square mass of the mean summable. Finite-sum interchange and subtraction therefore give

`V = Σ_q[Σ_i λ_i w_i(q)² − (Σ_i λ_i w_i(q))²]`
`  = Σ_i λ_i Σ_q w_i(q)² − Σ_q(Re α_q/M)² ≥ 0`.

For each coordinate, twice its variance is
`Σ_ij λ_i λ_j(w_i(q)−w_j(q))²`. Thus `V=0` exactly when every supported alphabet equals
the mean at every coordinate. Independent coloring reads transpositions as square masses;
the proved endpoint identity contributes `E/M²`. Adding these two exact differences gives
the claimed decomposition and its unique supported minimizer.

Both summands are nonnegative. Exact arithmetic agreement holds iff `E=V=0`, hence iff
RH holds and every positive-mass component is the endpoint alphabet.

## Lean

`HTGeometry/SymmetricCharacters/MeanPreservingMixtures.lean` proves summability, the variance
identity and rigidity, and positivity, normalization, conjugation and restriction of the
mixture characters.

`RHTower/Representation/EndpointMixtureDefect.lean` proves
`xiEndpointMixture_transposition_gap`, `xiEndpointMixture_transposition_gap_lower`,
`xiEndpointMixture_minimum_iff`, and `xiEndpointMixture_exact_iff`.
Both direct leaf checks pass; both umbrella imports are present.

## Scope

This is the classical variance identity applied to the exact endpoint discrepancy, not a
new positivity source. Fixed-mean randomization cannot improve that discrepancy. The theorem
does not exclude changing the mean or constructing a different arithmetic representation.
