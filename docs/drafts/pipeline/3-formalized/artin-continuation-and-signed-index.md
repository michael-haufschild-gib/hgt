# Artin continuation and signed index

- **ID:** A141-continuation-index
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every finite-dimensional Artin Euler product has an analytic
  numerator and denominator on `Re s > 0`, hence a meromorphic continuation.
  Its meromorphic order is the net multiplicity of a tempered virtual zero
  configuration, with its exact Weil index law counting zeros and poles.

## Proof

Brauer induction and reciprocity give `L(s)=∏ Λ_q(s)^{n_q}` on `Re s>1`.
Each `G_q(s)=(s−1)Λ_q(s)` is analytic on `Re s>0`, and every `Λ_q` is nonzero
on `Re s>1`. Put `n_q⁺=max(n_q,0)` and `n_q⁻=max(−n_q,0)` and define

`A(s)=∏ G_q(s)^{n_q⁺}(s−1)^{n_q⁻}`,
`B(s)=∏ G_q(s)^{n_q⁻}(s−1)^{n_q⁺}`.

Both are analytic on `Re s>0`; `B` is nonzero on `Re s>1`. Integer-power
algebra gives `A=B L` there. Thus `A/B` continues the actual Euler product.
Both analytic orders are finite on the connected half-plane, since both
functions are nonzero at `2`. The quotient rule identifies their difference
with `meromorphicOrderAt (A/B)`. The Artin order theorem applies to this pair: away from
`1`, `ord A−ord B=Σ n_q mult(Z_q)`; at `1` the order is the negative sum of
the trivial-character coefficients. The virtual-configuration index theorem
then counts distinct off-line points with nonzero net order and critical-line
points with negative net order.

## Lean

Module:
`GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinEulerProductHasAMeromorphicContinuationAndASignedIndexLaw.lean`.

- `exists_analytic_quotient_artin`
- `exists_meromorphicContinuation_artin`
- `exists_analytic_quotient_and_virtualConfig_artin`
- `exists_meromorphicContinuation_and_signedIndex_artin`

Final check from `formal/`:
`lake --old env lean GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinEulerProductHasAMeromorphicContinuationAndASignedIndexLaw.lean`.
All four transitive axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`. Imported by `AbsoluteGeometryOfSpecZ.lean`.

This closes the analytic-quotient input of A141's signed index transfer.
It does not establish the general-field `7/8` estimate or conductor exponents.
