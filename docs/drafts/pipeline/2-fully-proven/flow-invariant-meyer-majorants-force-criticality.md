# Flow-invariant Meyer majorants force criticality

- **ID:** flow-invariant-meyer-majorants-force-criticality
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II mixed source bounds and invariant evaluation gauges.
- **Status:** Exact source proof below; Lean landing pending; external novelty unverified.

## Statement

On actual strong logarithmic Meyer sources, existence of a finite nonnegative function
`Phi` invariant under centered dilation and satisfying

`meyerSourceTrace(g,h)^2 <= Phi(g) Phi(h)`

for every pair is equivalent to RH. No triangle, homogeneity, quotient descent,
faithfulness, or RR law for `Phi` is required.

## Source-to-evaluation proof

Fix a Xi divisor point `rho`, with multiplicity `m>=1`. Let `e_rho` be the actual
point source with Mellin value one at `rho` and zero at every other divisor point.
Put `h0=sharp(e_rho)` and `h1=sharp(i e_rho)`. The source trace identity and
involutivity of sharp give

`trace(g,h0)=Re(m M_g(rho))`,
`trace(g,h1)=Re(i m M_g(rho))=-Im(m M_g(rho))`.

Adding the two mixed bounds gives

`m² |M_g(rho)|² <= Phi(g) K`, where `K=Phi(h0)+Phi(h1)>=0`.

Since `m>=1`, it follows that `|M_g(rho)|²<=Phi(g) K`.
The elementary inequality `u<=u²+1` for `u>=0` then gives

`|M_g(rho)| <= (K+1)(Phi(g)+1)`.

Thus `Phi+1` is a finite nonnegative invariant evaluation gauge on actual sources.
The evaluation is nonzero, witnessed by `e_rho`. Centered source flow multiplies
it by `exp(c(rho-1/2))`. Apply the existing abstract theorem
`re_eq_zero_of_invariantGauge_bounded_eigenfunctional`: the exponent has zero real
part, so `Re rho=1/2`. Every divisor point is critical, hence RH.

This argument deliberately works on actual sources. It does not assume `Phi` is
constant on Poisson classes, and does not manufacture a quotient norm.

## Converse

Under RH use `Phi(g)=meyerSourceTrace(g,g)`. Positivity and the mixed Cauchy bound
follow from the already established trace/Hodge-index equivalence. Centered source
flow preserves the trace even without RH: in each reflected Mellin term its two
exponential factors multiply to one, since the second argument is evaluated at
`1-conj(rho)`. This proves the needed invariance directly from the exact trace sum.

## Insight and scope

Unconditional positive majorants can give independent Bézout, but an invariant one
controlling every actual mixed trace would already force criticality without RR.
The missing geometric compatibility cannot therefore be supplied merely by declaring
the majorant to be a norm or by passing to a completion. The positive survivor is
the explicit two-point-source evaluation bound, requiring no norm axioms.

No claim is made here that the compact-source global exponential majorant has this
invariance or extends to all strong logarithmic sources with the same formula.
The corresponding compact-source statement still needs its exact translated-pairing
bridge; the larger actual Meyer carrier has the point sections used above.

## Formalization dependencies

Read `DeningerMeyerInvariantEvaluationGaugeFrontier.lean` completely. Its abstract
eigenfunctional theorem already proves the exponential growth step; reuse it.
New obligations are the centered actual-source linear flow, the two trace readings,
the norm bound from their squares, and exact centered trace invariance. The required
raw Mellin flow identity is `deningerMeyerStrongLogMellin_flow`; full jet flow is
already in `DeningerMeyerXiSpectralInclusion.lean`.

## Stronger unconditional survivor: literal product invariance

The reflected exponential cancellation holds at every complex Mellin parameter,
not only at the Xi divisor. Actual Mellin injectivity therefore proves
`flow_c(g) * sharp(flow_c(h)) = g * sharp(h)` as an equality of original
sources. Every reading of that product is invariant, without linearity or
quotient descent. Trace invariance is a corollary. In particular the strictly
positive origin square degree is invariant too. This does not contradict the
majorant theorem: positivity and invariance of a different product reading
do not provide the required mixed bound on the original trace. The complete
pointwise proof replaces the trace-only proof in the unrun flow draft.
