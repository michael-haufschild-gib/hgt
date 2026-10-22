# Full theta tail: test the proposed Cauchy coercivity reserve

- **ID:** RH-FULL-THETA-COERCIVITY-AUDIT-ROOT-20260926
- **Stage:** 1-in-progress
- **Type:** [BRIDGE] hostile test of the current comparison target
- **Owner:** root
- **Parent:** `rh-nonlocal-tail-root-2026-09-26.md`

## Frozen C8 after the exact first-atom obstruction

The previous positive model supplies a Cauchy-energy reserve. The next actual
question is whether any strictly positive reserve can survive in complete theta,
uniformly over rank on a real tail.

Conjectured obstruction: for every real a and c>0, some finite real nodes x_i>a
and coefficients b_i satisfy

`sum_ij b_i*b_j*[K_Phi(x_i,x_j)
  -c*Phi(x_i)*Phi(x_j)/(exp(2x_i)+exp(2x_j))] < 0`.

Here K_Phi is the literal complete-source tail kernel. This is not a conjecture
that K_Phi is indefinite. It attacks strict relative coercivity, a stronger
claim than its still-open PSD sign. Classified [BRIDGE]: the following
reflection/locality mechanism already motivates the precise statement.

## Paper mechanism to audit

Exact source/kernel reflection and the proved diagonal tail asymptotic suggest
`K_Phi(x,x)/Phi(x)^2 -> 0` as x->-infinity. For the analytic feature
`h(x)=Phi(x)/(exp(2x)+1)`, the same limit holds relative to h(x)^2.
Thus K_Phi-c*h*h has a negative diagonal for every c>0. Add one scalar feature
to the completed analytic realization and apply the density/locality theorem:
the negative packet must survive on every real tail.

The Cauchy Gram kernel dominates `2/[(u+1)(v+1)]` as a quadratic form, by the
Schur complement of its extra node 1. Therefore a positive Cauchy reserve would
imply the excluded positive rank-one reserve. Every arrow must be checked;
no C8 result is claimed yet.

## Whole-route decision

This directly tests the missing all-rank comparison, using complete theta's
reflection rather than another first-atom refinement. If proved, it excludes
any argument leaving strictly positive Cauchy coercivity after the remainder.
It does not exclude a sharp semidefinite cancellation with zero reserve and
does not refute RH. Positive survivor sought: exact criterion for which
analytic reference features can admit a uniform lower bound.

## Plan

1. Check the actual reflected diagonal limit and analytic feature hypotheses.
2. Prove or falsify the rank-one reserve claim on every tail.
3. Audit the Cauchy Schur-complement transfer and formalize the exact result.
4. Reassess the complete-source sign target using the obstruction's survivor.

## C8 closed in Lean scratch

The frozen finite real-node statement passes Lean, together with the exact
reflected diagonal asymptotic, augmented rank-one analytic realization, tail
negative packets, and Cauchy Schur-complement bound. No hypotheses about RH or
Xi zeros, no numerical experiment, no omitted analytic bridge.

Leaf: `ThetaTailCauchyCoercivityObstruction.lean`; named build/audit underway.

Whole-route correction: C6 remains a valid positive model. Its strictly positive
Cauchy margin cannot persist in the exact source uniformly in rank. An error
estimate consuming the entire reserve and leaving zero could still prove PSD;
this theorem does not exclude that endpoint. Stop pursuing a strict residual
Cauchy gap. The next comparison must respect the reflected incoming envelope
or establish exact semidefinite cancellation.

## Final audit

Named leaf build and all 17 public theorem axiom reports pass, standard axioms
only. Leaf wired, index refreshed, final lint --check-generated passes.
Closed obstruction and positive survivors:
`../../../5-failed/rh-full-theta-positive-cauchy-reserve-root-2026-09-26.md`.

Next research must attack the exact semidefinite sign with no strictly positive
Cauchy reserve, or establish a different source-specific comparison geometry
that respects the incoming reflected scale. RH remains unresolved.
