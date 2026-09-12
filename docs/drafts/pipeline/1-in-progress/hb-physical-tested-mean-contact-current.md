# HB: restore the physical tested means and source contacts

- **ID:** HB-QTMCC
- **Stage:** 1-in-progress
- **Parent:** [Fully tested centered current](../3-formalized/hb-physical-tested-centered-current.md)
- **Route:** Literal theta cusp → Xi occurrence → retained spin two → physical causal radial/left-QNM action → fixed common Hawking-clock extinction → RH

The fully tested centered bilinear current has source-derived six-term and
all-complex-weight upper-trace proofs, verified by the exact named-leaf build
at default limits. Its improper density integral retains the negative lower
current.
The restored linear moments, original response means, Q contacts and complete
physical-action cancellation remain open. No finite-clock covariance or RH
conclusion follows from a zero upper cusp trace.

12 September 2026: the linear-current identities, weighted zero traces and exact
mean restoration passed a foreground `lake env lean` check in
`/tmp/hb-tested-linear-current.lean` at default limits. This scratch has not been
published, wired or given a final leaf audit. Further boundary-lemma expansion is
deferred in favor of the direct [causal source-symmetry repair attack](hb-causal-source-symmetry-repair.md).

## Next source identity

Write `U_b=R_b-M R_b`, `G_b=F_b-M F_b`, and retain the original physical
scalar `T`. Define `B_b=M[T U_b,y]`, `A_b=M[T U_b]`. The original forced
response equation and actual horizontal periodicity give

```
B_b' = M[T_y U_b,y] + M[T_x U_b,x]
     + alpha_b/y^2*M[T U_b] + 1/y^2*M[T G_b].
```

This has four retained terms. No positivity is asserted for these complex
bilinear quantities. The finite integral of B_b' keeps both endpoints.
The source already proves `|T|<=Cy` and `|T_x|,|T_y|<=C` above height three.

A direct unscaled Young inequality loses decay by adding a growing test
square. Use height scaling before integration instead. On a unit horizontal
cell, for every natural N, ordinary Cauchy--Schwarz and Young give

```
2*y^N*|M[T U_b,y]| <= y^(2N+4)*Var(R_b,y)+C^2/y^2.
```

Indeed the product is at most `C*y^(N+1)*sqrt(Var(R_b,y))`; apply Young to
`y^(N+2)*sqrt(Var(R_b,y))` and `C/y`. The same majorant handles either test
derivative and either centered response derivative, since y>3. The potential
term uses `Var R_b<=E_b`, retaining `|alpha_b|`. The forcing term gives
`C*y^(N-1)*sqrt(Var F_b)` and hence at most
`C*y^(N+1)*sqrt(forcingMass_b)`. Its scaled Young bound uses
`y^(2N+4)*forcingMass_b+C^2/y^2`. Both majorants are integrable by the
already proved arbitrary-weight energy and literal forcing estimates.

Thus both `y^N B_b` and its actual derivative have a source-derived L1
majorant. W1,1 would force B_b's weighted upper trace to zero. A_b is bounded
directly by `Cy*sqrt(nonconstantMass_b)` and has every weighted zero trace.
This is a paper argument for the next Lean theorem, not a verified new leaf.

To restore H_b's complete tested product, multiply these linear moments by
the original full means and their derivatives. Establish their polynomial
growth from the actual source mean equations and original particular terms.
For derivative-response source contacts replace T by the literal T*Q;
retain its full principal part and all signed tail jets when proving growth.
The remaining pure-source current `M[T Q Q_y]` requires its exact principal
boundary contribution, not an assigned zero value.

## Physical action interface still required

The exact established transduction is
`K_n(q)=-Sigma_n(q)*|D_n(q)|^2`, with `Sigma_n(q)>0`. Identifying the actual
complete physical left-QNM action with this K does not produce extinction.
A source-derived nonnegative real orientation of that same complete action
would force D=0; assuming that orientation would merely supply the missing
RH-strength statement. Current norm estimates give no such sign.

Restore both solved quadratic responses, retained spin two, independent
scalar/scalar, scalar/vector and vector/vector terms, changing metric/test
weights, and horizon, cusp, characteristic and source-contact faces in the
same physical reader. Only then can a variational or finite-clock identity
be tested for cancellation. The common Hawking clock remains unchanged.

The corpus hybrid action search found the exact total-cokernel transduction
and one-unit-clock equivalence. It had 57,218 inventoried files, pending
compiler metadata, unmeasured semantic coverage and no retrieval errors.
The source theorem confirms the remaining sign burden; it does not certify
that the physical action has that sign.
