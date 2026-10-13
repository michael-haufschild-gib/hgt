# Canonical finite Weil drift masks as polynomial idempotents

Status: IN PROGRESS — dependency-closed paper proof; native formalization pending.

## Objective and scope

Classify exactly the zero-weight interpolation polynomials, and therefore the leading drift masks of the already verified uniform-mixture approximation. The classification concerns this specific canonical approximation path. General approaches to a boundary can assign different decay rates to different atoms and are outside this statement.

For canonical nodes x_i and N=product_i(X-x_i), prove

`(exists Q, Z_Q=p) iff degree(p)<r+1 and N divides p^2-p and p != 1`.

Connect the same condition to existence of a target Q whose normalized approximation polynomials have coefficientwise logarithmic drift -p. All final canonical-law roots quantify arbitrary r, k, and p without auxiliary hypotheses.

## Local Lean evidence

- `FiniteLawBoundaryLogProfile`: zeroMassIndicator and its relation to actual normalized potential asymptotics.
- `PaperFourierLLogL/Finite/Law`: `mem_nonempty` supplies a positive atom; `proportional` constructs a probability law from nonnegative weights with positive sum.
- `FiniteNodePolynomialIdeal`: vanishing at every distinct node iff divisibility by the nodal polynomial.
- `WeilLogShiftPolynomialBoundaryProfile`: degree bound, node evaluations, and coefficientwise logarithmic limit for Z_Q.
- Local Mathlib Lean: Lagrange uniqueness and interpolation of the constant one; finite sum bounds; uniqueness of limits.

Initial documented lexical corpus search `idempotent interpolate` in HTGeometry returned no eligible declarations. Source searches found no existing nodal-idempotent or zero-indicator image classification. The broader `idempotent polynomial` search returned two declarations, both inspected: idempotence of Gomes profile normalization and of connection matrix units. Neither states this finite-node image classification. No external sources or computations.

## Dependency-closed paper proof

1. A finite law's zero indicator takes only values zero and one, with at least one zero because some atom has positive mass. Conversely, any such vector v is realized: normalize weights w_i=1-v_i. These are nonnegative, and a zero entry of v makes their sum positive. The resulting law's zero indicator is exactly v.
2. N divides p^2-p iff each p(x_i)^2-p(x_i)=0, equivalently each node value is zero or one. This is the existing finite-node ideal theorem plus scalar factorization.
3. For degree(p)<r+1, all node values one force p=1 by interpolation uniqueness. Thus an idempotent representative p different from one has at least one zero node.
4. Apply step 1 to v_i=p(x_i). Its realizing law Q has Z_Q and p equal at every node and both degree below r+1; interpolation uniqueness gives Z_Q=p. The forward implication follows from the binary indicator and existence of a positive atom.
5. The previous boundary theorem gives coefficientwise drift -Z_Q for every target. Uniqueness of real limits and polynomial coefficient extensionality show that a prescribed drift -p occurs exactly when Z_Q=p for some Q. This transfers the algebraic classification to the actual normalized approximation family.

## Planned artifacts

- `HTGeometry/FiniteLawZeroPattern.lean`
- `HTGeometry/FiniteNodePolynomialIdempotents.lean`
- `RHTower/WeilLogShiftPolynomialDriftIdempotents.lean`

## Verification pending

Native API scratch, sequential native leaves, final actual-root audit of every declaration, fresh objects/imports, umbrella wiring, formal lint, and transition to formalized only after verification.
