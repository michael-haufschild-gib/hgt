# Completed integral-multiplicative Dirichlet-shape blindness universality law

Status: paper proof complete; Lean exact audit passed.

## Lean sources

- `etaCompletion_completedDirichletShape`
- `etaCompletion_order_s₀`
- `forcesRHParity_iff_categorical`
- `lseries_alt_eq`

## Survivor

Imposing integrality and coprime multiplicativity on the actual coefficient sequence in a
completed Dirichlet presentation still does not force RH-grade parity when no functional equation
is imposed. The eta completion is a witness: its alternating coefficients are integral and
multiplicative, yet it has a simple off-line zero at `s₀` and therefore carries nontrivial deck
charge.

This strictly strengthens the prior separate no-go statements for completed Dirichlet shape and
for uncompleted integral multiplicative data. It also corrects the prior source commentary that
treated eta coefficients as nonmultiplicative.

## Proof skeleton

For coprime `m,n`, both cannot be even. Splitting the remaining three parity cases proves
`(-1)^(mn+1) = (-1)^(m+1)(-1)^(n+1)`, while integrality is immediate. The existing eta Dirichlet
identity puts this coefficient sequence in the completed shape presentation. Existing simple-zero
and trichotomy theorems then give off-line charge and failure of `ForcesRHParity`.

## Novelty audit

Pending post-formalization literature search.
