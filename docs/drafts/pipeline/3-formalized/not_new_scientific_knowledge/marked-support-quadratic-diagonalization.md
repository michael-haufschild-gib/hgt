# Marked-support quadratic diagonalization

- **ID:** `marked-support-quadratic-diagonalization`
- **Stage:** 3-formalized
- **Type:** `[PROVED] [BRIDGE] [POSITIVE SUCCESSOR]`
- **Scientific status:** not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MarkedSupportQuadraticDiagonalization.lean`
- **Inputs:** `prime-koszul-superdeterminant-cancellation.md`,
  `quadratic-reflection-anomaly-rh.md`

## Claim

Let `S` be a finite set of source-component or orbit labels and let `w_i` be their integral
weights.  Apply the marked Koszul character to the support of each ordered pair `(i,j)`.  Its value
is

```text
chi({i,j}) = 1,  i=j,
             0,  i!=j.
```

Consequently

```text
sum_(i,j in S) w_i w_j chi({i,j}) = sum_(i in S) w_i^2.   (1)
```

Lean proves the pair selector as `markedPairSupportExponent_eq` and `(1)` as
`markedSupport_diagonalizes_quadratic_sum`.

## Positive use

The quadratic reflection-anomaly route needs a finite-window sum of local squares but a raw global
quadratic refinement creates cross-orbit terms.  Equation `(1)` removes those terms canonically;
geometric orthogonality is unnecessary once the source anomaly has a finite component-labelled
incidence decomposition.  The scalar axis-factorization that was fatal for a connected prime
determinant is beneficial here: the desired output is deliberately the sum of independent positive
local squares.

## Boundary of the result

This theorem does not manufacture orbit labels from the completed source, subtract the fixed
reflection locus, transgress the integral square to the prime-log circle, or prove global anomaly
triviality.  Applying the selector only after expanding the unknown Xi divisor would be target-fed.
The remaining source theorem must construct the labelled incidence complex functorially from the
finite-window FE--Schwarz action groupoid before its divisor is read.

## Gates

- [x] finite support selector
- [x] exact removal of all quadratic cross-label terms
- [ ] source-defined component-labelled quadratic incidence
- [ ] equivariant fixed-locus subtraction
- [ ] source trivialization and RH
