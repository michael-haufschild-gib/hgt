# Central vanishing orders of the averaged Narain transform

- **ID:** W11-NJ
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Exact mean regularization](../3-formalized/ads3-narain-average-principal-part.md)

## Conjectures

Write `T_Y(u)=filledNumeratorMean Y u`, `c=2−4 Re ξ′(1)` and `Y*=exp(c)`.

1. `T_Y(−u)=−T_Y(u)` and `T′_Y(0)=√Y[c−log Y]`.
2. The actual averaged continuation has
   `M′_YZ(0)=4√(YZ)[c−log Y][c−log Z]`.
3. Its central zero has finite odd order. It is simple exactly when
   `Y≠Y*` and `Z≠Y*`. Its order is at least three when one height is
   exceptional, and at least five when both are exceptional.
4. Stronger target: these exceptional orders are exactly three and five.

Here `M_YZ(u)=narainMellinMean Y Z u`; the physical Mellin center is
`s=1/2`.

## Mechanism and unresolved input

The xi functional equation exchanges the two terms of `T_Y` with a
minus sign. Differentiating its explicit formula at zero and using
`ξ(0)=ξ(1)=1/2`, `ξ′(0)=−ξ′(1)` gives the first jet. Schwarz reflection
makes `ξ′(1)` real. The corpus supplies `xi_one_sub`, derivative reflection
and `xi_deriv_conj`; the existing Narain formalization gives entire
`T_Y/u` and the exact reduced mean quotient.

The quotient `T_Y/u` is even, so each of its zeros at zero has even order.
The reduced mean has one further factor of `u` and a denominator nonzero
at zero. Since `T_Y(1/2)=1`, these orders are finite. This gives the parity
law and the exceptional lower bounds.

Exact exceptional orders require proving `T'''_(Y*)(0)≠0`; oddness and
the first jet do not discharge that input. Audit it separately after
formalizing the first three statements. No RH-strength source estimate
follows from this central classification. The proved nonvanishing of
`T_Y` at every arithmetic resonance holds at every height, so exceptional
central cancellation cannot remove an arithmetic pole.

## Gates

- [ ] 0 → 1: audit exact first jets, reflection inputs and order arithmetic.
- [ ] 1 → 2: dependency-closed proof of the central classification.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
