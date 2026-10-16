# HCF complete source positivity

Status: investigation. Requested target remains open.

## Exact target

Prove nonnegativity of the complete actual heat Hankel form for every polynomial
at positive heat time, equivalently positivity of every actual leading heat
Hankel determinant. The existing `XiGaussianHeatRouteCapstone` proves that
this is RH-strength. No new equivalence, receiver, conditional theorem or
estimate will count as completion.

## Starting evidence

The new regular-head kernels reproduce the exact signed moment form and split
into mutually orthogonal block projections. This retains every negative
direction; idempotence alone supplies no sign. The existing source endpoint
rigidity preserves the preceding positive head at a first contact but leaves
the new pivot's sign unresolved.

## Attack ledger

1. Test whether the exact kernel/projection structure together with heat flow
   forces positive block couplings. Check all needed conditions against the
   actual source and existing first-contact results.
2. Inspect source-specific prime/archimedean ground-state decompositions for a
   cancellation identity that pays the complete signed remainder.
3. Inspect the new even-sector purification and cut-deficit laws for a genuine
   source sign producer, keeping their premises explicit.

No claim of complete positivity is made. Only a dependency-closed unconditional
proof, checked directly in Lean with standard axioms, can close this card.
