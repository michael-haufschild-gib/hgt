# Finite facet-orbit operator expansion law

- **ID:** `finite-facet-orbit-operator-expansion-law`
- **Stage:** 3-formalized
- **Type:** DIFFERENTIAL-OPERATOR ASSEMBLY BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [STANDARD PARENT THEORY]`
- **Statement:** Every finite family of facetwise finitely supported polynomial differential
  operators admits one common finite orbit packet, and the resulting finite operator matrix has
  exactly the same linear-independence matroid as the original nested coefficient rows.  On a
  differentially independent orbit packet, this is also exactly the nonlinear differential
  matroid of the output family.

## Exact law

Let `Q_i(A,g)` be a finite family indexed by `i`, with finitely supported orbit coordinate `g` for
each facet `A`, and values in `C[D]`.  Take the union of all supports and use it as the finite source
index type.  Coefficient expansion gives rows

```text
L_i(A,g)=Q_i(A,g).
```

Lean proves

```text
LinearIndependent C[D] L <-> LinearIndependent C[D] Q.
```

If `x_(A,g)` is differentially independent, the exact Toeplitz matroid theorem then gives

```text
DifferentialIndependent C (L(D)x) <-> LinearIndependent C[D] Q.
```

Thus passing from facetwise Laurent/group-ring notation to the actual finite differential-operator
matrix creates neither extra circuits nor lost circuits.

## Lean realization

`GaloisForLFunctions.HTGeometry.FiniteFinsuppOperatorRows` proves:

- `mem_finiteFinsuppRowSupport_of_ne`;
- `linearIndependent_finiteFinsuppOperatorRows_iff`;
- `differentialIndependent_finiteFinsuppOperatorRows_iff`.

The module builds unconditionally in the project toolchain.

## Boundary

This closes the finite-support matrix encoding used in the facet-sewn assembly.  It remains to
identify each localized facet quotient with the corresponding finitely supported Laurent orbit
coefficient module and to instantiate the common finite packet inside the formal upper-end
prime-log translation family.

## Gates

- [x] complete paper proof
- [x] complete unconditional Lean formalization
- [x] exact preservation and reflection of circuits
- [x] no independent novelty claim
