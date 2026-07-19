# Complete analytic Grassmann-field lattice embedding

- **ID:** `complete-analytic-grassmann-field-lattice-embedding`
- **Stage:** 3-formalized
- **Type:** GENERAL HT COMPLETION LAW / ARBITRARY INTERSECTION
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL]`
- **Parent:** `analytic-dirichlet-observable-field-correspondence`

## Theorem

Under the hypotheses of the split analytic Grassmann-field Galois connection, let

```text
Phi : Subspace(E) -> IntermediateField(C(s), M_infinity)
```

be the analytic source-field representation.

For every nonempty family `W : I -> Subspace(E)`,

```text
Phi(inf_i W_i) = inf_i Phi(W_i).
```

Equivalently, after restricting the codomain to the complete interval of intermediate fields below
`Phi(top)`, the map `Phi` is a complete lattice embedding:

```text
Phi(sup_i W_i) = sup_i Phi(W_i),
Phi(inf_i W_i) = inf_i Phi(W_i).
```

The interval formulation is necessary. For an empty family, the meet in the full ambient field
lattice is the whole meromorphic field, whereas `Phi(top)` need not equal that ambient top.

## Complete proof

The arbitrary-join law is already unconditional from the source-field Galois connection. The
easy meet direction

```text
Phi(inf_i W_i) <= inf_i Phi(W_i)
```

follows from monotonicity. The reverse direction follows from two finite-character laws.

1. **Finite source support of a field element.** Write

   ```text
   W = sup_(w in W) Cw.
   ```

   The arbitrary-compositum law gives `Phi(W)=sup_(w in W) Phi(Cw)`. Intermediate fields are
   compactly generated, so if `y in Phi(W)`, then `y` lies in the supremum of finitely many of the
   one-dimensional fields. Let `U` be the span of those finitely many source vectors. Then
   `U <= W`, `U` is finite-dimensional, and monotonicity gives `y in Phi(U)`.
2. **Finite determination of an intersection inside finite dimension.** If `U` is
   finite-dimensional and `W_i` is an arbitrary family, choose a finite set `S` minimizing

   ```text
   dim(U intersect intersection_(i in S) W_i).
   ```

   Adding any further `W_i` cannot lower this minimal dimension. Inclusion plus equality of finite
   dimensions therefore makes the intersection unchanged. Hence

   ```text
   U intersect (inf_i W_i) = inf_(i in S) (U intersect W_i).
   ```

   This is the descending-dimension condition: repeated intersections inside `U` can strictly
   lower dimension only finitely many times.

Now assume the index family is nonempty and take `y in inf_i Phi(W_i)`. Choose one index `i0` and
a finite-dimensional `U <= W_i0` with `y in Phi(U)`. The binary meet law, iterated over the finite
determining set `S`, gives

```text
y in Phi(U intersect intersection_(i in S) W_i)
```

and finite determination identifies this field with

```text
y in Phi(U intersect inf_i W_i) <= Phi(inf_i W_i).
```

This proves the reverse inclusion and therefore the nonempty arbitrary-meet theorem. `QED`

## Formalization target

- `exists_finiteDimensional_source_of_mem_analyticObservableGrassmannField`
- `exists_finset_inf_eq_iInf_inside_finiteDimensional`
- `cofiniteTailDenseOn_analyticObservableGrassmannField_finset_inf`
- `cofiniteTailDenseOn_analyticObservableGrassmannField_iInf`

The source is in
`formal/GaloisForLFunctions/HTGeometry/AnalyticDirichletObservableGrassmannCompleteLattice.lean`.
The exact leaf check and the headline axiom audit pass.  The audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## RH pressure test

If true, no nonempty infinite intersection of Euler source fields can create a residual analytic
sector absent from the intersection of the source constraints. Any route based on taking an
infinite descending family of represented Euler fields would converge algebraically to the exact
intersection source field, not to a hidden extra HT remainder.

This is a structural route constraint, not a zero-location theorem.

## Gates

- [x] exact statement corrected for the empty-family/top obstruction
- [x] finite-character proof mechanism isolated
- [x] existing arbitrary-join and binary-meet parents identified
- [x] finite source support lemma written in Lean
- [x] finite-dimensional intersection determination written in Lean
- [x] nonempty arbitrary-meet theorem written in Lean
- [x] exact targeted Lean check
- [x] axiom audit
- [x] complete interval-lattice embedding packaged
- [ ] literature novelty and significance audit
