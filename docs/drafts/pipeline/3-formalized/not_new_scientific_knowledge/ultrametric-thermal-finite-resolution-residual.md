# Ultrametric thermal finite-resolution residual

- **ID:** `ultrametric-thermal-finite-resolution-residual`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / FINITE-RESOLUTION OBSERVABILITY CORE
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [PARENT-DERIVED]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/UltrametricThermalTruncation.lean`
- **Paper application:**
  `../../2-fully-proven/not_new_scientific_knowledge/de-sitter-ultrametric-detailed-balance-hypertranscendence.md`
- **Statement:** The failure of an `N`-shell ultrametric thermal prefix to obey the infinite
  Mahler constraint is exactly the negative of its next omitted shell.

## Exact theorem

Over an arbitrary field, define the positive shell and the prefix with `N` positive shells by

```text
S_k(p,w) = (p-1)^2 p^k w^(p^(k+1)),
K_(p,N)(w) = (p-2)w + sum_(0<=k<N) S_k(p,w).               (1)
```

Lean first proves the scale shift

```text
S_(k+1)(p,w) = p S_k(p,w^p).                              (2)
```

It then proves the exact finite constraint

```text
K_(p,N+1)(w)
  = (p-2)w + w^p + p K_(p,N)(w^p),                        (3)
```

the consecutive-resolution law

```text
K_(p,N+1)(w) - K_(p,N)(w) = S_N(p,w),                     (4)
```

and therefore the same-resolution residual

```text
K_(p,N)(w) - [(p-2)w + w^p + p K_(p,N)(w^p)]
  = -S_N(p,w).                                             (5)
```

Equation `(5)` identifies the finite cutoff defect; it does not approximate it.

## De Sitter detector specialization

For the detailed-balance coordinate

```text
w_H = exp(-a/H),              a = 2 pi epsilon,
```

one has `w_(H/p)=w_H^p`.  Thus `(5)` becomes

```text
R_N(H) - [(p-2)e^(-a/H) + e^(-ap/H) + p R_N(H/p)]
  = -(p-1)^2 p^N e^(-a p^(N+1)/H).                        (6)
```

A finite experiment resolving the base shell and `N` positive shells can therefore test the
predicted next-shell boundary charge using measurements at two Hubble scales.  Repeating the test
as resolution grows gives a cofinal falsification protocol for the tower.

No fixed finite `N` proves that the tower continues forever or certifies hypertranscendence.
Every finite prefix is a finite exponential sum and hence differentially algebraic.  Equation
`(6)` is a finite-resolution witness for the constraint mechanism, not a finite HT certificate.

## Anti-theatre and novelty verdict

The proof is finite sum algebra applied to the already-derived ultrametric multiplicities.  It is
not new scientific knowledge.  Its value is operational: it replaces the phrase "measure the
infinite trace" by an exact hierarchy of finite, falsifiable residual identities while preserving
the sharp boundary that hypertranscendence itself remains an infinite-completion property.

## Lean surface

- `ultrametricThermalShell`
- `ultrametricThermalTruncation`
- `ultrametricThermalTruncation_zero`
- `ultrametricThermalShell_succ_eq_scale`
- `ultrametricThermalTruncation_succ_constraint`
- `ultrametricThermalTruncation_succ_sub`
- `ultrametricThermalTruncation_constraint_residual`

## Verification

- [x] exact cached module build passed in one foreground process
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation used
- [x] imported by the HTGeometry umbrella
- [x] repository lint scan reaches this module without flagging it
- [ ] repository lint is globally green; unrelated concurrent modules remain unreachable from
      their theorem-area umbrellas
