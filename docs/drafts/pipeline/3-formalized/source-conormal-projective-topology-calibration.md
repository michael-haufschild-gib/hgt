# A source-conormal clock topology remembers a line, not its Hermitian scale

- **ID:** `source-conormal-projective-topology-calibration`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [GENERAL HT TOPOLOGY--METRIC SEPARATION] [POSITIVE NO-GO]`
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `GaloisForLFunctions.HTGeometry.SourceConormalProjectiveTopology`
- **Parents:**
  - `source-conormal-strict-topology-refinement.md`;
  - `finite-observable-conormal-corona.md`;
  - `../1-in-progress/self-dual-decorated-clock-boundary.md`;
  - `../1-in-progress/source-polarized-laurent-pluecker-tangent-ward-law.md`.

## Theorem

Let `L : V -> Q` be a complex-linear source conormal with normed complex target, and let
`c != 0`.  The induced source-conormal topology is unchanged by rescaling:

```text
induced(cL)=induced(L).
```

For the minimal refinement of the raw complex product clock this gives

```text
T_src(cL)=T_src(L).                                      (1)
```

The Hermitian response behaves differently:

```text
||(cL)x||^2=|c|^2||Lx||^2.                              (2)
```

Equation `(1)` follows because multiplication by a nonzero complex scalar is a homeomorphism of
the target.  Equation `(2)` is the normed-space scaling law.  Both statements are proved in Lean.

## Positive HT content

The strict source-conormal refinement theorem proves that a nonzero infinite-support constraint
forces genuinely new clock-open sets.  The present theorem identifies exactly what those opens
remember: the projective conormal line.  They do not remember a preferred nonzero vector on that
line or its capacity.

Thus a constrained HT realization has two separate boundary data:

```text
projective conormal corona line     -- topological datum,
Hermitian calibration on that line -- source metric datum.            (3)
```

Any proposed theorem deriving a numerical Ward bound from the refined topology alone is false.
The topology is identical after arbitrary nonzero rescaling, whereas the Ward energy changes by
the square of that rescaling.

## RH pressure test

For the squarefree Möbius--Gamma source, the exceptional reciprocal-horizon connection identifies
the relevant projective corona line.  The separately formalized Gamma contact transgression fixes
the distinguished coefficient `-2`, hence the four-unit input norm.  Neither result implies that
the Hardy realization of the same line is contractive.

The remaining RH theorem must therefore construct a **calibrated** comparison, not merely a
topological one:

```text
(source corona line, Gamma contact norm 4)
  -> (Hardy--Green corona conormal, current P_anti Q_sq).               (4)
```

The comparison in `(4)` must arise from the Euler--Gamma source integration object before its
Hardy divisor is expanded.  Proving only equality of the underlying corona lines cannot control
the norm.

## Verification

- direct Lean check of `SourceConormalProjectiveTopology.lean` passes;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced;
- the proof uses only the existing source-conormal topology and standard topological-vector-space
  facts.

## Gates

- [x] induced topology proved invariant under nonzero conormal rescaling
- [x] minimal source-conormal clock refinement proved projective
- [x] exact Hermitian norm scaling proved
- [x] topology-only numerical Ward bounds ruled out
- [x] positive calibrated-conormal successor isolated

