# Bifiltered scalarization and comparison law

- **ID:** `bifiltered-scalarization-comparison-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / REALIZATION NO-GO AND POSITIVE TOMOGRAPHY LAW
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [NOT NEW GENERAL MATHEMATICS]`
- **Formal file:**
  `formal/GaloisForLFunctions/HTGeometry/BifilteredScalarizationNoGo.lean`
- **Parent:** `../1-in-progress/hypertranscendental-constraint-hodge-duality.md`

## The theorem

Let a genuine constraint object have bidegree `(p,q) in N^2`, with `p` its internal
derived/conormal degree and `q` its source-face/descent degree.

1. Every additive scalar realization `w:N^2 -> N` is noninjective.
2. For positive weighted degree `w_(a,b)(p,q)=ap+bq`, the pure degrees `(b,0)` and `(0,a)`
   collide.
3. The paired observation

   ```text
   (p,q) |-> (p+q,p+2q)
   ```

   is injective.
4. The pairing of the two observations is essential.  The distinct packets

   ```text
   A={(1,1),(2,1)},
   B={(0,2),(3,0)}
   ```

   have the same separate ordinary-total-degree and `(1,2)`-weighted scalar spectra, but require
   different matchings.

Therefore one scalar proof chain cannot be faithful, two transverse scalar observations separate
individual bidegrees, and two unpaired spectral marginals still do not reconstruct a packet.

## Proof

For an additive `w`, put `a=w(1,0)` and `b=w(0,1)`.  Additivity gives

```text
w(n,0)=na,       w(0,n)=nb.
```

If either weight vanishes, one axis already collapses.  Otherwise

```text
w(b,0)=ba=ab=w(0,a),
```

and `(b,0)!=(0,a)`.

For the paired map, equality gives the two linear equations

```text
p+q=p'+q',
p+2q=p'+2q'.
```

Subtracting yields `q=q'`, then `p=p'`.  The packet ambiguity is the exact identity table

```text
p+q:   2=2, 3=3,
p+2q:  3=3, 4=4,
```

where the second matching is crossed.

## Formal capstones

- `scalarTotalDegree_pureAxis_collision`;
- `scalarTotalDegree_not_injective`;
- `natProd_addMonoidHom_not_injective`;
- `transverseScalarDegrees_injective`;
- `transverseScalarMarginal_pairing_ambiguity`.

## Scientific consequence

`[NO-GO]` A master scalar grading, one total complex, or one scalar spectrum cannot define a
source-faithful unified object with unbounded source and internal degrees.

`[POSITIVE THEOREM]` A transverse pair separates the bidegrees when both values remain attached to
the same class.

`[SECOND NO-GO]` Agreement of two unpaired spectra does not supply that attachment.

`[POSITIVE SUCCESSOR]` A viable unified field must carry cross-realization comparison data.  Joint
conservativity is a property of coupled functors over one source object, not of a collection of
spectral sets.

This is the exact grading-level content of the hypothesis that different obstruction chains may
be representations of one object.  The theorem does not prove that any analytic RH chains are so
coupled; it states the minimum comparison structure such a claim must construct.

## Novelty and anti-theatre gate

The arithmetic and linear-algebra statements are elementary and are not new general mathematics.
Their role is to kill a structurally false unified-field design and to impose an exact,
machine-checked comparison requirement on the HT classification conjecture.  Calling the paired
map itself a new theory would fail the anti-theatre gate.
