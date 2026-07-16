# Fixed intrinsic HT dimension supports arbitrary derived source-coherence depth

- **ID:** `fixed-analytic-dimension-arbitrary-source-coherence`
- **Stage:** 2-fully-proven / Lean combinatorial core complete
- **Type:** THEOREM / ARCHITECTURAL NO-GO / POSITIVE REALIZATION LAW
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Parents:**
  - `../new_scientific_knowledge/boundary-wedge-uniform-ht-dimension-gap.md`
  - `../new_scientific_knowledge/hypertranscendental-hochster-source-coherence-duality.md`
- **Successors:**
  - `../../1-in-progress/hypertranscendental-constraint-sheaf-reconstruction-duality.md`
  - `../../1-in-progress/hypertranscendental-capacity-descent-postnikov-tower.md`

## Exact theorem

For every integer `m>=3`, there is a scalar meromorphic hypertranscendental source `F_m` whose
intrinsic analytic constraint dimension is exactly two and whose structural orbit module has
projective dimension exactly `m`:

```text
htDim(F_m)=2,                  pd Coh(F_m)=m.                         (1)
```

More precisely, take

```text
Delta_(r,s)=boundary(sigma^r) wedge boundary(sigma^s),   r,s>=2,    (2)
```

with the two simplex boundaries meeting only at their common vertex `0`.  Its facet-sewn analytic
realization satisfies

```text
htDim(Delta_(r,s))=2,
pd k[Delta_(r,s)]=r+s-1.                                      (3)
```

Thus `(1)` follows from `(r,s)=(2,m-1)`.

## Proof

The uniform boundary-wedge realization theorem proves the first equality in `(3)`.

Write the two vertex blocks as

```text
B_x={0,x_1,...,x_r},             B_y={0,y_1,...,y_s},
W={x_1,...,x_r,y_1,...,y_s}.                                  (4)
```

Deleting `0` turns each boundary into the facet opposite `0`.  Consequently the induced complex
on `W` is the disjoint union of two full simplices:

```text
Delta_(r,s)|W = sigma^(r-1) disjoint_union sigma^(s-1).         (5)
```

It has two connected components, so

```text
H_tilde^0(Delta_(r,s)|W;k) ~= k.                               (6)
```

Since `|W|=r+s`, Hochster's formula puts `(6)` in homological degree

```text
i=|W|-0-1=r+s-1.                                               (7)
```

Therefore `pd k[Delta_(r,s)]>=r+s-1`.

There are `n=r+s+1` vertices.  The whole wedge is connected.  In the Hochster formula, a class in
degree at least `n-1` could only come from reduced degree zero on the full vertex set or reduced
degree minus one on a nonempty induced complex.  The first vanishes by connectedness and the
second vanishes because every induced complex on a nonempty vertex set contains a vertex.  Hence

```text
pd k[Delta_(r,s)]<=n-2=r+s-1.                                 (8)
```

Equations `(7)` and `(8)` prove `(3)`.  For `m>=3`, the choice `r=2`, `s=m-1` has `r,s>=2` and
`r+s-1=m`.  `QED`

Equivalently, the wedge has Stanley--Reisner depth exactly two: connectedness gives depth at least
two, while the disconnected link of the common vertex gives depth at most two.

## No-go and positive law

> **NO-GO.** No function of intrinsic analytic HT dimension alone can bound the projective
> dimension, Postnikov height, or derived source-coherence amplitude of an HT constraint
> boundary.  In particular, there is no finite derived truncation theorem even on the stratum
> `htDim=2`.

The theorem has a nontrivial positive replacement:

> **FIXED-DIMENSION COHERENCE REALIZATION LAW.** Two intrinsic analytic constraint directions
> suffice to realize every finite source-coherence depth `m>=3` by a scalar meromorphic HT source.

Thus a thin analytic boundary need not be homologically shallow.  Analytic dimension measures the
number of active realization directions; derived amplitude measures the length of compatibility
failure among constraints.  They are independent axes of the theory.

## RH-facing consequence

An RH proof architecture cannot argue that a two-directional or otherwise low-dimensional source
model has only finitely many relevant derived obstruction layers.  Any truncation used in such a
proof must be justified by a source-specific arithmetic mechanism, not by analytic dimension.

The positive target is therefore a source-selected collapse law: identify an arithmetic datum
whose compatibility forces the unbounded kinematic tower to collapse, converge, or acquire a
canonical polarized limit.  The present theorem neither supplies such a datum nor asserts RH.

## Parent-theory and anti-theatre verdict

After erasing the HT vocabulary, the projective-dimension calculation is a direct application of
Hochster's formula and standard depth criteria for Stanley--Reisner rings.  The analytic
`htDim=2` realization is supplied by the separate boundary-wedge theorem.  Their conjunction is
useful and exact, but it introduces no new proof mechanism beyond its parents.

- `[PROOF GATE -- PASS]`
- `[SIGNIFICANCE AS ARCHITECTURAL NO-GO -- PASS]`
- `[PARENT-THEORY GATE -- FAIL FOR NEW KNOWLEDGE]`
- `[ANTI-THEATRE -- DOWNGRADE TO BRIDGE]`
- `[PAPER VERDICT]` Include as a corollary in the constraint-spectrum theory; it does not warrant
  a standalone paper.

## Lean boundary

The unconditional combinatorial core to formalize is:

1. after deleting the common vertex, a face lies entirely in the left block or entirely in the
   right block;
2. every same-block finite set is a face and no mixed edge is a face;
3. the block label is locally constant on faces but globally nonconstant;
4. every integer `m>=3` is `r+s-1` for some `r,s>=2`.

The general Hochster chain equivalence remains the correctly larger formal target.  No axiom or
structure field may be used to assume it.

## Gates

- [x] exact fixed-dimension family identified
- [x] exact projective dimension proved
- [x] every depth `m>=3` realized
- [x] strong no-go paired with a positive realization theorem
- [x] parent-theory reduction performed
- [x] anti-theatre downgrade recorded
- [x] unconditional Lean combinatorial core
- [ ] general Lean Hochster chain equivalence
