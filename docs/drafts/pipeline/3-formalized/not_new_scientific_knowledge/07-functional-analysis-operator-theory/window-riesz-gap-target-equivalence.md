# Window Riesz gap is a consumer unless a source homotopy is proved

- **ID:** `window-riesz-gap-target-equivalence`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-D TERMINAL AUDIT (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Input:** `../../5-failed/completed-source-window-index-amplifier.md`

## Statement

Let `D` be a bounded Jordan domain and let

```text
F(z)=1+K(z)
```

be a holomorphic trace-class Fredholm family on a neighbourhood of `closure(D)`, invertible on
`boundary(D)`.  Put

```text
d(z)=det_F(F(z)).
```

Assume a proposed reflection-odd source model has the characteristic-divisor property

```text
ord_z(d)=multiplicity of the free FE--Schwarz orbit represented by z.       (C)
```

Then the following are equivalent:

1. the total analytic-Fredholm root multiplicity in `D` is zero; when `F(z)=z-A` for a
   compact-resolvent closed operator, equivalently the Riesz projection of `A` on `D` is zero;
2. `F(z)` is invertible for every `z in D`;
3. `d` has no zero in `D`;
4. the boundary winding of `d` is zero;
5. no free reflection orbit lies in the corresponding height window.

Thus constructing the closed family and proving `(C)` supplies an exact reader, not a source gap.
Projection vanishing is the local RH target itself.

A finite bound on the boundary resolvent does not imply any of the five conditions.  A genuine
sufficient source theorem is instead a boundary homotopy estimate relative to a zero-index reference,
for example

```text
sup_(z in boundary(D)) ||F_0(z)^(-1)(F_1(z)-F_0(z))|| < 1,                 (H)
```

where `F_0` is zero-free in `D`.  Estimate `(H)` keeps the linear homotopy invertible on the boundary,
so the winding and zero count remain zero.  Proving `(H)` from the completed Euler--Gamma source is
the substantive missing theorem; contour Fredholmness and boundedness alone do not approach it.

## Proof of the equivalence

Analytic Fredholm theory identifies the algebraic multiplicity of a characteristic value of `F`
with the zero order of its Fredholm determinant.  Hence the total root multiplicity is zero exactly
when `d` has no zero in `D`.  In the linear case `F(z)=z-A`, the same multiplicity is the rank of the
sum of the finite-rank Riesz projections for the isolated spectrum in `D`; that sum is zero exactly
when the spectral set is empty.  This proves the equivalence of 1--3.

Because `d` is holomorphic and nonzero on the boundary, the argument principle gives

```text
wind_(boundary(D))(d)
 = sum_(z in D) ord_z(d).                                  (1)
```

Every summand is nonnegative.  Thus the winding is zero exactly when there is no zero.  This proves
the equivalence with 4.  Assumption `(C)` identifies the right side of `(1)` with the free-orbit
multiplicity, proving equivalence with 5.

## Boundary-resolvent counterexample

Take the scalar family

```text
F(z)=z
```

on the unit disk.  It is invertible on the unit circle and

```text
sup_(|z|=1) |F(z)^(-1)|=1,
```

but it has one zero inside and boundary winding one.  More generally, for the closed scalar operator
`A=0`, the resolvent on the circle `|z|=r` has finite norm `1/r` while its Riesz projection is the
identity.  Therefore finiteness, trace-ideal membership, or an explicit upper bound for a contour
resolvent does not imply an empty spectral window.

## Relative homotopy theorem

Let `F_t=F_0+t(F_1-F_0)`.  On the boundary,

```text
F_t=F_0(1+t F_0^(-1)(F_1-F_0)).
```

Under `(H)`, the second factor is invertible for every `0<=t<=1` by the Neumann series.  Hence
`det_F(F_t)` is a homotopy of nonzero boundary loops, so its winding is constant.  If `F_0` is
zero-free, its winding is zero, and equation `(1)` forces `F_1` to be zero-free as well.

This proves that a relative `<1` estimate is sufficient.  It is not automatic from construction of
the model: it compares the completed source with a specified zero-index reference in exactly the
topology that prevents a characteristic value from entering the window.

## Application to the audited Route D candidates

The possible references considered in Route D do not supply `(H)`:

- the completion-compatible all-place local-ratio multiplier is identically `1`, so it has no
  characteristic Xi divisor to compare;
- the Marcinkiewicz unit-tail extension and every bounded scalar pushout split;
- the canonical residue graph is nonclosable off RH and cannot define `F_1` unconditionally;
- lifted unit and phase classes have zero connecting index;
- restricting Euler Pick nodes retains the global negative-square index rather than producing a
  height-excisive family; and
- the genuine semilocal prolate deformation still lacks a source-selected closed realization and
  determinant-compatible relative estimate.

Accordingly, the phrase “prove a Riesz-projection gap” does not identify unfinished functional
analysis after the source model.  It asks for the new source homotopy `(H)`, and no current Route D
construction provides either side of that comparison with all required properties.

## Exact route boundary

- `[PROVED]` A characteristic closed family converts its determinant winding into the free-orbit
  count.
- `[PROVED]` Its zero Riesz projection is exactly the desired local free-orbit exclusion.
- `[PROVED]` Contour resolvent bounds alone do not imply projection vanishing.
- `[PROVED]` A relative boundary norm smaller than one against a zero-index reference is sufficient.
- `[OPEN OUTSIDE ROUTE D]` Construct such a reference and prove the relative estimate from a genuinely
  new source geometry.  This would reopen Route D as a consumer but is not produced by Route D.

## Novelty audit

Analytic Fredholm determinants, the argument principle, Riesz projections, homotopy invariance, and
the Neumann-series criterion are standard.  Their assembly gives the terminal route audit but is not
new scientific knowledge.

## Lean formalization (2026-08-25)

`GaloisForLFunctions.HTGeometry.WindowRieszGapTargetEquivalence` proves the full five-way theorem as
`windowRieszGapTarget_equivalent`.  `BoundedJordanDomain` is a chosen
Carathéodory--Schoenflies chart, so its image is an arbitrary bounded Jordan domain without a smooth
boundary assumption.  `TraceClassKernelFamily` carries the Hilbert--Schmidt kernel and the literal
Schatten-`1` proof; `IsHolomorphicFredholmOn` bundles analyticity of `I+K(z)` and its canonical
ordinary Fredholm determinant on one open neighbourhood.

The dependency-closed proof is split into exact reusable leaves:

- `JordanWindowArgumentPrinciple` proves arbitrary-multiplicity zero finiteness, the boundary
  winding formula, and zero-count/zero-free equivalence using an inner-circle homotopy;
- `KernelFredholmDeterminant` defines
  `det_F(I+K)=det₂(-K) exp(tr K)` and proves its zero set is exactly the noninvertibility locus;
- `ClosedCompactResolventWindowRiesz` proves the compact-resolvent Fredholm-pencil equivalence and
  canonical window spectral-range projection vanishing criterion;
- `WindowCompactRiesz` supplies the literal contour Riesz-projection zero equivalence for compact
  operator windows; and
- `WindowRieszRelativeNeumann` proves exact relative estimate `(H)` and the scalar boundary-resolvent
  counterexample.

The characteristic-divisor law `(C)` is used exactly as stated.  No source exclusion or determinant
nonvanishing is assumed.  Targeted leaf build
`lake build GaloisForLFunctions.HTGeometry.WindowRieszGapTargetEquivalence` passes.  Batched axiom
reports for every new declaration contain only `propext`, `Classical.choice`, and `Quot.sound`.
