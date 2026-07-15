# Jet-horizon translation-gauge classification

- **ID:** `jet-horizon-translation-gauge-classification`
- **Stage:** 2-fully-proven
- **Type:** DIFFERENTIAL-ALGEBRAIC RECONSTRUCTION / GAUGE CLASSIFICATION
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY CANDIDATE] [STRUCTURALLY SIGNIFICANT]`
- **Source:** `nonlinear-rational-observation-curve-horizon-reconstruction`
- **Statement:** For a differential-generic point of an irreducible affine variety, a positive
  derivative horizon loses information at any depth exactly when the variety has a flat additive
  cylinder factor. The lost data form a finite tower of additive integration torsors.

## Set-up

Let `C` be an algebraically closed constant field of characteristic zero and let `U` be a
sufficiently saturated differentially closed extension. Let `Y subset A^m_C` be an irreducible
affine variety of dimension `d`. A tuple `y=(y_1,...,y_m) in Y(U)` is **differential-generic on
Y** when it has no differential-algebraic constraint over `C` beyond the algebraic constraint
`y in Y` and its differentiated consequences. Put

```text
F=C<y_1,...,y_m>,
H_n(Y)=C<delta^n y_1,...,delta^n y_m>,   n>=1,             (1)
A=Stab_trans(Y)={a in G_a^m : Y+a=Y},
K_n=ker(delta^n:U^m -> U^m).                              (2)
```

The group `A` is a linear subspace of `G_a^m`.

## Theorem

### 1. Generic embedding groupoid

For every differential-field embedding

```text
sigma:F -> U   over H_n(Y),
```

the displacement

```text
h_sigma=sigma(y)-y
```

satisfies

```text
h_sigma in A(U) intersection K_n.                         (3)
```

Conversely, if `h in A(U) intersection K_n` and `y` is differential-generic over `C<h>`, then
translation `y |-> y+h` induces an `H_n(Y)`-embedding. Thus generic pairs with the same depth-`n`
horizon are exactly the pairs related by the differential additive translation group
`A(K_n)`.

This is an embedding groupoid in `U`, not in general an ordinary automorphism group of `F`.

### 2. Exact reconstruction criterion

For every `n>=1`,

```text
H_n(Y)=F  iff  A=0.                                       (4)
```

Equivalently, all positive horizon depths have the same binary reconstruction defect: a
translation-rigid algebraic constraint reconstructs its differential-generic point from every
finite-depth derivative tail, whereas an additive cylinder never does.

### 3. Canonical cylinder decomposition

Choose a linear complement `G_a^m=A direct_sum B` and put `Z=Y intersection B`. Translation
invariance gives an algebraic product, not merely a birational one:

```text
Y = A x Z,                  Stab_trans(Z)=0.               (5)
```

Writing the differential-generic point as `y=(a,z)`, equation `(4)` applied to `Z` gives

```text
F=C<a,z>,
H_n(Y)=C<delta^n a,z>.                                    (6)
```

The nonlinear reduced geometry is visible at every depth. Only the coordinates along the
maximal flat additive foliation lose their lower jets.

### 4. Successive-torsor law

For `j>=0`, set

```text
H_j=C<delta^j a,z>.
```

Then each adjacent layer

```text
H_j / H_(j+1)                                              (7)
```

is the Picard--Vessiot additive torsor for

```text
delta X=delta^(j+1)a,
```

with differential Galois group `G_a^r`, where `r=dim A`. Hence a depth-`n` horizon factors its
information loss canonically into `n` successive additive torsors. If `r>0`, every inclusion

```text
F=H_0 > H_1 > ... > H_n                                   (8)
```

is strict.

## Proof

### Embedding rigidity

Let `sigma:F -> U` fix `H_n(Y)` and put `h=sigma(y)-y`. Since `sigma` fixes `delta^n y`,

```text
delta^n h=0.                                               (9)
```

Therefore `h` is differentially algebraic over `C`. The field `C<y,h>` contains `C<y>`, whose
differential transcendence degree over `C` is `d`, while adjoining the differentially algebraic
tuple `h` cannot increase that degree. Hence

```text
dtrdeg(C<y,h>/C<h>)=d.                                    (10)
```

If `y` satisfied an extra ordinary algebraic equation over `C<h>`, then its ordinary
transcendence degree over `C<h>` would be less than `d`, forcing the differential transcendence
degree in `(10)` to be less than `d`. Thus `y` remains an algebraic generic point of `Y` over
`C<h>`.

For every `P in I(Y)`, the tuple `sigma(y)=y+h` lies in `Y`, so

```text
P(y+h)=0.                                                  (11)
```

Because `y` is generic on `Y` over `C<h>`, equation `(11)` says that translation by `h` maps
`Y_(C<h>)` into itself. Its image is an irreducible closed subvariety of the same dimension, so
the inclusion is equality. Therefore `h in Stab_trans(Y)(C<h>)=A(C<h>)`. Together with `(9)` this
proves `(3)`.

Conversely, translation by an `h in A intersection K_n` preserves every algebraic equation of
`Y` and preserves `delta^n y`; when `y` is generic over `C<h>`, substitution gives the stated
field embedding.

### Fixed-field separation and reconstruction

Quantifier elimination for `DCF_0` implies that the definable closure of a differential field is
the field itself. Consequently

```text
H_n(Y) = {f in F : sigma(f)=f for every H_n(Y)-embedding F -> U}.   (12)
```

If `A=0`, equation `(3)` makes every such embedding the identity, so `(12)` yields `F=H_n(Y)`.
If `A` is nonzero, any nonzero `c in A(C)` gives a nontrivial translation automorphism
`y |-> y+c` that fixes `delta^n y`; hence `H_n(Y)` is proper. This proves `(4)`.

### Splitting and the torsor tower

Choose `A^m=A direct_sum B`. If `(a,b) in Y`, translation by `-a in A` shows `(0,b) in Y`; the
reverse translation recovers the full fiber. Therefore `Y=A x (Y intersection B)` on algebraic
points, hence as reduced affine varieties. Any translation stabilizing `Z=Y intersection B`
would lift to a translation of `Y`, so `Z` has trivial stabilizer. This proves `(5)` and `(6)`.

Finally, `H_j` is generated over `H_(j+1)` by the vector `delta^j a`, which solves the first-order
inhomogeneous system in `(7)`. The corresponding unipotent fundamental matrix is

```text
[ I_r   delta^j a ]
[  0         1     ],
```

so the extension is Picard--Vessiot with additive group `G_a^r`. Constant translations make each
layer strict when `r>0`.

## Why the original automorphism claim was false

For `Y=A^1` and a differential indeterminate `x`,

```text
H_n=C<delta^n x>.
```

At `n>1`, the ordinary automorphisms of `C<x>/H_n` do not realize all of `ker(delta^n)` inside
`C<x>`. The information loss is instead resolved by the chain

```text
C<x> > C<delta x> > ... > C<delta^n x>,
```

one additive Picard--Vessiot torsor at a time. Replacing an ordinary fixed-field claim by the
embedding groupoid `(3)` and the tower `(7)` is essential, not terminological.

## New geometric and physical content

The result is a no-hair theorem for derivative horizons:

```text
finite-depth horizon hair = maximal affine-cylinder dimension.    (13)
```

The defect is independent of horizon depth and insensitive to all nonlinear reduced geometry.
Depth changes only the length of the unipotent integration tower.

Physically, `ker(delta^n)` is a finite clock-jet gauge: changing the first `n` integration data
does not change the observed tail. The algebraic constraint acts like an exact Higgs mechanism.
Every nonlinear direction fixes its clock jet; only flat additive directions retain gauge. This
does not turn the HT source into a flow. It describes the static equivalence relation induced by
forgetting finite jets.

The quotient `Y -> Y/A=Z` is the precise topology behind the horizon: leaves are affine spaces,
the leaf space is translation-rigid, and the horizon reconstructs the leaf-space coordinate at
every depth.

## Parent-theory and novelty gate

- Picard--Vessiot torsors and Kolchin's use of embeddings into a universal differential field are
  classical.
- Quantifier elimination and definable closure for `DCF_0` are classical.
- Constant affine-group differential invariants and jet/arc invariant theory are classical.
- The rational-curve theorem in the source card is a special case.
- No checked source states the combined arbitrary-variety classification `(3)--(8)`, the
  depth-independent criterion `(4)`, or the exact cylinder/torsor interpretation `(6)--(8)`.

The novelty label remains conservative until specialist and literature review. The theorem is not
claimed to be Fields-Medal scale merely because it closes the stated proof wall.

## Lean formalisation boundary

The exact first non-affine case is formalised in
`formal/GaloisForLFunctions/HTGeometry/NonlinearConstraintHorizon.lean`:

```text
z=x*y,
W=x' y''-x'' y' != 0
```

implies that every derivation-closed field containing `x'`, `y'`, and `z'` contains both `x` and
`y`. Lean verifies the explicit reconstruction identities and the intermediate-field theorem with
no axioms or placeholders. The general DCF embedding-groupoid theorem is not encoded as an
assumption.

## RH impact audit

`[FORMULATION TOOL; NOT RH PROGRESS]` Any multichannel source-pure model for completed zeta data
would now have to exhibit an actual affine-cylinder factor to support finite-jet information loss.
A nonlinear observation constraint with trivial translation stabilizer cannot hide an RH-relevant
branch behind any finite derivative horizon. No canonical affine observation variety for the zeta
field has been identified, so the result presently yields no zero-location claim.

## Gates

- [x] 0 -> 1 in-progress: gauge quotient conjecture and exact proof wall identified
- [x] 1 -> 2 fully-proven: embedding rigidity, DCF separation, cylinder splitting, and torsor
  tower proved; incorrect ordinary-automorphism formulation removed
- [ ] 2 -> 3 formalized: general affine-variety theorem requires a DCF/formal differential
  algebraic geometry layer; the bilinear nonlinear core is formalized separately
- [ ] 3 -> 4 publication-ready: external differential-algebra specialist and exhaustive
  literature audit

## References

- D. Marker, *Model Theory: An Introduction*, Chapter 4 and Section 7.4; differential closure,
  quantifier elimination, and differential Galois groups.
- P. J. Cassidy and M. F. Singer, *Galois theory of parameterized differential equations and
  linear differential algebraic groups*, for differential algebraic Galois groups.
- G. R. Maurischat, *Picard--Vessiot theory of differentially simple rings*, for the torsor
  formulation of Picard--Vessiot extensions.
- S. Bekbaev, *On rational differential invariants of the field of rational functions in several
  indeterminates under an action of a subgroup of the affine group*, for the affine-invariant
  parent theory.

## Log

- 2026-07-15 — conjectured that the horizon was an ordinary fixed field of `A(K_n)`.
- 2026-07-15 — affine-line falsification at depth `n>1` forced the embedding-groupoid correction.
- 2026-07-15 — proved embedding rigidity, the all-depth reconstruction criterion, exact cylinder
  splitting, and the successive additive-torsor law.
