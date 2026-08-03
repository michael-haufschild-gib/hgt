# Source-pointed observation network law

- **ID:** `resolved-source-augmentation-conservativity-law`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL EXACT-DESCENT / SOURCE-SUPPORT LAW
- **Status:** `[PAPER PROOF COMPLETE] [LEAN CORE COMPLETE] [NOVELTY UNVERIFIED]`
- **Stage-1 card:**
  `../../../1-in-progress/resolved-defect-augmentation-conservativity-law.md`

## Main theorem: source-pointed observation network law

Let

```text
E_0 --T_0--> E_1 --T_1--> ... --T_(m-1)--> E_m
```

be linear maps and let `S_0 <= E_0` be the actual source sector.  Propagate it by

```text
S_(i+1) = T_i(S_i).
```

Write `Conservative(T,S)` when `S intersect ker(T)={0}`.  Then

```text
Conservative(T_(m-1)...T_0, S_0)
  iff Conservative(T_i,S_i) for every i.                 (0)
```

For two stages this is the exact identity

```text
ker(g f) = f^(-1)(ker g)
```

restricted to `S`: if `gf` is conservative on `S`, then `f` is conservative on `S`, and `g` is
conservative on `f(S)`; the converse follows by applying those two implications in order.  The
finite statement `(0)` follows by induction.  Thus every serial route has a unique logical audit:
propagate the actual source sector and find the first edge whose kernel meets it.  No later reader,
positivity form, quotient, or completion can restore information killed at that edge.

If the spaces are normed and each edge has a source-relative lower bound

```text
||T_i x|| >= c_i ||x||  (x in S_i),  c_i > 0,
```

then the composite has lower bound `product_i c_i`.  This follows by successive substitution.  It
is the quantitative form of `(0)`: algebraic separation is stagewise injectivity; stable separation
is a nonzero lower modulus along the whole propagated route.  A cofinal family may therefore remain
injective at every finite stage while its inverse conditioning diverges and every uniformly regular
reader loses fixed source separation.

Finite augmentation below is one edge of this general law, not the parent law itself.

For parallel readers `f:E->F` and `h:E->H`, retain both outputs by `(f,h):E->F x H`. Then

```text
ker(f,h) = ker(f) intersect ker(h),
Conservative((f,h),S)
  iff S intersect ker(f) intersect ker(h) = {0}.          (0p)
```

The proof is coordinatewise: `(f(x),h(x))=0` iff both coordinates vanish.  In contrast,
`ker(f)<=ker(gf)` for every serial postprocessor `g`.  Thus a parallel coordinate can protect
information only when retained before a lossy quotient; no later reader can reconstruct it.  The
serial law and `(0p)` recursively compute the invisible radical of every finite linear observation
network built from composition and parallel products.

## Finite augmentation corollary

Let `R` be a commutative ring, let `X,Z,W` be `R`-modules, and let

```text
D : X -> Z^n,       epsilon : Z^n -> Z,       O : Z -> W
```

be linear maps, with `n>=1`.  Think of `D` as a resolved family of transported factor defects and
`epsilon(z)=sum_i z_i` as ordinary composition/augmentation.  Let `S<=Z^n` be a source-selected
resolved sector containing `range(D)`.

### A. Universal cancellation sequence

Define

```text
boundary : Z^(n-1) -> Z^n,
boundary(w_0,...,w_(n-2))=(-sum_i w_i,w_0,...,w_(n-2)).   (1)
```

Then

```text
0 -> Z^(n-1) --boundary--> Z^n --epsilon--> Z -> 0        (2)
```

is exact.  In particular,

```text
ker(epsilon)=range(boundary).                             (3)
```

Thus ordinary conservation `epsilon D=0` says exactly that every resolved defect lies in the
universal zero-sum cancellation module.  It does not say `D=0`.

### B. Resolved source-support criterion

The following are equivalent:

```text
(i)   epsilon is conservative on S;
(ii)  S intersect ker(epsilon)={0};
(iii) S intersect range(boundary)={0};
(iv)  for every d in S, epsilon(d)=0 implies d=0.         (4)
```

When these conditions hold and `range(D)<=S`,

```text
epsilon D=0  iff  D=0.                                   (5)
```

More generally, observation after augmentation can recover the resolved defect only if
`O epsilon` is conservative on `S`; no post-augmentation observer can repair a nonzero element of
`S intersect ker(epsilon)`.

### C. Factorized covariance

For a composable chain

```text
X_0 --T_0--> X_1 --T_1--> ... --T_(n-1)--> X_n
```

with endomorphisms `C_i` on `X_i`, define

```text
delta_i=C_(i+1)T_i-T_i C_i.                              (6)
```

Transport `delta_i` through every later and earlier factor to an endpoint map `D_i:X_0->X_n`.
Then telescoping gives

```text
C_n(T_(n-1)...T_0)-(T_(n-1)...T_0)C_0=sum_i D_i.          (7)
```

Consequently `(5)` is the exact criterion under which covariance of a composite implies
covariance of all its transported factor defects on the actual source sector.

## Proof

For `(2)`, `boundary` is injective because its last `n-1` coordinates are the input.  Its coordinate
sum is zero, so `range(boundary)<=ker(epsilon)`.  Conversely, if

```text
z_0+...+z_(n-1)=0,
```

put `w_i=z_(i+1)`.  Then `z_0=-sum_i w_i`, hence `z=boundary(w)`.  Augmentation is surjective by
`(z,0,...,0)|->z`.  This proves exactness and `(3)`.

Conditions `(i)` and `(ii)` are the definition of conservativity.  Substitute `(3)` to obtain
`(iii)`.  The standard disjoint-submodule criterion gives `(iv)`: an element of `S` with zero
augmentation lies in both `S` and `ker(epsilon)`.  Conversely, `(iv)` kills every element of that
intersection.  If `range(D)<=S`, applying `(iv)` pointwise proves the forward direction of `(5)`;
the reverse direction is immediate.

For `(7)`, insert and subtract the intermediate terms

```text
T_(n-1)...T_(i+1) C_(i+1) T_i...T_0
```

between the two endpoint expressions.  Consecutive intermediate terms cancel, leaving precisely
the transported copies of `(6)`.  This is the finite Leibniz/telescoping identity for covariance
defects.  `QED`

## Completion law

Let the modules now be normed and let `S_alg` be the algebraic source sector.  Algebraic
conservativity is not stable under completion.  The completed inference is valid exactly on a
completed sector `S_bar` satisfying

```text
S_bar intersect ker(epsilon)={0}.                         (8)
```

For stable bounded recovery, mere `(8)` must be strengthened to a uniform estimate

```text
||epsilon d|| >= c ||d||  for all d in S_bar              (9)
```

with `c>0`.  If there are unit vectors `d_k in S_alg` with `epsilon d_k ->0`, no bounded inverse
exists on the augmented range.  If a nonzero zero-sum vector enters the completed sector, even
injectivity fails.  A closed relation that retains a nonzero output while its input tends to zero
acquires a vertical fibre; if such outputs are dense, the relation becomes maximally vertical.

Equation `(8)` is algebraic/topological conservativity.  Equation `(9)` is its quantitative closed-
range form.  Disjoint closed grades with positive angle, or a pointed cone on which augmentation is
strictly positive, are sufficient implementations; labels without `(8)` or `(9)` are not.

## Riemann consequence

The finite arithmetic Green map has two factor defects.  With `epsilon(u,v)=u+v`, Lean proves

```text
D_Green(a)=(u(a),-u(a)),
epsilon D_Green=0                                         (10)
```

unconditionally.  At a divisor copy `rho`, one basis source detects

```text
u=0  iff  2 Re(rho)-1=0.                                  (11)
```

Therefore total Frobenius covariance of the Green composite carries no zero-exclusion content by
itself.  The exact RH-producing statement is:

```text
there exists a source-derived completed sector S such that
  range(D_Green)<=S
and
  S intersect ker(epsilon)={0}.                           (12)
```

Indeed `(10)` and `(12)` imply `D_Green=0`; `(11)` at every divisor copy gives RH.  Conversely, RH
makes `D_Green=0`, so `(12)` holds with the zero sector.  Nontrivial research content is a canonical
arithmetic `S`, not the existential equivalence.

The current corpus determines both sides of the frontier:

1. the ordered Calderón--Witt cross-effect supplies a nonzero, source-faithful resolved arithmetic
   boundary which ordinary cup augmentation kills;
2. each finite balanced Hellinger--Gamma coface range is transverse to the augmentation kernel;
3. no nonzero Green antidiagonal can therefore be represented by merely reusing one such finite
   grade;
4. restoring orthogonal depth labels still does not close the bridge: factorial damping and
   adjacent exactness put conserved endpoint charge in the vertical graph closure;
5. a successful construction must join factor provenance with independent physical-jet/source
   support before completion and prove `(8)`, preferably `(9)`.

This replaces the weaker phrase “vanishing Frobenius--Hodge commutator.”  Composite commutator
vanishing is already `(10)`.  Missing theorem is resolved source-support plus completed
augmentation conservativity.

## Why this is parent to Cartan conservation

Cartan slope is one coordinate detector on a resolved defect.  A reflected pair has slopes
`mu,-mu`, so invariant scalarization augments them to zero.  The rank-one Cartan fate theorem
classifies what happens when one nevertheless tries to retain `mu`: radicalization, reciprocal
condition growth, indefinite cross-pairing, singular grading, or verticality.  Those are concrete
ways that `(4)`, `(8)`, or `(9)` fail.  Zero-Cartan source support is the rank-one special case of
`range(D)<=S` with augmentation conservative on `S`.

Thus parent statement is not “purity cannot be created by regular transport.”  It is:

> **Conservation is an augmented statement.  It controls resolved source defects exactly when the
> actual completed source sector is transverse to the augmentation kernel.**

## Lean correspondence

Already formalized unconditionally:

- source-pointed two-stage chain law, failure propagation, and multiplication of uniform lower
  bounds: `SourcePointedConservativityChainLaw.lean`;
- parallel kernel intersection, common-radical conservativity, and irreversibility under
  postprocessing: `SourcePointedObservationNetworkLaw.lean`;
- two-factor identity `(7)` and exact two-channel sequence `(3)`:
  `ResolvedDefectConservationLaw.lean`;
- criterion `(5)` for a specified sector:
  `observedDefect_eq_zero_iff_of_conservativeOn`;
- arithmetic cancellation `(10)`, detector `(11)`, and grade-separated RH implication:
  `DeningerGreenInternalDefectCancellationLaw.lean`;
- finite Hellinger--Gamma transversality:
  `DeningerResolvedDefectHellingerGammaBalancedCofaceNoGo.lean`;
- nonzero resolved arithmetic cross-effect killed by codiagonal:
  `DeningerCalderonWittResolvedCrossEffectBoundary.lean`;
- completed vertical obstruction:
  `DeningerCalderonWittCompletedXiHellingerGammaGradedVerticalObstruction.lean`;
- maximally vertical closed-relation consequence:
  `DeningerMeyerHalfDensityXiGraphClosure.lean` and the current publication paper certificate.

**The finite serial route law `(0)` itself**, which the card obtained from the two-stage law "by
induction", is now formalized in `SourcePointedFiniteRouteLaw.lean`:

- `routeComp`, `routeSector` — the composite of the first `m` edges and the sector propagated to
  stage `m`, with `routeSector_eq_map`: propagating the sector is mapping it along the composite.
- `isConservativeOn_routeComp_iff` — **`(0)` for a route of any finite length**: the route is
  conservative on its initial source sector exactly when every edge is conservative on the sector
  propagated to that edge.  This is the statement that every serial route has a unique logical
  audit.
- `not_isConservativeOn_routeComp_of_edge` — failure at one edge is failure of the whole route.
- `norm_routeComp_lower` — **the quantitative form**: a route whose `i`-th edge has source-relative
  lower bound `c i` has lower bound `∏ c i`.  This is what makes the card's point about cofinal
  families precise — every finite stage can be injective while the product tends to zero.
- `isUniformlyConservativeOn_routeComp` — the corresponding uniform conservativity.

The remaining source-specific theorem is not abstract infrastructure: construct the arithmetic
sector in `(12)`.  Arbitrary finite exactness, homogeneous arbitrary-factor telescoping, and the
uniform normed sufficient criterion for `(9)` are now formalized in
`ResolvedSourceAugmentationConservativityLaw.lean`.

## Antagonist verdict

- The algebraic sequence is elementary; no novelty is claimed for it.
- The frontier correction is nontrivial: unconditional Green covariance is proved to be exact
  information-destroying cancellation, so a previously named target cannot imply RH.
- Law is more universal than Cartan conservation because it identifies common logical structure of
  source support, factor transport, scalar positivity, grade retention, and completion.
- Law does not prove `(12)` and therefore does not prove RH.
- Scientific value depends on demonstrating that all cited route maps really factor through the
  stated augmentation; paper must give exact maps, not analogy.

## Log

- 2026-08-03 — Audited the Lean correspondence against the numbered statements rather than the
  module list.  Every claimed module exists and audits clean, but only the *two-stage* chain law and
  its two-stage lower-bound product were formalized; the card's `(0)` is the finite `m`-stage
  statement, obtained "by induction", and that induction was missing.  Formalized it, together with
  the explicit product lower bound `∏ c i` rather than only the existential uniform bound.
