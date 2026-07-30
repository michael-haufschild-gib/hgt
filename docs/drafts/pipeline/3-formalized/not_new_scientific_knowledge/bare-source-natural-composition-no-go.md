# A bare source cannot naturally compose itself

- **ID:** `bare-source-natural-composition-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM TARGET / COMPOSITION-SELECTION NO-GO / NEW-PHYSICS DESIGN CONSTRAINT
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED YONEDA SHADOW]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO PHYSICS PROVED]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/BareSourceNaturalCompositionNoGo.lean`
- **Live parent:** `../../1-in-progress/composition-curvature-universal-law.md`
- **Related:** `../../1-in-progress/dynamical-composition-universal-law.md`,
  `../../1-in-progress/source-generated-ternary-reciprocity-law.md`

## Question

Can a raw collection of outcomes generate a nontrivial same-level composition law without added
incidence, order, coefficients, or target structure?

Demanding naturality under every relabeling and coarse-graining makes the answer exact.

## Binary natural-operation classification

Let a binary natural operation on bare sets be a family
\[
\mu_X:X\times X\longrightarrow X
\tag{BN.1}
\]
for every set \(X\), such that every map \(f:X\to Y\) obeys
\[
f(\mu_X(x_0,x_1))
=
\mu_Y(f(x_0),f(x_1)).
\tag{BN.2}
\]

### Theorem 1

`[PAPER-PROVED] [LEAN-PROVED]`

Every family `(BN.1)`--`(BN.2)` is exactly one coordinate projection:
\[
\boxed{
\mu_X(x_0,x_1)=x_0\ \text{for all }X,x_0,x_1
\quad\text{or}\quad
\mu_X(x_0,x_1)=x_1\ \text{for all }X,x_0,x_1.
}
\tag{BN.3}
\]

### Proof

Evaluate the operation on the two-point set
\[
\mathbf2=\{0,1\}.
\]
Its value \(\mu_{\mathbf2}(0,1)\) is either \(0\) or \(1\).

For arbitrary \(X\) and \(x_0,x_1\in X\), let
\[
f:\mathbf2\to X,\qquad f(0)=x_0,\quad f(1)=x_1.
\]
Naturality gives
\[
\mu_X(x_0,x_1)
=f(\mu_{\mathbf2}(0,1)).
\]
If the universal two-point value is \(0\), every \(\mu_X\) is first projection. If it is \(1\),
every \(\mu_X\) is second projection. \(\square\)

This is the binary Yoneda classification:
\[
\operatorname{Nat}(\operatorname{Hom}(\mathbf2,-),\operatorname{Id})
\cong \operatorname{Id}(\mathbf2)\cong\mathbf2.
\]

### Corollary 2

`[PAPER-PROVED] [LEAN-PROVED]`

No binary natural operation on all bare sets is commutative.

### Proof

On \(\mathbf2\), neither first nor second projection is invariant under exchanging \(0\) and \(1\).
\(\square\)

## Exact meaning

The theorem kills a hidden premise in several completion conjectures:

```text
raw outcomes
  -/-> canonical nontrivial outcome × outcome -> outcome.
```

Same-type closure cannot be generated naturally from the underlying outcome set alone. Any
nontrivial operation must use additional source structure or change codomain.

The positive survivor is:

```text
raw source graph/incidence
  -> freely adjoin paths, spans, or higher fillers
  -> composition lives in a larger completion
  -> only later may a source law identify or quotient composites.
```

Thus the first candidate-new mathematical object cannot be a magically selected multiplication on
the original carrier. It must be a source-relative completion tower whose successive levels have
different types.

## Parent-theory audit

The theorem is a direct Yoneda/parametricity shadow and is not new mathematics.

Established higher-composition parents already implement the positive survivor:

- [Dyckerhoff--Kapranov](https://arxiv.org/abs/1212.3563) introduce 2-Segal spaces, in which
  higher coherence rather than a single-valued multiplication controls Hall-type composition;
- [Gal--Gal](https://arxiv.org/abs/1905.03376) identify higher Segal conditions with coherent
  \(A_\infty\)-algebra objects in categories of correspondences; and
- [Gálvez-Carrillo--Kock--Tonks](https://arxiv.org/abs/1404.3202) obtain incidence coalgebras from
  decomposition spaces, whose exactness condition is weaker than the Segal condition.

Free categories, Segal completion, bar/cobar constructions, small-object arguments, and
decomposition spaces already adjoin or organize composites. Therefore “composition requires
higher fillers” is occupied mathematics.

## Failure-driven stronger conjecture

`[CONJECTURE; PROOF ROUTE UNKNOWN]`

> **No physical event has its consequence in the world that existed before it. Time is the
> minimal enlargement required to make consequences composable.**

Technical version: a primitive incompatibility source \(S_0\) generates a tower
\[
S_0\longrightarrow S_1\longrightarrow S_2\longrightarrow\cdots,
\qquad
S_{n+1}=\mathsf{PosFill}(S_n),
\tag{BN.4}
\]
where \(\mathsf{PosFill}\) minimally adjoins:

1. missing composite fillers;
2. their coherent comparisons;
3. a source-generated dagger and positive public report; and
4. no same-level quotient not forced by complete counterfactual incidence.

Quantum phase is conjectured to be the first projective filler obstruction; internal forces the
vertical comparison curvature; gravity the failure of positive public anchors to agree across
successive enlargement; matter stable comparison correspondences; Hypertranscendence the failure
of the completion tower to stabilize in any finite differential-algebraic reporter.

## Why this is not yet a result

`(BN.4)` currently names desired behavior. It does not define \(\mathsf{PosFill}\), prove
existence, prove minimality, select positivity, recover a causal cone, or select the Standard
Model. Known free and fibrant completions give many possible towers and generally add far more
structure than observed physics.

The candidate becomes new mathematics only if complete source data uniquely select the positive
completion tower and its equivalences, rather than if a known Segal/2-Segal completion is chosen.

## Exact open core

`[OPEN CORE: SOURCE-POSITIVE FILLER UNIVERSAL PROPERTY]`

Define a category of finite raw incompatibility sources and a category of positive coherent
completion towers, without supplied scalar field, dagger, norm, composition, spacetime, or target
gauge group. Construct a left-universal completion
\[
\mathsf{PosFill}^{\infty}
\]
whose unit:

1. preserves and recovers all source incidence;
2. is nontrivial on the minimal hollow triangle/projective square;
3. excludes projection-only and free-path spectator phases by an intrinsic minimality property;
4. generates rather than assumes its positive coefficient category;
5. has inequivalent vertical and public-anchor comparison sectors; and
6. possesses a finite invariant not shared by ordinary free, Segal, 2-Segal, or operator-system
   completions.

## Hostile-review verdict

- **Theorem novelty:** `REDISCOVERED`. Direct Yoneda.
- **Bare-set composition:** `FALSIFIED`. Only projections exist.
- **Higher-filler remedy:** `BRIDGE`. Free/Segal/2-Segal/decomposition completion is established.
- **Physical tower:** `SURVIVES PRELIMINARY ATTACK` only as a conjecture. Positivity, unique
  minimality, physical sectors, continuum dynamics, and prediction remain open.
- **Nature status:** do not write.

## Lean status

Unconditional declarations:

- `binaryNaturalOperation_eq_projection`; and
- `no_commutative_binaryNaturalOperation`.

Their statements quantify over all small bare types and every map between them. They assume no
composition, algebra, topology, probability, spacetime, or physical premise.
