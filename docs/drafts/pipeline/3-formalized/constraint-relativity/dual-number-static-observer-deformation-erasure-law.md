# Dual-number static observer deformation-erasure law

- **ID:** `dual-number-static-observer-deformation-erasure-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE] [FORMALIZED IN LEAN]`
- **Role:** minimal countermodel to static observer reconstruction; positive mixed-cell
  reconstruction theorem.
- **Novelty:** standard module theory. Its use as the decisive gate for heterogeneous
  law-deformation descent is new internal synthesis, not an independent novelty claim.

## Goal

Show exactly why faithful, exact, conservative observer functors can reconstruct static objects
while erasing the deformation class that distinguishes their source laws. Identify minimal mixed
synchronization data that restores the lost law.

## Theorem 1: a faithful exact observer erases the full extension class

Let `k` be a field and

\[
 A=k[\varepsilon]/(\varepsilon^2).
 \tag{1}
\]

Let

\[
 U:A\text{-Mod}_{\rm fin}\longrightarrow k\text{-Vect}_{\rm fin}
 \tag{2}
\]

forget the `A`-action. Then `U` is faithful, exact, and conservative. However, the sequence

\[
 0\longrightarrow k
 \xrightarrow{\;1\mapsto\varepsilon\;}
 A
 \xrightarrow{\;a+b\varepsilon\mapsto a\;}
 k
 \longrightarrow0
 \tag{3}
\]

is nonsplit as an `A`-module extension and split after applying `U`. In particular,

\[
 \operatorname{Ext}^1_A(k,k)\cong k,
 \qquad
 \operatorname{Ext}^1_k(k,k)=0.
 \tag{4}
\]

### Proof

Restriction of scalars does not change underlying maps or vector-space kernels and cokernels, so
`U` is faithful and exact. If an `A`-linear map is an isomorphism after forgetting, its inverse as
a set map commutes with the `A`-action by conjugating the intertwining identity; hence `U` is
conservative.

If `(3)` split `A`-linearly, there would be `s:k->A` with quotient composite the identity. Put
\(s(1)=1+c\varepsilon\). Because \(\varepsilon\) acts trivially on `k`, `A`-linearity would give

\[
 0=s(\varepsilon\cdot1)=\varepsilon s(1)=\varepsilon,
\]

a contradiction. As vector spaces, \(A=k\cdot1\oplus k\cdot\varepsilon\), so `(3)` splits
after forgetting.

For `(4)`, resolve the residue module by the periodic free resolution

\[
 \cdots\xrightarrow{\varepsilon}A
 \xrightarrow{\varepsilon}A
 \xrightarrow{\varepsilon}A
 \longrightarrow k\longrightarrow0.
 \tag{5}
\]

Applying `Hom_A(-,k)` gives zero differentials because \(\varepsilon\) annihilates `k`, so
degree-one cohomology is \(\operatorname{Hom}_A(A,k)\cong k\). Every short exact sequence of
vector spaces splits, giving
`Ext^1_k(k,k)=0`. QED.

## Theorem 2: one mixed comparison cell reconstructs the source action

Giving a finite `A`-module is equivalent to giving a finite-dimensional vector space `V` and an
endomorphism

\[
 N:V\to V,
 \qquad N^2=0,
 \tag{6}
\]

where \(\varepsilon\) acts as `N`. Put `F=ker N`. Then

\[
 \theta_N:V/F\longrightarrow F,
 \qquad
 [v]\longmapsto Nv
 \tag{7}
\]

is a well-defined injection.

Conversely, given `(V,F,theta)` with `F` a subspace and `theta:V/F->F` injective, define

\[
 N=\iota_F\,\theta\,q_F.
 \tag{8}
\]

Then `N^2=0` and `ker N=F`. These constructions are mutually inverse.

### Proof

If \(v-v'\in F=\ker N\), then `Nv=Nv'`, so `(7)` is well defined. If
\(\theta_N([v])=0\), then \(v\in\ker N=F\), hence `[v]=0`; thus it is injective.

For `(8)`, \(q_F\iota_F=0\), so `N^2=0`. Also \(F\subseteq\ker N\). If `Nv=0`, injectivity of
`theta` implies `q_F(v)=0`, so \(v\in F\); hence `ker N=F`. Finally `(7)` applied to `(8)` recovers
`theta`, and `(8)` applied to `(7)` recovers `N`. QED.

## Interpretation

The marginal observer data `V` and `F` do not determine the dual-number law: many injections
`V/F->F` yield different nilpotent actions. The mixed synchronization cell `theta` reconstructs
it exactly.

Therefore:

\[
\boxed{
\text{static joint conservativity}
\not\Rightarrow
\text{deformation conservativity}.}
\tag{9}
\]

A candidate meta-theory must reconstruct which heterogeneous observer changes are deformations of
one source law. Static object values, even under faithful exact conservative realization, are
insufficient.

## No-go closure

- **Exact killing mechanism:** restriction of scalars annihilates the nonzero source
  `Ext^1` class while remaining faithful, exact, and conservative on objects and morphisms.
- **Strongest positive survivor:** the mixed cell `theta:V/F->F` reconstructs the square-zero
  source action exactly.
- **New insight:** law information can live in synchronization of observer deformations rather
  than in any observer object.
- **Status:** dependency-closed paper proof; standard algebraic parent.

## Lean-return note

Formalized; see `dual-number-static-observer-deformation-erasure-law-formalized.md`.  The note below was written before that work and is kept for the record: it is no longer a restriction.

> No Lean work is authorized. If later requested, formalize the nonsplitting sequence and the
> `N^2=0` reconstruction separately. Do not couple to RH in the generic file.

## Log

- 2026-08-08 — extracted from foundational-program census.

## Formalized companion

`dual-number-static-observer-deformation-erasure-law-formalized.md` (same directory).
