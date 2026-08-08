# Residue-preserving law-promotion anomaly trilemma

- **ID:** `residue-preserving-law-promotion-anomaly-trilemma`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NEW RH-ROUTE LEVERAGE]`
  `[NO RH CLAIM] [NO LEAN WRITTEN]`
- **Role:** first exact law-event classification theorem in Nomotopy; classifies every cell-attachment
  attempt to kill the physical cyclic-to-paracyclic defect while preserving source residue.
- **Novelty:** generic proof is elementary homological algebra. Candidate-new content is the exact
  promotion-anomaly-rank invariant and its application to the literal arithmetic source defect.

## Goal

The remaining arithmetic-source theorem asks that physical paracyclic defect become
null-homologous while literal cyclic residue remains a source cocycle. Determine what any genuine
law extension must add if defect has nonzero residue.

## Setup

Let `(C,d)` be a chain complex of vector spaces over field `k`. Let

\[
 R:C_n\longrightarrow W
 \tag{1}
\]

be a `W`-valued degree-`n` residue cocycle:

\[
 R\,d_{n+1}=0.
 \tag{2}
\]

Let `V` be defect-parameter space and let

\[
 Z:V\longrightarrow Z_n(C)=\ker d_n
 \tag{3}
\]

be linear. Attaching law cells to kill defects means adjoining `V` in degree `n+1` and setting

\[
 d'(0,v)=Z(v).
 \tag{4}
\]

## Theorem 1: no-surplus attachment criterion

The residue `R` extends unchanged to a cocycle on cell-attached complex `(C',d')` if and only if

\[
 \boxed{RZ=0.}
 \tag{5}
\]

If `Z` is surjective onto defect subspace `D`, a residue-preserving attachment kills every class
in `D` if and only if `R|_D=0`.

### Proof

There are no new degree-`n` vectors, so any unchanged extension satisfies `R'=R` there. Cocycle
condition on new cell `v` is

\[
 0=R'd'(0,v)=RZ(v).
\]

Thus `(5)` is necessary. It is sufficient because cocycle condition already holds on old
degree-`n+1` chains by `(2)`, and `(5)` checks every new generator. Surjective case is immediate.
QED.

## Theorem 2: minimal compensator rank

Suppose `RZ` is nonzero. Allow new compensator space `A` in degree `n`, with zero outgoing
differential, and attach `V` by

\[
 d'(0,v)=Z(v)+q(v),
 \qquad q:V\to A.
 \tag{6}
\]

Extend residue by a linear map `S:A->W`, so \(R'=R\oplus S\) in degree `n`. Then `R'` is a
cocycle exactly when

\[
 \boxed{RZ+Sq=0.}
 \tag{7}
\]

Every such compensator satisfies

\[
 \dim A\ge\operatorname{rank}(RZ).
 \tag{8}
\]

Equality is always achievable. Hence

\[
 \boxed{
 \operatorname{anomrank}_R(Z)
 :=\min\dim A
 =\operatorname{rank}(RZ).}
 \tag{9}
\]

### Proof

The only new cocycle condition is

\[
 0=R'd'(0,v)=RZ(v)+Sq(v),
\]

which proves `(7)`. It implies \(\operatorname{im}(RZ)\subseteq\operatorname{im}(S)\), hence

\[
 \operatorname{rank}(RZ)
 \le\operatorname{rank}S
 \le\dim A,
\]

proving `(8)`.

For equality, take

\[
 A=\operatorname{im}(RZ),
 \qquad q=RZ:V\to A,
 \qquad S=-\iota_A:A\hookrightarrow W.
\]

Then `(7)` holds and `dim A=rank(RZ)`. QED.

## Conservation interpretation

When \(RZ\ne0\), equation `(6)` does not make original defect charge disappear. It gives

\[
 [Z(v)]=-[q(v)]
 \tag{10}
\]

in extended homology, and `(7)` assigns opposite residue to compensator. Thus every extension
obeys exact trilemma:

\[
\boxed{
\begin{array}{c}
\text{do not kill charged defect},\\
\text{kill it and break source-residue cocyclicity},\\
\text{or transfer its charge to new compensating sector}.
\end{array}}
\tag{11}
\]

There is no fourth option that simultaneously kills charged class, preserves source residue, and
adds no compensating law data.

## Theorem 3: minimal fitted compensation is derived-trivial

Assume `q:V->A` in `(6)` is an isomorphism and `(7)` holds. Then compensated extension is chain
isomorphic to direct sum of original complex `C` and contractible two-term complex

\[
 V\xrightarrow{\;q\;}A.
 \tag{12}
\]

Under this isomorphism extended residue is `R` on `C` and zero on contractible summand.

### Proof

Define degree-`n` change of coordinates

\[
 \Phi_n(c,a)=\bigl(c-Zq^{-1}a,a\bigr),
 \tag{13}
\]

and let `Phi` be identity in all other degrees. Because `dZ=0`, this commutes with outgoing
differential from degree `n`. On a new degree-`n+1` cell,

\[
 \Phi_nd'(0,v)
 =\Phi_n(Zv,qv)
 =(0,qv).
 \tag{14}
\]

Old chains are unchanged, so `Phi` is chain isomorphism to stated direct sum.

From `(7)` and invertibility of `q`,

\[
 S=-RZq^{-1}.
\]

Writing original coordinate as \(c=\widetilde c+Zq^{-1}a\) gives

\[
 R(c)+S(a)
 =R(\widetilde c)+RZq^{-1}a-RZq^{-1}a
 =R(\widetilde c).
 \tag{15}
\]

Thus contractible summand carries no invariant residue after splitting. QED.

For one nonzero scalar defect, every rank-minimal fitted compensator has
`dim V=dim A=1` and nonzero `q`, hence is invertible. It is therefore only a contractible
re-presentation under chain/derived equivalence, not genuine law birth. A stronger Morita claim
would require specifying full algebraic theory and is not asserted.

## Theorem 4: presentation invariance

Let `F:C->C_tilde` be chain isomorphism or chain equivalence inducing isomorphism on relevant
homology. Suppose residues agree on homology and defect classes correspond:

\[
 \widetilde R\,F_*=R,
 \qquad
 F_*[Z(v)]=[\widetilde Z(v)].
 \tag{16}
\]

Then

\[
 \operatorname{rank}(RZ)
 =\operatorname{rank}(\widetilde R\widetilde Z).
 \tag{17}
\]

### Proof

Both composites are same linear map `V->W` after identifications in `(16)`. Rank is invariant
under isomorphism. QED.

Thus promotion anomaly rank is not artifact of chosen resolution or coordinates.

## Theorem 5: finite/infinite compensator dichotomy for actual Xi source

Assume compensator realization contains actual completed theta source `XiC` and is stable under
spectral-coordinate multiplication:

\[
 \Xi_C\in\mathcal S,
 \qquad
 f\in\mathcal S\Longrightarrow(z\mapsto zf(z))\in\mathcal S.
 \tag{18}
\]

Then `mathcal S` is infinite-dimensional. Consequently, at an off-line divisor fibre there is no
finite-dimensional promotion that is simultaneously:

1. source-residue preserving;
2. noncontractible under derived equivalence;
3. faithful to actual `XiC` source; and
4. stable under descended spectral-coordinate generator.

### Proof

Parent theorem `hedenmalm-finite-source-port-obstruction` proves `(18)` forces linear
independence of

\[
 \Xi_C,z\Xi_C,z^2\Xi_C,\ldots,
\]

because `XiC` is nonzero on neighbourhood of spectral centre. Hence `mathcal S` is
infinite-dimensional. Off line, Theorem 2 requires nonzero compensator. Rank-minimal
finite compensator is derived-trivial by Theorem 3; any other finite `XiC`-faithful,
coordinate-stable compensator contradicts parent theorem. QED.

This is first strict size prediction of Nomotopy: any genuine off-line residue-conserving law
extension compatible with actual Hedenmalm source must have infinite law tangent, despite
promotion anomaly itself having rank one.

## Theorem 6: holomorphic compensator no-go before divisor specialization

Let `U` be connected open subset of `C`, let `n>1`, and let `c:U->C` be holomorphic and not
identically zero. Define real-analytic defect charge

\[
 a_n(s)=\bigl(n^{s+\bar s-1}-1\bigr)c(s).
 \tag{19}
\]

There is no holomorphic or meromorphic function `h` on `U` satisfying

\[
 h(s)=-a_n(s)
 \tag{20}
\]

on any nonempty open subset where `c` is nonzero.

### Proof

On complement of discrete zero set of `c`, Wirtinger derivative is

\[
 \partial_{\bar s}a_n(s)
 =(\log n)n^{s+\bar s-1}c(s)\ne0.
 \tag{21}
\]

Holomorphic function has zero `bar-partial`; meromorphic function is holomorphic away from its
discrete poles. Therefore neither can equal `-a_n` on open set where `c` is nonzero. QED.

For fixed pre-divisor Xi grade `k`, filtered landing coefficient `c_k(s)` is holomorphic. Thus no
purely holomorphic Hedenmalm/Xi module, even infinite-dimensional and coordinate-stable, can carry
the required opposite residue grade-wise. Any source-generated compensator must be genuinely
mixed in `s` and `bar s` (or singular enough to leave ordinary meromorphic category), and must
retain dagger/reflection before scalarization.

## Literal Riemann-source application

In publication-ready arithmetic source, for ordinary-prime trace-one cycle `x_p`, physical
cyclic-to-paracyclic defect satisfies

\[
 R(D_{n,\rho}x_p)
 =(\delta_n(\rho)-1)c_\rho,
 \qquad
 \delta_n(\rho)=e^{(2\Re\rho-1)\log n},
 \qquad c_\rho\ne0.
 \tag{22}
\]

Take `V=k`, `Z(1)=D_{n,rho}x_p`, and `W=k`. Then

\[
 \boxed{
 \operatorname{anomrank}_R(Z_\rho)
 =
 \begin{cases}
 0,&\Re\rho=\tfrac12,\\
 1,&\Re\rho\ne\tfrac12.
 \end{cases}}
 \tag{23}
\]

### Proof

For positive integer `n>=2`, `delta_n(rho)=1` exactly when `Re rho=1/2`. Equation `(22)` and
\(c_\rho\ne0\) show `RZ` is zero on line and nonzero off line. A linear map `k->k` has rank zero or
one accordingly. Apply `(9)`. QED.

## New leverage on live obstruction

The remaining source-null-homology problem is no longer an unrestricted search for “new
geometry.” Any proposed Nomotopic law promotion is classified:

1. **No-surplus, residue-preserving promotion:** possible exactly when physical source residue is
   zero; on all Xi fibres this is RH-bearing.
2. **Off-line promotion:** must create at least one new degree-`n` compensator with residue
   `-(delta_n(rho)-1)c_rho`.
3. **Minimal fitted compensation:** splits as contractible pair and has zero genuine
   law-promotion content.
4. **Regular-observer limitation:** regular orientation readers can measure only compensator's
   scalar charge and cannot distinguish a source-generated noncontractible sector from fitted
   contractible copy. Decisive construction must therefore occur in singular relative/pre-scalar
   source before regular scalarization.
5. **Actual-Xi size law:** if compensator retains completed theta source and spectral-coordinate
   generator, every genuine candidate is infinite-dimensional.
6. **Pre-divisor type law:** no holomorphic/meromorphic Xi module can carry opposite charge;
   candidate must be mixed `s,bar s`, dagger-dependent, or singular beyond meromorphic category.

This is unconditional route leverage: it rules out free cell attachment, rank-minimal fitted
compensation, Koszul--Tate repair, exact completion, and abstract “obstruction becomes law” as
solutions unless they exhibit a source-generated, noncontractible opposite-residue sector. It
also gives a concrete corpus search target:

> Find a source-generated noncontractible singular class with exactly opposite residue, or prove
> none exists. If it retains actual Xi source action, search must be infinite-dimensional and
> genuinely mixed rather than holomorphic.

If none exists in literal arithmetic source, `(15)` forces every divisor fibre to be anomaly rank
zero. That last nonexistence theorem is not proved here.

## Relation to unique Stokes port

For one physical defect, anomaly rank is at most one. Independently, Stokes Cartan form has at
most one negative/null port and regular source-orientation quotient has rank one. The rank
agreement is exact but does not identify spaces. A future mixed theorem must construct a
source-natural isomorphism between compensator image `im(RZ)` and Stokes central port; dimension
counting alone is insufficient.

## Hostile audit

1. The theorem does not prove RH; `(15)` is an exact dichotomy.
2. Compensator can always be adjoined abstractly, so no-surplus must be source theorem, not axiom
   chosen to force answer.
3. Adding a rank-one spectator with fitted opposite residue fails autogenic criterion.
4. Same result is standard chain-level obstruction theory; novelty lives only in invariant's
   arithmetic application and ensuing route elimination.
5. A singular compensator may exist outside regular observer category; orientation completeness
   does not exclude it.

## Lean-return note

No Lean work is authorized. If later requested, formalize generic attachment criterion, minimal
rank theorem, and arithmetic specialization in separate files. Existing residue formula can be
imported from `MobiusThetaSourceDaggerMinimalBoundaryLaw`.

## Log

- 2026-08-08 — proved during first Nomotopy attack on physical source-null-homology obstruction.
