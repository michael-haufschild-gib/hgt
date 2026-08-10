# Relative-law observer-descent duality

- **ID:** `relative-law-observer-descent-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / FOUNDATIONAL BRIDGE
- **Status:** `[PAPER-PROVED] [CANONICAL RELATIVE-OBSERVER PAIRING] [LITERAL ROUTE-R APPLICATION]`
  `[CLASSICAL HOMOLOGICAL ALGEBRA] [CORPUS INTERFACE NEW] [NOT RH] [LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
- **Statement:** For an exactification `Phi:C->X`, relative mapping-cone laws and observers that
  fail to descend through `H(Phi)` are canonically dual to the same kernel; their evaluation gives
  an exact arithmetic--geometric--spectral pairing in literal Route R.
- **Literal input:** `route-r-raw-resolved-relative-cone-character-law.md`.

## Goal

Replace metaphor “obstruction moves between representations” by a closed theorem. Identify the
precise object simultaneously seen as:

1. source class erased by exactification;
2. relative mapping-cone class;
3. obstruction to descent of an observer;
4. physical value obtained by pairing source law with observer.

## 1. Setup

Let `k` be a field, `C^bullet,X^bullet` cochain complexes of `k`-vector spaces, and

\[
 \Phi:C^\bullet\longrightarrow X^\bullet
 \tag{ROD.1}
\]

a cochain map. Fix degree `n` and a `k`-vector space `V`. Put

\[
 H_C=H^n(C),
 \qquad H_X=H^n(X),
 \qquad f=H^n(\Phi):H_C\to H_X.
 \tag{ROD.2}
\]

Precomposition gives

\[
 f^*:\operatorname{Hom}_k(H_X,V)\longrightarrow
       \operatorname{Hom}_k(H_C,V).
 \tag{ROD.3}
\]

Define observer-descent quotient

\[
 \mathcal O_f(V)=\operatorname{coker}(f^*).
 \tag{ROD.4}
\]

An element is an observer on source cohomology, modulo observers that factor through resolved
cohomology.

Use cone convention

\[
 \operatorname{Cone}(\Phi)^j=X^j\oplus C^{j+1},
 \qquad
 d(x,c)=(d_Xx-\Phi c,-d_Cc).
 \tag{ROD.5}
\]

## 2. Observer-descent exact sequence

There is a natural exact sequence

\[
 0\longrightarrow\operatorname{Hom}_k(\operatorname{coker}f,V)
 \longrightarrow\operatorname{Hom}_k(H_X,V)
 \xrightarrow{f^*}\operatorname{Hom}_k(H_C,V)
 \xrightarrow{\mathrm{res}}\operatorname{Hom}_k(\ker f,V)
 \longrightarrow0,
 \tag{ROD.6}
\]

where `res(chi)=chi|_(ker f)`. Consequently restriction induces canonical isomorphism

\[
 \boxed{
 \mathcal O_f(V)\cong\operatorname{Hom}_k(\ker f,V).}
 \tag{ROD.7}
\]

### Proof

A map `H_X->V` lies in kernel of `f^*` exactly when it vanishes on `im f`, hence exactly when it
factors uniquely through `coker f`. Every element of `im f^*` vanishes on `ker f`.

Conversely, if `chi:H_C->V` vanishes on `ker f`, it factors through
`H_C/ker f`, canonically identified with `im f`. Since vector subspace `im f subset H_X` admits a
linear complement, the resulting map `im f->V` extends to `H_X->V`; hence `chi` lies in
`im f^*`. Finally, every map `ker f->V` extends to `H_C->V`, again by a vector-space complement.
This proves exactness and `(ROD.7)`. `[PROVED HERE]`

The induced isomorphism `(ROD.7)` is canonical; only proof of surjectivity uses noncanonical
extensions.

## 3. Relative-law exact sequence

Put

\[
 C[1]^j=C^{j+1},
 \qquad d_{C[1]}=-d_C.
 \tag{ROD.8a}
\]

The short exact sequence of complexes

\[
 0\longrightarrow X^\bullet
 \longrightarrow\operatorname{Cone}(\Phi)^\bullet
 \longrightarrow C[1]^\bullet\longrightarrow0
 \tag{ROD.8}
\]

gives exact segment

\[
 H^{n-1}(X)
 \longrightarrow H^{n-1}(\operatorname{Cone}(\Phi))
 \xrightarrow{\pi}H^n(C)
 \xrightarrow{f}H^n(X).
 \tag{ROD.9}
\]

Therefore

\[
 \boxed{
 \mathcal R_f:=
 \frac{H^{n-1}(\operatorname{Cone}(\Phi))}
      {\operatorname{im}H^{n-1}(X)}
 \cong\ker f.}
 \tag{ROD.10}
\]

Here image in denominator means image of first arrow in `(ROD.9)`. `[PROVED HERE]`

Call `R_f` relative-law space: it consists exactly of source cohomology classes made exact by
resolved comparison, represented together with a chosen resolved primitive.

## 4. Canonical relative-observer pairing

Combining `(ROD.7)` and `(ROD.10)` yields

\[
 \boxed{
 \mathcal O_f(V)\cong\operatorname{Hom}_k(\mathcal R_f,V).}
 \tag{ROD.11}
\]

Equivalently there is canonical pairing

\[
 \langle-,-\rangle_{\Phi,V}:
 \mathcal O_f(V)\times\mathcal R_f\longrightarrow V,
 \qquad
 \langle[\chi],[\kappa]\rangle
 =\chi\bigl(\pi[\kappa]\bigr).
 \tag{ROD.12}
\]

It is well-defined because a descending observer vanishes on `ker f`, while a cone class coming
from `H^(n-1)(X)` has zero projection under `pi`. Formula `(ROD.11)` proves:

> **Descent--detection complementarity.** An observer descends through exactification if and only
> if it vanishes on every relative law created by that exactification.

This is an exact factorization theorem, not a numerical Heisenberg inequality. `[PROVED HERE]`

## 5. Literal Route-R arithmetic--geometric--spectral pairing

Take `n=1`, fix actual Xi divisor copy `rho`, set `t=t_rho=2 Re(rho)-1`, and use rational-adelic
source complex `C_p`, resolved Route-R complex `X_t`, and strict comparison `Phi_p`. Retained
arithmetic source class obeys

\[
 [\eta_p]\ne0,
 \qquad H^1(\Phi_p)[\eta_p]=0.
 \tag{ROD.13}
\]

Cone class and its relative-law quotient are

\[
 \kappa^{\mathrm{cone}}_{p,\rho}=[(L_p,\eta_p)]
 \in H^0(\operatorname{Cone}(\Phi_p)).
 \tag{ROD.14a}
\]

\[
 \bar\kappa_{p,\rho}
 =\kappa^{\mathrm{cone}}_{p,\rho}\bmod\operatorname{im}H^0(X_t)
 \in\mathcal R_f,
 \qquad
 \pi(\bar\kappa_{p,\rho})=[\eta_p].
 \tag{ROD.14}
\]

For fixed physical prime-sequence quotient

\[
 V=\mathbb C^{\mathcal P}/\ell^1(\mathcal P),
 \tag{ROD.15}
\]

the forward spectral/physical observer is

\[
 P_{t,\rho}([x])=c_\rho\bar I_p([x])[F_{-t}].
 \tag{ROD.16}
\]

Its observer-descent class pairs with the relative law as

\[
 \boxed{
 \left\langle[P_{t,\rho}],\bar\kappa_{p,\rho}\right\rangle
 =c_\rho[F_{-t}].}
 \tag{ROD.17}
\]

The reflected observer gives

\[
 \boxed{
 \left\langle[P^{\mathrm{ref}}_{t,\rho}],\bar\kappa_{p,\rho}\right\rangle
 =c_\rho[F_t].}
 \tag{ROD.18}

\]

The ingredients now have exact distinct roles:

| face | literal object | universal role |
|---|---|---|
| arithmetic | retained `[eta_p]` | law in `ker H^1(Phi_p)` |
| geometric/topological | `bar kappa_(p,rho)` | relative cone lift modulo resolved classes |
| spectral/Fourier/physical | `[P_(t,rho)]` | non-descending observer covector |
| measured value | `c_rho[F_(-t)]` | canonical relative-observer pairing |

This is one exact object viewed through three mathematical doctrines, not a metaphorical merger.
The corresponding physical reader is an ordinary cochain character on `Cone(Phi_p)` obtained by
projection to shifted source coordinate. No secondary cohomology operation is needed.

## 6. RH leverage and exact boundary

In critical strip, forward pairing `(ROD.17)` is nonzero exactly for `t<=0`, and reflected pairing
`(ROD.18)` is nonzero exactly for `t>=0`. Their simultaneous nonzero value occurs exactly at
`t=0`. Thus RH is equivalent to simultaneous nonvanishing of forward and reflected observer
evaluations on every distinguished retained relative class `bar kappa_(p,rho)` attached to actual
Xi divisor copy.

This theorem does not prove simultaneous nonvanishing. It shows that merely constructing another
carrier, boundary, or chain map, without source law forcing these evaluations nonzero, is
insufficient.

## 7. Conjecture/proof-or-fail ledger

1. **Conjecture:** three Route-R faces lie in one unaugmented resolved absolute cohomology group.
   **Failed:** raw reporter is curved and physical observer cannot descend through resolved
   absolute cohomology; relative cone cohomology does carry it.
2. **Conjecture:** information is destroyed by resolved exactification.
   **Failed:** nonzero relative cone class retains it.
3. **Conjecture:** physical observer requires an undefined secondary operation.
   **Failed positively:** ordinary relative cone character realizes it; its absolute descent
   obstruction and evaluation are canonical `(ROD.7)`--`(ROD.12)`. Only source production of
   simultaneous nonvanishing on distinguished retained classes remains open.
4. **Conjecture:** arithmetic, geometry, and spectral reader require one common carrier.
   **Failed positively:** they occupy kernel, relative lift, and dual observer spaces; canonical
   pairing, not carrier identification, is the merger.

## 8. Hostile falsifiers

1. Over general rings, extensions used in `(ROD.6)` need not exist; theorem is stated over field.
2. For topological vector spaces, continuous complements may fail; no continuous version is
   claimed.
3. If physical observer is not defined on source cohomology or fails to kill boundaries, literal
   application fails. Here Stokes theorem supplies both facts.
4. Pairing alone cannot force simultaneous nonvanishing on distinguished classes. Inserting it as
   axiom would be RH-equivalent circularity.
5. Do not identify `R_f` with all of `H^(n-1)(Cone)`; quotient by image from `H^(n-1)(X)` is
   essential.

## 9. Novelty boundary

Exact Hom sequence, mapping-cone long exact sequence, and evaluation duality are classical linear
homological algebra. Candidate new-to-corpus content is their literal coupling to the retained
rational-adelic Stokes class, resolved Xi primitive, and fixed trace-ideal observer, yielding the
exact three-face dictionary `(ROD.13)`--`(ROD.18)`. No external priority claim is made.

## Lean-return note

Formalized; see `relative-law-observer-descent-duality-formalized.md`.  The named target
`(ROD.6)`--`(ROD.12)` is complete, and the literal Route-R instantiation `(ROD.13)`--`(ROD.18)` is
complete as well: the source complex, the retained class, the resolved complex and its comparison,
the physical quotient `V = C^P/l^1(P)` and the Euler profile are all constructed, so every
displayed value is a theorem with no premises beyond `c_rho != 0`.  The §6 consequence is
formalized both abstractly and at the divisor parameter `t_rho = 2 Re rho - 1`, where simultaneous
nonvanishing is exactly `Re rho = 1/2`; which `rho` satisfy it is not addressed.

## Gates

- [x] 0 → 1: exact kernel/observer question isolated
- [x] 1 → 2: dependency-closed proof over vector spaces
- [x] literal arithmetic--geometric--spectral instantiation
- [x] circularity boundary stated
- [x] independent hostile audit
- [ ] continuous/filtered version
- [ ] source-derived simultaneous nonvanishing on distinguished retained classes
- [x] Lean formalization
- [ ] RH

## Log

- 2026-08-08 — exact observer-descent sequence and relative-law pairing proved; literal Route-R
  Cartier class identified as pairing of arithmetic kernel law, geometric cone lift, and spectral
  observer covector.
