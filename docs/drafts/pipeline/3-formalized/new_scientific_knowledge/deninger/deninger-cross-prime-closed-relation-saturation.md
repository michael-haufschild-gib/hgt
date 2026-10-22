# Calderón--Witt dense-core closed-relation saturation

- **ID:** `deninger-cross-prime-closed-relation-saturation`
- **Stage:** 3-formalized
- **Type:** ROUTE-L NO-GO / POSITIVE CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [GENERAL TOPOLOGICAL LINEAR ALGEBRA PARENT] [ROUTE APPLICATION NEW] [NOT RH]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittCrossPrimeClosedRelationNoGo.lean`
- **Parents:**
  - `deninger-cross-prime-arithmetic-source-completion.md`;
  - `deninger-all-cross-prime-incidence-koszul-exactness.md`;
  - `DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion.lean`.

## Statement

Let

\[
  E=\ell^2(I),\qquad
  I=\{(p,q):p,q\text{ ordinary primes},\ p\ne q\},
\]

and let

\[
  \iota:S_{\mathrm{arith}}\longrightarrow E
\]

be the coefficient realization of the actual ordered Calderón--Witt witness
span.  The corpus proves that `range(iota)` is dense in `E` and that the old
all-prime oriented boundary vanishes on all of `S_arith`.

Let `W` be any complex topological vector space and let

\[
  R\subset E\times W
\]

be a closed complex-linear relation satisfying

\[
  (\iota s,0)\in R\qquad(s\in S_{\mathrm{arith}}).
\tag{1}
\]

Write

\[
  V_R=\{w\in W:(0,w)\in R\}
\]

for its vertical fibre.  Then

\[
  \boxed{R=E\times V_R.}
\tag{2}
\]

Consequently:

1. if `R` is single-valued over zero, then `V_R=0` and `R=E×{0}`;
2. if `R` contains any nonzero output, that output is already vertical over
   zero and occurs over every source input;
3. every closable partial linear operator agreeing with the old oriented
   boundary on the arithmetic core has zero closure;
4. neither an unbounded graph norm nor passage from operators to closed
   linear relations can turn the old boundary into a selective Route-L
   annihilator.

## Proof

Define the zero-output source subspace

\[
  Z_R=\{x\in E:(x,0)\in R\}.
\]

It is closed because it is the inverse image of the closed set `R` under
the continuous linear map `x -> (x,0)`.  By `(1)`, `Z_R` contains the dense
subspace `range(iota)`.  Hence `Z_R=E`, so

\[
  (x,0)\in R\qquad(x\in E).
\tag{3}
\]

If `(x,w) in R`, subtracting `(x,0)` from `(3)` gives `(0,w) in R`; hence
`w in V_R`.  Conversely, if `w in V_R`, adding `(x,0)` to `(0,w)` gives
`(x,w) in R` for every `x`.  This proves `(2)`.

If `R` is the closed graph of a partial operator, graph single-valuedness
forces `V_R=0`, hence its graph is the full zero graph.  For a closable
operator this applies to the closure of its graph.  The remaining claims
follow.

## Strict gain over existing completion no-go

The previous theorem excluded only **continuous operators** on `ell2(I)`
which extend the old oriented boundary.  Formula `(2)` excludes the larger
class of:

- closed unbounded operators;
- closures of closable partial operators;
- arbitrary closed linear relations.

The last class matters because a singular cofinal source construction can
be multivalued after Hilbert completion.  The theorem classifies that escape:
if it still agrees with the zero old boundary on the dense arithmetic core,
its closed relation is a product `E x V_R`, so every nonzero output is pure
vertical ambiguity and contains no source-selecting information.

## Frontier consequence

The updated Hellinger--Hodge--Green descent manuscript asks that the usable
Calderón--Witt comparison retain the boundary primitive, extend the
algebraic direct sum by a locally finite strict grade, and remain
packet-valued.  This theorem adds a necessary condition:

> strict completion alone is insufficient.  The new horizontal arithmetic
> differential must be nonzero already on the finite actual witness core,
> or it must be constructed before the `ell2` topology in a source topology
> whose closed relation is changed by an additional arithmetic identity.

In particular, a boundary-at-infinity obtained merely by closing the old
zero boundary is impossible.  The surviving Route-L object is a genuinely
new horizontal transgression, not another domain for the vertical Koszul or
orientation differential.

This does not prove the required annihilation identity.  It prevents a
large class of false constructions from being presented as that identity.

## Novelty boundary

The abstract fact that a closed linear relation containing a dense zero
graph equals the full source times its vertical fibre is elementary
topological linear algebra.  No novelty is claimed for it in isolation.
New project knowledge is the exact application to the source-faithful
Calderón--Witt completion: the previous continuous-extension wall persists
for every closed/closable singular Hilbert realization, and its only
relation-valued escape is maximally nonselective vertical ambiguity.

## Lean statements

| Card item | Lean declaration |
|---|---|
| dense core `range(iota)` | `deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange` |
| old boundary vanishes on `S_arith` | `deningerCalderonWittGlobalOrientedBoundary_crossPrimeSourceSpan` |
| `(2)`, generic | `closedLinearRelation_eq_top_prod_vertical_of_dense_zeroCore` |
| `(2)`, Calderón--Witt | `deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical` |
| consequence 1 | `deningerCalderonWittCrossPrimeClosedRelation_eq_zeroGraph_of_singleValued` |
| consequence 2, generic | `closedLinearRelation_mem_vertical_of_dense_zeroCore` |
| consequence 2, Calderón--Witt | `deningerCalderonWittCrossPrimeClosedRelation_output_is_vertical` |
| consequence 3 | `deningerCalderonWittCrossPrimeClosableExtension_closure_eq_zero` |
| consequence 4, generic | `closedLinearRelation_outputFiber_const_of_dense_zeroCore` |
| consequence 4, Calderón--Witt | `deningerCalderonWittCrossPrimeClosedRelation_outputFiber_const` |

Consequence 4 is formalized as exact nonselectivity: the output fibre
`{w : (x,w) ∈ R}` is the same set for every source point `x`, so no closed
relation extending the old boundary can distinguish two packets.

## Gates

- [x] exact source completion and dense arithmetic core
- [x] dependency-closed paper proof
- [x] distinguish operators, closable partial operators, and closed relations
- [x] classify the multivalued survivor exactly
- [x] formalize the generic relation theorem and Calderón--Witt specialization
- [x] unconditional Lean certificate for `(2)` and all four consequences
- [x] targeted axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] module wired into `RHTower.lean`
- [ ] construct a horizontal differential nonzero on finite actual witnesses
- [ ] prove source-derived annihilation of actual completed Green provenance
- [ ] RH

The three unchecked gates are downstream Route-L research targets, not
statements of this card.

## Log

- 2026-08-10 — Formalized consequences 2 and 4 (generic and Calderón--Witt
  forms); audited every other numbered item against the existing module.
  Card promoted to `3-formalized`.
