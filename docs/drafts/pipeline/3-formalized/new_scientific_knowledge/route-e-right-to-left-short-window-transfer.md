# Route E right-to-left short-window transfer

- **ID:** `ROUTE-E-RIGHT-TO-LEFT-WINDOW-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [EXACT FINITE TRANSFER] [NUMERICAL-DIRECTION REPAIR]`
- **Parent:** `route-e-product-truncated-reservoir-harmonic-mass-law.md`,
  `route-e-entropy-complement-breadth-mixture-load-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteERightToLeftWindowTransfer.lean`

## Exact theorem

Let `h : ℕ → ℕ` be monotone and suppose `2h(y) ≤ y`. Put

\[
  x=y-2h(y).
\]

Then

\[
  (x,x+h(x)]\subset (y-2h(y),y).
\tag{1}
\]

Indeed, monotonicity gives `h(x) ≤ h(y)`, so

\[
  x+h(x)\le y-h(y)<y
\]

unless `h(y)=0`, when the source window is empty. Consequently every predicate count in the
right window transfers unchanged to the left window:

\[
 \#\{m\in(x,x+h(x)]:A(m)\}
 \le
 \#\{m\in(y-2h(y),y):A(m)\}.
\tag{2}
\]

The module also proves the real-scale inclusion used when the token centre is a quotient such as
`n/t`.

## Route E consequence

The published all-right structured-almost-prime input may be applied at the predeclared shifted
centre `y-2h(y)`. Its complete token predicate—breadth, squarefreeness, forbidden-prime exclusion,
and factor ranges—is retained. Thus every admitted upward token family has a downward numerical
family of the same proved cardinality within twice the window radius. Multiplication by a
product-truncated reservoir `t=X^{o(1)}` gives

\[
  |q-n|\le 2t h(n/t)=X^{1/2+o(1)}.
\tag{3}
\]

Möbius grade is unchanged by translating the interval, so the whole-anchor or
entropy-complement breadth rule still makes every edge parity-reversing. Numerical direction and
Wold-grade direction are therefore independent choices.

## What this closes

- Separate left-interval almost-prime theorem is unnecessary.
- One-sided numerical orientation is not intrinsic to the factorization relation.
- Product-truncated and breadth-mixture candidates can be made numerically bidirectional without
  losing token count, parity, freshness, or strict-half displacement exponent.

## What remains open

This theorem supplies rows, not coefficient-one Hall expansion. Mixing upward and downward rows
does not bound physical column load, weighted chi-square, or load-gradient energy. It also does
not formalize the external all-interval almost-prime count itself. Remaining source theorem is
still joint rough-token/source-layer physical balance plus normalized co-moving seam flux.

The parity-coalesced full-terminal cube is a different object: its individual terminal jumps are
explicitly `X^(1-o(1))`; only its full mixed difference has strict-half cost. Equation (3) does
not turn that high-order mixed estimate into an `H`-local edge estimate.

## Verification

Direct foreground check:

```text
lake env lean GaloisForLFunctions/RHTower/RouteERightToLeftWindowTransfer.lean
```

The module is wired into `formal/GaloisForLFunctions/RHTower.lean`. Targeted build and axiom audit
are recorded after final audit.

