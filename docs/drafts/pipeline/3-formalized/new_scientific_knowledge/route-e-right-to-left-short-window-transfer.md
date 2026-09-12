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

## Stronger sign-exclusive one-radius transfer

Suppose the token predicate `A` excludes the source `y`, as an opposite-Möbius-grade predicate
does. Applying the same right-window supply at

\[
  x=y-h(y)
\]

places its complete filtered token set in the strict left window `(y-h(y),y)`. No token count is
lost, and the numerical displacement falls from `2h(y)` to `h(y)`. After multiplication by a
reservoir `t`, the corresponding bound is

\[
  |q-n|\le t h(n/t).
\tag{4}
\]

The numerical edges which fail the ordinary reverse-window test lie in an initial strip of width

\[
  \Delta_y=h(y)-h(y-h(y)).
\tag{5}
\]

Consequently their number is at most `Δ_y`. For the real radius `h(y)=c\sqrt y`, `c\ge0` and
`c^2\le y`, Lean proves

\[
  c\sqrt y-c\sqrt{y-c\sqrt y}\le c^2.
\tag{6}
\]

For `c=(\log X)^{1.55}`, the numerical nonreverse boundary is therefore at most
`(\log X)^{3.1}=X^{o(1)}`.

More precisely, if the original shifted right window contains at least `D` predicate tokens, the
subfamily which also passes the reverse-window test has cardinality at least

\[
  D-\Delta_y.
\tag{7}
\]

This is the exact finite interface from a one-sided token lower bound to a numerically pair-stable
token lower bound.

This is a numerical statement only. A source-dependent factorization certificate must separately
be proved stable under endpoint reversal. Equations (4)--(7) do not provide that factorization
pair-stability.

## Why the two-radius shift is not a transpose device

The original count-preserving shift based at `y-2h(y)` remains useful for unconditional downward
row supply. But at most one token in its shifted window can satisfy the numerical reverse-window
test, and any such token equals the single boundary point `y-h(y)`. Hence the two-radius theorem
cannot by itself build a bulk approximate transpose.

## What this closes

- Separate left-interval almost-prime theorem is unnecessary.
- One-sided numerical orientation is not intrinsic to the factorization relation.
- Product-truncated and breadth-mixture candidates can be made numerically bidirectional without
  losing token count, parity, freshness, or strict-half displacement exponent.
- Under source exclusion, the shift costs one radius; its purely numerical failure of reverse
  overlap is confined to the radius-oscillation boundary (5).

## What remains open

This theorem supplies rows, not coefficient-one Hall expansion. Mixing upward and downward rows
does not bound physical column load, weighted chi-square, or load-gradient energy. It also does
not formalize the external all-interval almost-prime count itself. Remaining source theorem is
still joint rough-token/source-layer physical balance plus normalized co-moving seam flux.

The whole-anchor certificate has an additional structural obstruction: if a forward reservoir
`t` is inserted into `q=t*m`, then that same nontrivial `t` cannot be fresh at reverse source `q`,
because `gcd(t,t*m)=1` iff `t=1`. Surviving mechanisms must decode a different reverse reservoir,
use a genuinely symmetric toggle certificate, symmetrize support and control reciprocal degree,
or estimate aggregate mismatch divergence without entrywise reversal.

The parity-coalesced full-terminal cube is a different object: its individual terminal jumps are
explicitly `X^(1-o(1))`; only its full mixed difference has strict-half cost. Equation (3) does
not turn that high-order mixed estimate into an `H`-local edge estimate.

## Verification

Direct foreground check:

```text
lake env lean GaloisForLFunctions/RHTower/RouteERightToLeftWindowTransfer.lean
```

Targeted module build passed:

```text
lake build GaloisForLFunctions.RHTower.RouteERightToLeftWindowTransfer
```

The module is wired into `formal/GaloisForLFunctions/RHTower.lean`. `#print axioms` on every public
theorem reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
