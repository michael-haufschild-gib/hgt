# Source-depth/codiagonal global properness conjecture and hostile gate

- **ID:** ULF-FDPM-1
- **Stage:** 1 — in progress / superseded conjecture
- **Type:** UNIVERSAL-LAW-FIELD MECHANISM CONJECTURE / HOSTILE GATE
- **Status:** `[CONJECTURE FROZEN] [FALSE AS STATED] [POSITIVE SURVIVOR EXTRACTED]`
  `[NOT A ROUTE CARD] [NOT RH]`

## 1. Frozen mechanism conjecture

Let one source carry a countable formation-depth grading, let `D` be its depth generator, and let
`c` be its normalized codiagonal. The conjecture was:

> **Formation-depth properness conjecture.** On the canonical completed source, the joint response
> `(c,D)` is globally proper. Consequently no unit source displacement can escape all finite-depth
> formation tests, and bounded full formation orbit selects the neutral displacement.

This asks for a mechanism, not a new carrier: grading generates a derivative, derivative and
codiagonal jointly reconstruct/coerce the source, and source dilation turns coercivity into
selection.

## 2. Hostile verdict: false without a formation-generated topology

The conjecture is false on an arbitrary completion.

On the algebraic finite-support source, put

\[
 c(x)=\sum_{j\ge0}x_j,
 \qquad
 (Dx)_j=jx_j.
\]

In the unweighted Hilbert completion `ell^2`, `c` is nonclosable: the vectors supported on the first
`N` coordinates with all coordinates `1/N` converge to zero in `ell^2` while their codiagonal is
one. Thus `(c,D)` is not even a typed closed observer on that completion. Conversely, on unweighted
`ell^1`, `c` is bounded but `D` is unbounded and not defined on every source.

Therefore source depth does not produce properness until it also produces the admissible graph
domain. Properness is not a property of the algebraic grading alone.

## 3. Strongest positive survivor

Use the weighted first-moment graph domain

\[
 \mathcal D_1
 =\left\{x:\sum_j|x_j|<\infty,
               \ \sum_j j|x_j|<\infty\right\}.
\]

On this domain the exact source inequality is

\[
 \boxed{
 \sum_j|x_j|
 \le \left|\sum_jx_j\right|+2\sum_jj|x_j|.}
\]

It forces the joint response `(c,D)` to be injective and bounded below, eliminates adaptive unit
escape, and makes bounded scalar-formation orbit equivalent to `x=0`. It also gives the uniform
tail law

\[
 \sum_{j\ge N}|x_j|
 \le {1\over N}\sum_jj|x_j|
 \qquad(N\ge1),
\]

which is the cofinal compactness mechanism.

The actual complete high-exponent source belongs to this domain: its adjacent shell ratio tends to
`2^{-s}`, of norm below one on `Re(s)>0`, so multiplication by every fixed polynomial in the depth
preserves summability. Its depth current has an exact cofinal longitudinal landing.

## 4. Representation lesson

Global selection does not come from adding a stronger observer to a fixed completion. The source
operation must generate three things together:

1. grading;
2. graph admission;
3. properness scale.

Changing any one independently reopens escape. The surviving field primitive is therefore a
**formation-generated graph law**, not curvature, a metric chosen afterward, or a route endpoint.

## 5. Disposition

The unrestricted conjecture is retired. The weighted-graph survivor is proved in
`source-depth-graph-properness-and-cofinal-mixer-selection-law.md` and must be formalized before it
counts as closed.

