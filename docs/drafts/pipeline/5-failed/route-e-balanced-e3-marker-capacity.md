# Route E balanced-\(E_3\) marker capacity

- **ID:** `ROUTE-E-BALANCED-E3-MARKER-CAPACITY-001`
- **Stage:** 5-failed
- **Type:** SOURCE-MECHANISM NO-GO / PHYSICAL-DENSITY SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** physical Hall-capacity inequality already formalized as
  `sum_conductance_le_neighborUnionCapacity` and
  `replacementNeighborCutDeficiency_le_unusedConductance` in
  `MobiusBoundaryOppositeSignTransport.lean`

## Proposed mechanism

For every source block \(u\asymp U\), use the balanced all-interval \(E_3\) theorem at \(u/\ell\)
and adjoin a fresh marker prime \(\ell\).  Distinct marker families were intended to:

1. tag replacement coordinates so a product corner can be decoded;
2. make target families disjoint;
3. provide enough labels to overcome incoming-corner co-degree.

The displacement remains critical:

\[
\left|\ell m-u\right|
\ll \sqrt{u\ell}(\log u)^{1.55}
=U^{1/2+o(1)}
\]

for subpower \(\ell\).

## Exact killing count

Use the published balanced factor ranges

\[
P=(\log U)^{1.1},\qquad
R\asymp\sqrt{\frac{U}{\ell P}},
\]

and tokens

\[
q=\ell p_1p_2p_3,\qquad
p_1\asymp P,\quad p_2,p_3\asymp R,\quad q\asymp U.
\tag{1}
\]

For fixed \(\ell\), elementary prime upper bounds give

\[
\#\{q\text{ of form }(1)\}
\ll
\frac{P}{\log P}
\left(\frac{R}{\log R}\right)^2
\ll
\frac{U}
{\ell\,(\log\log U)(\log U)^2}.
\tag{2}
\]

Take any family \({\cal L}\) of distinct prime markers with \(\ell\le U^C\).  Even if the target
families are made disjoint, Mertens' prime-reciprocal bound and `(2)` give

\[
\#\bigcup_{\ell\in{\cal L}}T_\ell(U)
\le\sum_{\ell\in{\cal L}}\#T_\ell(U)
\ll_C
\frac{U}{(\log\log U)(\log U)^2}
\sum_{\ell\le U^C\atop \ell\ {\rm prime}}\frac1\ell
\ll_C\frac{U}{(\log U)^2}.
\tag{3}
\]

There are \(\asymp U/\log U\) prime-coordinate sources in the same scale.  Thus the physical
target/source ratio is \(O(1/\log U)\).  For arbitrary integer blocks the deficit is
\(O(1/\log^2 U)\).

No fractional weighting repairs `(3)`.  If \(c(s,t)\ge0\) is supported on the source--target
incidence and every target has load at most one, then

\[
\sum_s\sum_t c(s,t)\le \#\bigcup_sN(s).
\tag{4}
\]

This is the unweighted specialization of the already-Lean-proved theorem
`sum_conductance_le_neighborUnionCapacity`.  Replacing markers by incidence labels changes
representation multiplicity but not the right side of `(4)`.

The obstruction persists across scales.  Balanced targets have dyadic density
\(O(1/\log^2 U)\), so their reciprocal mass is summable:

\[
\sum_{\substack{q\ {\rm balanced\ target}}}\frac1q
\ll\sum_{j\ge1}\frac1{j^2}<\infty.
\tag{5}
\]

By contrast the source-prime reciprocal mass diverges.  Thinning source primes to match `(3)`
therefore leaves a positive-density set of ordinary integers with no usable coordinate; it
cannot produce strict-half uncovered capacity.

## Strongest positive survivor

Pointwise square-root admission is insufficient by exactly one physical logarithm even for
prime-coordinate sources.  Any viable token source must do at least one of the following:

1. prove a square-root-window opposite-parity target family with
   \(\gg U/\log U\) distinct physical targets at prime-coordinate scale;
2. recover the missing logarithm through unbalanced factor ranges, not repeated labels of the
   balanced Type-II slice;
3. prove a genuinely higher-order physical-corner theorem whose image is not confined to
   multiples of a reciprocal-summable token family.

This is a sharper gate than pointwise \(E_3/E_4\) existence.  The required lower bound must be a
local Hall expansion theorem for physical integers, not a row-degree theorem and not a count of
factorization labels.

## Hostile audit

- `(2)` is an upper bound, so overcounting repeated products only strengthens the no-go.
- Allowing every prime marker up to \(U^C\) already maximizes the harmonic marker entropy at
  \(O(\log\log U)\); polynomially many labels do not create polynomially many physical vertices.
- Composite pairwise-coprime squarefree markers have no larger harmonic supply than their least
  prime factors.  Non-coprime markers destroy unique decoding and increase physical collisions.
- The exact prime estimates and Mertens bound are classical.  Standalone novelty is not claimed;
  the Route E synthesis newly rules out marker/codebook amplification of the published balanced
  token slice.

## Status

`RETIRED`.  Balanced \(E_3/E_4\) tokens remain valid pointwise replacements but cannot by marker
amplification furnish Route E fractional capacity.  `OPEN-SOURCE-001` now requires the physical
missing-logarithm/local-Hall theorem stated above.
