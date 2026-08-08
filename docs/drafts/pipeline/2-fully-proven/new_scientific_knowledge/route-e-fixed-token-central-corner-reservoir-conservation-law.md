# Route E fixed-token central-corner reservoir conservation law

- **ID:** `ROUTE-E-FIXED-TOKEN-RESERVOIR-CONSERVATION-001`
- **Stage:** 2-fully-proven
- **Type:** `[THEOREM (paper)]` / `[SHARP ARCHITECTURE LAW]` / `[POSITIVE NO-GO SURVIVOR]`
- **Parent:** `route-e-grade-recurrent-sparse-reservoir-cube-admission.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** intentionally not started during corpus refactor

## 1. Result

Consider a multiplicative cube whose source coordinates have Wold breadths

\[
 k_i=\omega(U_i),\qquad 1\le i\le d,
\]

and whose replacement in coordinate \(i\) is a product of a reservoir of breadth \(b_i\)
and one fixed-breadth \(E_r\) token.  Put

\[
 \delta_i=b_i+r-k_i,
 \qquad K=\sum_i k_i,
 \qquad B=\sum_i b_i.                                  \tag{1}
\]

Thus \(\delta_i\) is exact Wold-grade change in coordinate \(i\).  Let

\[
 E=\max_{S\subseteq[d]}
       \left|\sum_{i\in S}\delta_i\right|              \tag{2}
\]

be largest grade excursion among all cube corners.  Then

\[
 \boxed{|B-(K-rd)|\le E.}                               \tag{3}
\]

More precisely, if

\[
 P=\sum_{\delta_i>0}\delta_i,
 \qquad N=\sum_{\delta_i<0}(-\delta_i),                 \tag{4}
\]

then

\[
 E=\max(P,N),\qquad
 \sum_i|\delta_i|=P+N\le2E,                            \tag{5}
\]

and

\[
 B=K-rd+P-N.                                            \tag{6}
\]

Consequently, for fixed \(r\), any breadth-full family with

\[
 K=(1-o(1))L,qquad d=o(L),\qquad E=o(L)                \tag{7}
\]

must satisfy

\[
 \boxed{B=(1-o(1))L.}                                  \tag{8}
\]

In particular, a reservoir-free fixed-\(E_r\) cube on such anchors must either have
\(d=\Omega(L)\) or an \(\Omega(L)\) corner-grade excursion.  Combining `(8)` with the proved
harmonic terminal-capacity law shows that any fixed prime pool supporting the construction must
have reciprocal mass of order \(L\).  The critical harmonic reservoir in current Route E relation
is therefore forced by simultaneous full-breadth participation, sublinear arity, and centrality
of every cube corner.

## 2. Exact algebraic proof

Replacement breadth in coordinate \(i\) is \(b_i+r\), so `(1)` is an identity, not an estimate.
Summing it gives

\[
 \sum_i\delta_i=B+rd-K,
\]

or equivalently `(6)`.

For a subset \(S\), corner grade relative to source is \(\sum_{i\in S}\delta_i\).  Taking
\(S_+=\{i:\delta_i>0\}\) gives excursion \(P\); taking
\(S_-=\{i:\delta_i<0\}\) gives excursion \(-N\).  Every other subset sum lies in
\([-N,P]\).  Therefore

\[
 E=\max(P,N).
\]

It follows that \(P+N\le2E\), and

\[
 |B-(K-rd)|=|P-N|\le\max(P,N)=E,
\]

which proves `(3)`--`(6)`.  Under `(7)`, both \(rd\) and \(E\) are \(o(L)\), so `(3)` gives
`(8)`.

No distribution theorem, Möbius estimate, or asymptotic independence is used.

## 3. Parity makes the alternative rigid

Assume all source and replacement factors are squarefree and mutually coprime in usual cube
sense.  Then coordinate \(i\) reverses Möbius sign exactly when

\[
 (-1)^{b_i+r}=-(-1)^{k_i},

\]

equivalently

\[
 \delta_i\equiv1\pmod2.                                \tag{9}
\]

Hence every parity-reversing coordinate has \(|\delta_i|\ge1\).  Equation `(5)` then gives

\[
 d\le\sum_i|\delta_i|\le2E.                            \tag{10}
\]

This is a second exact obstruction: if every corner remains in an \(o(L)\) Wold window, then
parity-reversing cube arity is automatically \(o(L)\).  A proposal cannot hide \(\Theta(L)\)
fixed-token coordinates inside a central cube by arranging only its full-terminal drift to be
small.  Arbitrary subsets select all positive or all negative shifts and expose total variation
`(5)`.

## 4. Reservoir-free fixed-token dichotomy

Set \(B=0\).  Equation `(3)` yields

\[
 K\le rd+E.                                             \tag{11}
\]

Thus a reservoir-free construction using one fixed \(E_r\) token per coordinate has exact
dichotomy

\[
 \boxed{K\le rd+E.}                                    \tag{12}
\]

If \(K\asymp L\) and \(E=o(L)\), then \(d\ge(1-o(1))K/r=\Omega(L)\).  But parity reversal
and `(10)` give \(d\le2E=o(L)\), a contradiction.  Therefore no reservoir-free fixed-token cube
can simultaneously satisfy

1. active source breadth \(K\asymp L\);
2. opposite parity in every coordinate; and
3. \(o(L)\) grade excursion at every corner.

This kills the tempting construction which partitions almost all source primes into even groups
and replaces every group by one \(E_3\) token.  Its full terminal can be tuned to drift by only
\(+1\) or \(+3\), but its arity is \(\asymp L/3\).  The corner selecting all \(+1\) groups, or
all negative groups, has fixed-fraction Wold drift.  Small full-terminal drift does not imply
centrality of complete cube.

## 5. Harmonic-pool consequence

Suppose all reservoir primes come from fixed pool \({\cal P}_X\), and every terminal contains
the \(B\) distinct inserted reservoir primes.  The proved physical divisor-incidence theorem gives

\[
 \#\{v\in[cX,CX]:\omega_{{\cal P}_X}(v)\ge B\}
 \le CX\left(\frac{eS({\cal P}_X)}B\right)^B,
 \qquad
 S({\cal P}_X)=\sum_{p\in{\cal P}_X}\frac1p.            \tag{13}
\]

If `(7)` holds, `(8)` gives \(B=(1-o(1))L\).  Therefore

\[
 S({\cal P}_X)=o(L)                                    \tag{14}
\]

forces terminal universe to be

\[
 X\exp(-\Omega(L\log(L/S({\cal P}_X))))=o(X),          \tag{15}
\]

far too small for unit physical load on central-density anchors.  In particular, moving all
reservoir primes to a fixed polylogarithmic or other harmonically sparse low band cannot repair
fine collisions.  Large raw pool cardinality is irrelevant; reciprocal mass is forced.

The present annular pool has

\[
 S({\cal P}_X)=L-2\log L-\sqrt L+O(1),                 \tag{16}
\]

so it lies at the correct structural scale.  This does not prove its sufficiency.

## 6. Conjecture--proof--failure loops

### Loop A: eliminate reservoirs by using one \(E_3\) per small source group

`[CONJECTURE]` Partition almost all source prime mass into groups of size two and four.  Replacing
a pair by \(E_3\) changes grade by \(+1\); replacing a quadruple changes it by \(-1\).  Choose an
odd number of groups with full-terminal drift \(+1\) or \(+3\).

`[PARTIAL PROOF]` Such a source-defined partition exists, all source mass can participate, every
coordinate reverses parity, sparse-forbidden \(E_3\) theorem applies, and mixed Gibbs cost remains
\(X^{-1/2+o(1)}\).

`[FAILED]` Arity is \(\Theta(L)\).  Equation `(10)` forces an \(\Omega(L)\) corner excursion.
The relation therefore reloads fixed off-normal Wold sectors and does not replace current central
cube.

### Loop B: move current reservoir to a low separated prime band

`[CONJECTURE]` A low band makes every reservoir product much smaller and removes inverse-interval
collision loss.

`[FAILED]` Equations `(8)` and `(13)` show that breadth-full central corners still force
\(B\asymp L\), while low band has \(S({\cal P}_X)=o(L)\).  Its physical terminal universe is too
small before any collision estimate is attempted.

### Loop C: small full-terminal drift controls all corners

`[CONJECTURE]` Alternating fixed-token grade changes and forcing
\(|\sum_i\delta_i|=O(1)\) keeps cube central.

`[FALSIFIED]` Full-terminal drift is \(P-N\); largest corner excursion is \(\max(P,N)\).  Equal
large positive and negative totals can cancel at full terminal while separate subset corners see
each total without cancellation.

## 7. Revised scientific boundary

This theorem does not prove unit Carleson or RH.  It removes three false escapes from current
frontier:

- reservoir-free fixed-\(E_r\) full-breadth cubes;
- harmonically sparse low reservoir pools; and
- full-terminal-only Wold balancing.

Any genuine successor must keep critical harmonic reservoir, replace fixed-token architecture by
a denser variable-breadth source, or abandon complete-cube support through a new signed design
whose off-normal corner mass is quantitatively negligible.  Merely shrinking reservoir primes or
balancing endpoint grade is theatre after `(3)`.

## 8. Scientific and formal status

`[PAPER-PROVED] [NOVELTY UNVERIFIED]`.  Equations `(3)`--`(12)` are exact finite identities.  The
harmonic consequence uses already-proved physical divisor-incidence bound from parent Route E
card.  No external literature search was performed under current instruction.  No Lean was
written or built while corpus refactor is active.
