# Route E opposite-parity Metropolis rejection law

- **ID:** `ROUTE-E-OPPOSITE-PARITY-METROPOLIS-REJECTION-001`
- **Stage:** 2-fully-proven
- **Type:** EXACT REVERSIBILITY REDUCTION / SHARP RATE GATE
- **Parent:** `route-e-entropy-complement-breadth-mixture-load-law.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** paper-only while the Lean corpus is being refactored

## 1. Exact theorem

Let \(\Omega=\Omega_+\sqcup\Omega_-\) be finite, let \(w_x>0\), and put
\[
 W_\pm=\sum_{x\in\Omega_\pm}w_x,
 \qquad W=W_++W_-,
 \qquad J=W_+-W_-.                                    \tag{1}
\]
Let \(P(x,y)\ge0\) be row stochastic and parity reversing:
\[
 \sum_yP(x,y)=1,
 \qquad P(x,y)>0\Longrightarrow x,y\text{ have opposite parity}. \tag{2}
\]
Define directed edge mass, its reversal, and accepted symmetric conductance by
\[
 Q(x,y)=w_xP(x,y),qquad Q^{\rm R}(x,y)=Q(y,x),
 \qquad C(x,y)=\min\{Q(x,y),Q^{\rm R}(x,y)\}.           \tag{3}
\]
Put
\[
 r_x=w_x-\sum_yC(x,y),qquad R=\sum_xr_x.               \tag{4}
\]
Then
\[
 \boxed{
 R={1\over2}\sum_{x,y}|Q(x,y)-Q^{\rm R}(x,y)|,
 \qquad |J|\le R.}                                     \tag{5}
\]

Proof is exact.  Since \(C\le Q\), every \(r_x\ge0\).  Both \(Q\) and \(Q^{\rm R}\) have
total mass \(W\), so
\[
 {1\over2}\sum|Q-Q^{\rm R}|=W-\sum_{x,y}\min(Q,Q^{\rm R})=R. \tag{6}
\]
Symmetry of \(C\) and parity reversal imply accepted mass leaving \(\Omega_+\) equals accepted
mass leaving \(\Omega_-\).  Therefore \(J=R_+-R_-\), where
\(R_\pm=\sum_{x\in\Omega_\pm}r_x\), and `(5)` follows.

This is a source-predeclared opposite-parity matching theorem: no endpoint sign is inspected and
no optimal flow is selected after seeing \(J\).

## 2. Sharp Radon--Nikodym rate

If \(Q\ll Q^{\rm R}\), Pinsker applied to the normalized edge laws gives
\[
 {R\over W}
 \le\sqrt{\frac12D\!\left({Q\over W}\middle\|{Q^{\rm R}\over W}\right)}. \tag{7}
\]
If both edge directions are present and
\[
 \left|\log{Q(x,y)\over Q(y,x)}\right|\le\eta          \tag{8}
\]
on support, then directly from `(5)`
\[
 {R\over W}\le{e^\eta-1\over2}.                       \tag{9}
\]
At physical scale \(X\), Route E requires \(|J|/W\le X^{-1/2+o(1)}\).  Hence a pointwise
detailed-balance route needs
\[
 \eta\le X^{-1/2+o(1)},                                \tag{10}
\]
or an edge-relative entropy of order \(X^{-1+o(1)}\).  Mere \(1+o(1)\), polylogarithmic, or
\(X^{o(1)}\) reversibility is quantitatively insufficient.

For direct physical edges \(|m-n|\le X^{1/2+o(1)}\), the Gibbs factor contributes exactly the
admissible amount
\[
 \left|\log{e^{-m/X}\over e^{-n/X}}\right|
 ={ |m-n|\over X}\le X^{-1/2+o(1)}.                   \tag{11}
\]
Thus all remaining loss is proposal asymmetry.  This separates the already-closed Gibbs geometry
from the arithmetic incidence law.

## 3. Hostile instantiation on current Route E relation

The structured \(E_3\), whole-anchor, and entropy-complement constructions are oriented by
one-sided intervals: generated terminal exceeds its anchor.  For their present proposal kernels,
\(P(n,v)>0\) generally has \(P(v,n)=0\).  Therefore \(Q\) and \(Q^{\rm R}\) are mutually singular
on those edges, and `(5)` gives
\[
 R=W.                                                    \tag{12}
\]
Generic Metropolis symmetrization accepts nothing.  Adding the reverse support abstractly does not
repair the rate: existing reciprocal-allocation theorem controls columns only by
\(\exp(O((\log\log X)^{3/2}))\), while `(10)` requires a relative defect of order
\(X^{-1/2+o(1)}\).

## 4. Conjecture--proof--failure loop

1. **Metropolis automatically closes column load.** Failed: it closes load only on accepted
   mass; rejection is exactly edge-law total variation and already dominates the parity current.
2. **Co-moving Gibbs weights make rejection small.** Failed for current relation: physical
   weights satisfy `(11)`, but reverse proposal support is absent.
3. **Subpower forward/reverse degree comparability suffices.** Failed quantitatively by `(10)`.
4. **A genuinely two-sided arithmetic proposal is a new avenue.** Survives, with exact target:
   prove `(8)` at scale \(X^{-1/2+o(1)}\), or prove edge entropy \(X^{-1+o(1)}\), before using
   `(5)`.

## 5. Frontier consequence

The positive-flow lane now has a sharp alternative to unit Carleson:

`TWO-SIDED-ENTROPY-COMPLEMENT-DETAILED-BALANCE` — construct a source-predeclared, parity-flipping,
two-sided physical proposal on the same unit log shell whose edge Radon--Nikodym defect satisfies
`(10)` outside \(X^{1/2+o(1)}\) Gibbs mass and whose accepted conductance carries the normalized
friable/one-large-prime seam.

This is not weaker arithmetic disguised as Markov-chain language.  Equation `(5)` proves the
required rate and also proves why forward-only or merely subpower-balanced proposals cannot close
Route E.

