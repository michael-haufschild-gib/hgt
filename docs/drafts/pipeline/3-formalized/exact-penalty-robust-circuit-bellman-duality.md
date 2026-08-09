# Exact-penalty robust circuit Bellman duality

- **ID:** `exact-penalty-robust-circuit-bellman-duality`
- **Stage:** 3-formalized
- **Formalized companion:** `./exact-penalty-robust-circuit-bellman-duality-formalized.md`
- **Lean:** Theorems A–C formalized in `HTGeometry/ExactPenaltyCircuitBellman.lean`
- **Type:** theorem / exact control duality / frontier correction
- **Parent:** `./static-orbit-net-no-go-and-circuit-bellman-law.md`
- **Status:** `[PAPER-PROVED] [BRIDGE] [FRONTIER CORRECTION] [LEAN-PROVED]`
- **Date:** 2026-08-09

## Public sentence

Robust circuit complexity is exactly the largest solution of a one-gate Bellman inequality below
one metric obstacle.  Such a calibration always exists and becomes exact at a finite penalty, so
its existence is not evidence for complexity growth; the scientific content must be an
independent formula whose growth can be proved from the static Hamiltonian.

## Setup

Let `(X,d)` be a metric space, let `G` be a nonempty compact inverse-closed family of isometries of
`X` whose evaluation action is continuous, and fix a reference point `chi`.  Finite gate
alphabets are the discrete special case; the compact family of all one- and two-body gates on
prescribed supports is also included.  A word `w=(g_1,...,g_l)` has length `|w|=l` and acts by

\[
 W_w=g_l\cdots g_1 .                                             \tag{1}
\]

Write

\[
 Z_s=\{W_w\chi:|w|\le s\},\qquad
 d_s(x)=\min_{z\in Z_s}d(x,z),                                  \tag{2}
\]

and, for `epsilon>=0`,

\[
 C_\epsilon(x)=\min\{s\in\mathbb N:d_s(x)\le\epsilon\},        \tag{3}
\]

with value `infinity` if the set is empty.  Compactness of `G` makes every `Z_s` compact, so the
minimum in `(2)` exists.

For `lambda>=0`, define the exact-penalty value

\[
 V_{\lambda,\epsilon}(x)
 =\min_w\left\{|w|+\lambda
       \bigl(d(x,W_w\chi)-\epsilon\bigr)_+\right\}.             \tag{4}
\]

The minimum exists: the empty word gives a finite upper bound and every word with length above
that bound is irrelevant; for each remaining length, compactness of the finite Cartesian power of
`G` gives a minimizing word.

## Theorem A -- exact robust Bellman equation

For every `lambda,epsilon>=0`, the value `(4)` is `lambda`-Lipschitz and obeys

\[
 \boxed{
 V_{\lambda,\epsilon}(x)=
 \min\left\{
   \lambda(d(x,\chi)-\epsilon)_+,\ 
   1+\min_{g\in G}V_{\lambda,\epsilon}(g^{-1}x)
 \right\}.}                                                     \tag{5}
\]

Moreover

\[
 0\le V_{\lambda,\epsilon}(x)\le C_\epsilon(x),                \tag{6}
\]

whenever the right side is finite, and inverse closure gives

\[
 \boxed{
 |V_{\lambda,\epsilon}(gx)-V_{\lambda,\epsilon}(x)|\le1
 \qquad(g\in G).}                                               \tag{7}
\]

### Proof

Every function

\[
 x\longmapsto |w|+\lambda(d(x,W_w\chi)-\epsilon)_+
\]

is `lambda`-Lipschitz.  The pointwise infimum of an equi-Lipschitz family is
`lambda`-Lipschitz, proving the first claim.  Split the words in `(4)` into the empty word and
nonempty words.  Every nonempty word has a unique last gate `g`; isometry gives

\[
 d(x,gW_w\chi)=d(g^{-1}x,W_w\chi),                              \tag{8}
\]

and its length is `1+|w|`.  Taking the two minima proves `(5)`.

If `c=C_epsilon(x)<infinity`, a word of length `c` lies within `epsilon` of `x`; its penalty in
`(4)` vanishes, proving `(6)`.  Prepending `g` to every competitor for `x` gives
`V(gx)<=1+V(x)`.  Apply the same statement to `g^{-1}` and `gx` to obtain the reverse inequality
and hence `(7)`.

## Theorem B -- maximal-subsolution duality

Let `A_(lambda,epsilon)` be the class of all functions `phi:X->R` satisfying

\[
 \begin{aligned}
 \phi(x)&\le\lambda(d(x,\chi)-\epsilon)_+,\\
 \phi(x)&\le1+\phi(g^{-1}x)\qquad(g\in G).                     \tag{9}
 \end{aligned}
\]

Then

\[
 \boxed{
 V_{\lambda,\epsilon}(x)
 =\sup_{\phi\in A_{\lambda,\epsilon}}\phi(x).}                \tag{10}
\]

The same supremum is obtained after restricting to `lambda`-Lipschitz subsolutions.

### Proof

Iterate the second inequality in `(9)` along a word `w` and then use the first inequality at
`W_w^{-1}x`.  Isometry gives

\[
 \phi(x)\le |w|+
 \lambda(d(x,W_w\chi)-\epsilon)_+.                             \tag{11}
\]

Taking the minimum over `w` proves `phi(x)<=V_(lambda,epsilon)(x)`.  Theorem A shows that `V`
itself satisfies `(9)` and is `lambda`-Lipschitz, so equality holds in both versions of the
supremum.

## Theorem C -- finite exact-penalty recovery of approximate complexity

Assume `c=C_epsilon(x)<infinity`.  If `c=0`, then
`V_(lambda,epsilon)(x)=0` for every `lambda`.  If `c>0`, put

\[
 \lambda_*(x,\epsilon)
 =\max_{0\le s<c}
   {c-s\over d_s(x)-\epsilon}.                                  \tag{12}
\]

Every denominator in `(12)` is strictly positive.  For every
`lambda>=lambda_*`,

\[
 \boxed{
 V_{\lambda,\epsilon}(x)=C_\epsilon(x).}                        \tag{13}
\]

Consequently

\[
 \boxed{
 C_\epsilon(x)
 =\sup_{\lambda\ge0}\ \sup_{\phi\in A_{\lambda,\epsilon}}
       \phi(x),}                                                \tag{14}
\]

and the outer supremum is attained at a finite penalty whenever the complexity is finite.

### Proof

For `s<c`, definition of `c` gives `d_s(x)>epsilon`, so `(12)` is finite.  Consider any word of
length `s<c`.  Since its endpoint belongs to `Z_s`,

\[
 s+\lambda(d(x,W_w\chi)-\epsilon)_+
 \ge s+\lambda(d_s(x)-\epsilon)\ge c.                           \tag{15}
\]

Every word of length at least `c` has cost at least `c`.  A length-`c` word within `epsilon` has
cost exactly `c`.  Thus the minimum `(4)` equals `c`, proving `(13)`.  Equation `(14)` follows
from Theorem B.

## Corollary -- the calibration-existence route is circular

For any fixed target endpoint, robust Bellman calibrations with the desired value exist if and
only if the corresponding approximate circuit lower bound is true.  The canonical calibration is
`V_(lambda,epsilon)`, and its exact penalty threshold `(12)` is itself defined by all lower circuit
layers.  Therefore the instruction

> construct some metric-robust function changing by at most one per local gate

does not reduce the Brown--Susskind problem unless the proposed function has an independently
controlled formula that does not evaluate `Z_s`, `d_s`, or `C_epsilon`.

This corrects the final paragraph of the parent card.  Its one-sided calibration theorem is valid,
but existence of a calibration was not a new mathematical source.  The load-bearing task is now to
construct an **external subsolution**: a member of `(9)` defined from ordinary static-local
Hamiltonian structure whose value on `exp(-itH)chi` has a quenched Brown-rate lower bound.

## Conjecturing and falsification ledger

### C0 -- any robust Bellman calibration moves the frontier

`[FALSIFIED AS A RESEARCH REDUCTION]`.  Theorems B--C construct one exactly from the unknown
complexity and recover complexity at a finite penalty.  Bare existence is equivalent to the
desired conclusion.

### C1 -- use lifted elapsed action as the calibration

`[FALSIFIED]`.  Lifted action is a history variable, not a function on the recurrent endpoint.
The corpus's restricted-history completion theorem proves that no continuous endpoint observable
on the compact recurrent torus recovers its unbounded lift.

### C2 -- use a fixed local observable, energy, entanglement, or magic

`[FALSIFIED AT BROWN SCALE]`.  These standard endpoint monotones have at most polynomial or linear
range on `n` qubits, whereas the state-complexity target is `Theta(2^n/log n)`.

### C3 -- external Bellman subsolution from computational reuse

`[CONJECTURE] [OPEN CORE]`.  A viable subsolution must charge repeated noncommuting reuse of the
same local degrees of freedom.  Fresh-block simulation lower bounds, local observable growth,
unstructured orbit geometry, and the canonical value function do not provide it.

## External boundary added on 2026-08-09

Zlokapa, Allen and Harrow, *Optimal Lower Bounds for Hamiltonian Simulation*, arXiv:2607.19852,
prove asymptotically optimal gate lower bounds.  Their static bounded-degree local gadget supplies
the unit-time base case.  Linear dependence on late time is obtained by acting on fresh disjoint
blocks in successive time intervals; equivalently, the static reduction enlarges system size
proportionally to time.  It therefore does not give repeated-reuse growth for one fixed-size,
time-independent local Hamiltonian.  This is a direct primary-source boundary, not a criticism of
their theorem.

## Hostile audit

1. Theorems A--C are exact dynamic programming and penalty mathematics, not a Brown growth proof.
2. The duality is a `[BRIDGE]`; shortest-path Bellman equations and exact penalties are classical.
   No standalone novelty is claimed.
3. Equation `(14)` is not an efficient algorithm.  Evaluating its maximal subsolution is exactly as
   hard as evaluating circuit complexity.
4. The result does not supply the external subsolution in C3, a first-hard-time bound, or a
   recurrence scale.
5. No final manuscript may cite this card as evidence that static local complexity grows.

## Exact next move

Replace endpoint-only monotones by a reuse-sensitive object on the autonomous computation
groupoid.  It must descend to an endpoint subsolution of `(9)` after genuine spectral returns are
quotiented, yet it may not be defined using circuit reachability.  Prove a quenched Brown-rate lower
bound for that explicit object on the fixed-shell local ensemble.  Failure to descend means it is
only lifted history; failure of exponential range means it cannot reach the Brown plateau.

## Lean realization after corpus refactor

1. finite word action and reachable sets;
2. exact-penalty value `(4)` and existence of the minimum;
3. Lipschitz and Bellman laws `(5)--(7)`;
4. maximal-subsolution comparison `(9)--(10)`;
5. finite exact-penalty threshold `(12)--(14)`.
