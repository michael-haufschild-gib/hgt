# Pro-Kummer holonomy capacity, reconstruction, and linear-threshold selection law

- **ID:** ULF-DFPM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GLOBAL PROPERNESS / INTEGER-CHARGE SELECTION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [SHARP THRESHOLD] [RECURRENT OBSERVER + OPEN LIFT] [JOINT RECONSTRUCTION] [RH-EQUIVALENT SPECIALIZATION] [SOURCE CAPACITY GENESIS OPEN] [FULLY LEAN-FORMALIZED]

## 1. Root-holonomy tower

For (q\in\mathbb Z) and integer (n\ge2), define

\[
 h_n(q)=\exp(2\pi iq/n)\in S^1.
 \tag{PKH.1}
\]

This is the depth-(n) Kummer holonomy of a meromorphic divisor of order (q).  It is also the
endpoint of the discrete history

\[
 k\longmapsto h_n(q)^k.
 \tag{PKH.2}
\]

The observed history is periodic, while the marked logarithmic lift

\[
 k\longmapsto 2\pi qk/n\in\mathbb R
 \tag{PKH.3}
\]

is unbounded when (q\ne0).

## 2. Reconstruction

### Theorem 2.1 -- complete root-holonomy tomography

For every finite nonempty set (F\subset\mathbb N_{\ge2}), the packet

\[
 (h_n(q))_{n\in F}
\]

determines (q) modulo

\[
 L_F=\operatorname{lcm}(F).
 \tag{PKH.4}
\]

The full tower ((h_n(q))_{n\ge2}) determines (q\) exactly.

#### Proof

For one depth,

\[
 h_n(q)=h_n(q')
 \Longleftrightarrow n\mid(q-q').
\]

Equality for all (n\in F) is therefore equivalent to divisibility by their least common
multiple.  If the full towers agree and (d=q-q'\ne0), choose (n>|d|); then (n\nmid d), a
contradiction. ∎

### Corollary 2.2 -- finite recurrence with open recovered history

The observer orbit (PKH.2) has exact period (n/\gcd(n,q)), while the marked lift (PKH.3) advances
linearly.  Closing every finite observer therefore does not close the source history.  The full
family of finite closures reconstructs the integer lift by Theorem 2.1.

## 3. Sharp weighted action

Let (w_n\ge0) and define the extended action

\[
 \mathcal A_w(q)
 =\sum_{n\ge2}w_n|1-h_n(q)|^2\in[0,+\infty].
 \tag{PKH.5}
\]

### Theorem 3.1 -- exact capacity criterion

For every fixed nonzero (q\in\mathbb Z), and every (n\ge2|q|),

\[
 \boxed{
 16\frac{q^2}{n^2}
 \le |1-h_n(q)|^2
 \le4\pi^2\frac{q^2}{n^2}.}
 \tag{PKH.6}
\]

Consequently,

\[
 \boxed{
 q\ne0
 \Longrightarrow
 \left(
 \mathcal A_w(q)<\infty
 \Longleftrightarrow
 \sum_{n\ge2}\frac{w_n}{n^2}<\infty
 \right).}
 \tag{PKH.7}
\]

Also (\mathcal A_w(0)=0) for every weight sequence.

#### Proof

The elementary identity

\[
 |1-e^{ix}|^2=4\sin^2(x/2)
\]

with (x=2\pi q/n) gives

\[
 |1-h_n(q)|^2=4\sin^2(\pi q/n).
\]

For (n\ge2|q|), (0\le|\pi q/n|\le\pi/2).  On this interval,

\[
 \frac{2y}{\pi}\le\sin y\le y.
\]

Substitution yields (PKH.6).  Multiplication by (w_n\ge0) and comparison of tails proves
(PKH.7); finitely many initial terms do not affect convergence.  The zero-charge statement is
immediate. ∎

### Corollary 3.2 -- polynomial threshold

For (w_n=n^a), (a\in\mathbb R),

\[
 \boxed{
 q\ne0\Longrightarrow
 \mathcal A_a(q)
 \begin{cases}
 <\infty,&a<1,\\
 =+\infty,&a\ge1.
 \end{cases}}
 \tag{PKH.8}
\]

Thus linear depth capacity (w_n=n) is the first polynomial scale that selects trivial charge by
finite action.

## 4. Global properness

Assume

\[
 \sum_{n\ge2}\frac{w_n}{n^2}=+\infty.
 \tag{PKH.9}
\]

### Theorem 4.1 -- bounded-action selection

\[
 \boxed{
 \mathcal A_w(q)<\infty
 \Longleftrightarrow q=0.}
 \tag{PKH.10}
\]

Every finite-action sublevel in the discrete charge space (\mathbb Z) is the compact singleton
(\{0\}).  More generally, any family of integer charges with uniformly bounded truncated actions

\[
 \sup_N\sum_{2\le n\le N}w_n|1-h_n(q)|^2<\infty
\]

contains only (q=0).

#### Proof

The forward implication is Theorem 3.1 under (PKH.9); the reverse is
\(\mathcal A_w(0)=0\).  The truncated sums increase to the full extended action, so a uniform bound
would make the limit finite. ∎

This is a global formation/properness theorem.  Its load-bearing datum is capacity growth across the
entire root tower, not one finite root observer.

## 5. Coordinate-free contour form

Let (R\) be nonzero meromorphic on a domain and let

\[
 \omega=-d\log R.
\]

For a closed contour (\Gamma) avoiding the divisor, put

\[
 q_\Gamma=\frac1{2\pi i}\int_\Gamma\omega\in\mathbb Z,
 \tag{PKH.11}
\]

and

\[
 h_n(\Gamma)
 =\exp\left(\frac1n\int_\Gamma\omega\right)
 =e^{2\pi iq_\Gamma/n}.
 \tag{PKH.12}
\]

### Corollary 5.1 -- contour-charge selection

Under (PKH.9), finite pro-Kummer action for (\Gamma) is equivalent to

\[
 \int_\Gamma\omega=0.
\]

If this holds for every sufficiently small contour, the divisor of (R) is zero.

#### Proof

Apply Theorem 4.1 to the integer (PKH.11).  Small contours isolate individual divisor points, so
zero charge on all of them is equivalent to zero local order everywhere. ∎

## 6. Euler-shell RH specialization

For the renormalized formation transfer (R_{m,r}) of ULF-DFPM-1, every strict-right zeta zero
(\rho) of multiplicity (q\) has local work charge (q).  Therefore the following are equivalent:

1. RH;
2. every local pro-Kummer action with linear weights (w_n=n) is finite;
3. every such local action is zero;
4. the uniform bounded-truncated-action law holds at every point of (\Re s>1/2).

#### Proof

ULF-DFPM-1 identifies local charges with strict-right zero multiplicities.  Theorem 4.1 selects
charge zero.  Absence of strict-right zeros is equivalent to RH by functional-equation reflection.
∎

This is an unconditional equivalence, not an RH proof.  The missing theorem is a pre-target source
construction of the weights and a uniform finite-action bound.

## 7. Four-shadow fusion

One integer charge now has four exact shadows:

| organ | shadow |
|---|---|
| divisor theory | local order (q) |
| root descent | depth-(n) Kummer character (e^{2\pi iq/n}) |
| recurrence/history | finite cyclic observer with open logarithmic lift |
| global properness | weighted chordal action and sharp linear threshold |

The divisor is jointly reconstructed by all root observers, and the conservation identity is

\[
 h_n(q+q')=h_n(q)h_n(q').
 \tag{PKH.13}
\]

The fourth-organ prediction not used in reconstruction is the sharp capacity wall (PKH.8).

## 8. Hostile boundaries

1. **Unweighted all-depth action selects.** False: (\sum n^{-2}<\infty).
2. **One finite depth selects.** False: it sees only (q\bmod n).
3. **Finite observer recurrence closes history.** False by (PKH.3).
4. **Root-stack existence selects.** False: it supplies the characters but not finite global action.
5. **Any growing capacity selects.** False: (w_n=n^a) with (0<a<1) still gives finite action.
6. **Linear capacity is source-derived here.** False.  The theorem classifies the required growth;
   the literal source assignment remains open.
7. **Functional equation supplies the action bound.** False.  Reflection preserves charge
   multiplicity and the common-recovery lift is information-neutral.

## 9. Parent mathematics and status

Roots of unity, Kummer monodromy, (p)-series comparison, and winding reconstruction are classical.
The result is a Frankenstein fusion by design: divisor order, finite recurrence, open history,
capacity, and properness become one exact law.  Infinite-root-stack theory supplies a natural
carrier for the finite holonomies but not the source capacity or bounded-action theorem.

## 10. Lean formalization boundary

Every theorem of this card is Lean-certified, unconditionally and without added hypotheses.

| Module | Content |
|---|---|
| `HTGeometry.ProKummerHolonomyCapacity` | §1–§5: the holonomy tower, reconstruction, exact recurrence with open lift, the sharp chord bounds, the capacity threshold, the polynomial threshold, and the contour form |
| `RHTower.ProKummerLinearThresholdSelection` | §6: linear capacity and the Euler-shell equivalence with RH |

Extended actions are formalized as `Summable` statements on nonnegative terms, which is equivalent
to finiteness of the `ℝ≥0∞`-valued sum and keeps the comparison arguments in `ℝ`.  The exact
period of the finite observer is `addOrderOf` in `ZMod n`, so the minimality asserted by
"exact period" is part of the statement rather than an informal remark.

Axiom audit over the 25 public declarations: only `propext`, `Classical.choice`, `Quot.sound`; no
`sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.  Both leaves are wired into their area umbrellas
and into `UniversalLawField.lean`.

The pre-target source construction of the weights, and a uniform finite-action bound for the
literal source, are not claimed.

