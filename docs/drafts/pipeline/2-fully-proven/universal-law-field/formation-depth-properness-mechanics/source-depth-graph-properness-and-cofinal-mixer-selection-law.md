# Source-depth graph properness and cofinal mixer selection law

- **ID:** ULF-FDPM-2
- **Stage:** 2 — fully proven on paper
- **Type:** GLOBAL FORMATION / PROPERNESS / SOURCE-MIXING THEOREM
- **Parent field:** Universal Law Field — Formation-Depth Properness Mechanics
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM FIRST] [GLOBAL PROPERNESS]`
  `[FORMATION-GENERATED GRAPH DOMAIN] [ADAPTIVE ESCAPE EXCLUDED]`
  `[COFINAL MIXER ADMITTED] [BRIDGE] [NOT RH]`
- **Formal status:** Lean formalization required before promotion to Stage 3.

## 1. Mathematical delta

Earlier formation laws expel every fixed nonneutral ray but permit an adaptive sequence of changing
directions whose observed work tends to zero. This theorem closes that gap on the actual countable
source mechanism.

The source depth grading generates its own unbounded operator. The graph domain of that operator,
together with the source codiagonal, carries a uniform coercive law. No extra target norm is chosen.
For the literal complete high-exponent source the same operator is admitted and creates a nonzero
cofinal longitudinal mixer.

## 2. Formation graph domain

Let

\[
 \mathcal D_1=\left\{x=(x_j)_{j\ge0}\in\mathbb C^{\mathbb N_0}:
 \sum_{j\ge0}|x_j|<\infty,
 \quad \sum_{j\ge0}j|x_j|<\infty\right\}.
 \tag{FDP.1}
\]

Define

\[
 c(x)=\sum_{j\ge0}x_j,
 \qquad
 (Dx)_j=jx_j,
 \qquad
 M_1(x)=\|Dx\|_1=\sum_{j\ge0}j|x_j|,
 \tag{FDP.2}
\]

and the formation gauge

\[
 \Phi(x)=|c(x)|+2M_1(x).
 \tag{FDP.3}
\]

This is a source-generated graph law: `c` reads the longitudinal source coordinate and `D` is the
infinitesimal depth formation.

## 3. Main theorem

### Theorem 3.1 — global source-depth properness

For every `x in D_1`:

1. **Exact coercive fusion**

   \[
   \boxed{\|x\|_1\le |c(x)|+2\|Dx\|_1=\Phi(x).}
   \tag{FDP.4}
   \]

2. **Joint reconstruction kernel**

   \[
   \boxed{c(x)=0\ \text{and}\ Dx=0\iff x=0.}
   \tag{FDP.5}
   \]

3. **Uniform cofinal tail control.** For every integer `N>=1`,

   \[
   \boxed{
   \sum_{j\ge N}|x_j|
   \le {1\over N}M_1(x).}
   \tag{FDP.6}
   \]

4. **Adaptive-escape exclusion.** No sequence `x_n in D_1` can satisfy simultaneously

   \[
   \|x_n\|_1=1,
   \qquad
   |c(x_n)|+M_1(x_n)\longrightarrow0.
   \tag{FDP.7}
   \]

5. **Bounded-orbit selection.** For `d>1` and `k in N`, scalar formation
   `F_d^k x=d^k x` obeys

   \[
   \Phi(F_d^kx)=d^k\Phi(x),
   \qquad
   \boxed{
   \sup_{k\ge0}\Phi(F_d^kx)<\infty\iff x=0.}
   \tag{FDP.8}
   \]

6. **Closed graph and cofinal properness.** The operator `D:D_1 subset ell^1 -> ell^1` is closed.
   Every `Phi`-bounded family is bounded in `ell^1` and has uniformly vanishing `ell^1` tails by
   `(FDP.6)`. Hence every `Phi`-sublevel is relatively compact in `ell^1`; because `Phi` is lower
   semicontinuous, it is compact. Equivalently, `Phi:D_1->R_{>=0}` is a proper exhaustion when
   `D_1` is viewed inside `ell^1`.

### Proof

Write

\[
 T_0(x)=\sum_{j\ge1}|x_j|.
\]

Absolute convergence gives

\[
 c(x)=x_0+\sum_{j\ge1}x_j.
\]

Therefore

\[
 |x_0|
 \le |c(x)|+\left|\sum_{j\ge1}x_j\right|
 \le |c(x)|+T_0(x).
 \tag{FDP.9}
\]

Since `j>=1` on the tail,

\[
 T_0(x)\le\sum_{j\ge1}j|x_j|=M_1(x).
 \tag{FDP.10}
\]

Adding `T_0(x)` to `(FDP.9)` proves `(FDP.4)`. If `Dx=0`, every coordinate `x_j` with `j>=1`
vanishes; if also `c(x)=0`, then `x_0=0`, proving `(FDP.5)`.

For `j>=N`, `1<=j/N`; multiplying by `|x_j|` and summing proves `(FDP.6)`. Equation `(FDP.4)`
immediately contradicts `(FDP.7)`.

Both terms in `Phi` are absolutely homogeneous, so

\[
 \Phi(d^kx)=d^k\Phi(x).
\]

If `x=0`, the orbit is zero. If `x!=0`, `(FDP.4)` gives `Phi(x)>0`, and `d^k Phi(x)` is unbounded.
This proves `(FDP.8)`.

For graph closedness, suppose `x^(n)->x` and `Dx^(n)->y` in `ell^1`. Coordinate evaluation is
continuous, hence `j x_j^(n)->j x_j` and also `j x_j^(n)->y_j`; thus `y_j=jx_j` for every `j`, so
`x in D_1` and `Dx=y`.

For compactness, `(FDP.4)` gives uniform `ell^1` boundedness and `(FDP.6)` gives uniform tails.
Every finite coordinate head lies in a bounded subset of a finite-dimensional space. A diagonal
subsequence argument plus the uniform-tail estimate produces an `ell^1`-convergent subsequence.
Fatou's lemma for the nonnegative first-moment sums proves lower semicontinuity and closure of each
sublevel.

## 4. Exact abstract selection interface

Let `Y` be a normed space and let `T:D_1->Y` be a linear realization satisfying, for constants
`a,b>0`,

\[
 a\Phi(x)\le\|Tx\|\le b\Phi(x).
 \tag{FDP.11}
\]

If the target formation `U_d` is norm-conservative and

\[
 T(F_dx)=U_d(Tx),
 \tag{FDP.12}
\]

then `x=0`. Indeed, iteration makes `||T(F_d^kx)||=||Tx||`, while `(FDP.11)` and `(FDP.8)` force
every nonzero orbit to escape. Thus a conservative, source-faithful realization can land only on
the neutral formation class.

This is a typed selection theorem. It does not assert that an RH receiver satisfies `(FDP.11)` or
`(FDP.12)`.

## 5. Literal complete-resolution admission

Fix `K in N` and `s in C` with `Re(s)>0`. Put

\[
 h_j=h_{K,s}(j)=\operatorname{completeResolutionMultiplier}(K,j,s).
 \tag{FDP.13}
\]

The existing complete-resolution law gives

\[
 \sum_{j\ge0}|h_j|<\infty,
 \qquad
 \sum_{j\ge0}h_j=1.
 \tag{FDP.14}
\]

### Theorem 5.1 — cofinal depth admission and mixer conservation

The literal vector `h_(K,s)` belongs to `D_1` and

\[
 \boxed{
 \sum_{j\ge0}j h_j
 =\sum_{j\ge0}
 \left(1-\zeta((K+j)s)^{-1}\right).}
 \tag{FDP.15}
\]

Both series converge absolutely.

If `s` is real and

\[
 s>0,
 \qquad Ks>1,
 \tag{FDP.16}
\]

then every term on the right of `(FDP.15)` is positive. Hence

\[
 \boxed{c(Dh_{K,s})>0.}
 \tag{FDP.17}
\]

The source depth generator therefore converts transverse resolution history into a nonzero
longitudinal signal before zero specialization.

### Proof

For `j>=1`, `h_j` is the shell multiplier at depth `K+j-1`. The adjacent-shell ratio tends to
`2^{-s}`, whose norm is below one on `Re(s)>0`. Multiplying by `j` changes the ratio by
`(j+1)/j -> 1`. The ratio test proves

\[
 \sum_j j|h_j|<\infty.
 \tag{FDP.18}
\]

The finite formation-generation conservation law already proved in the corpus is

\[
 \sum_{j=0}^{N}j h_j
 =\sum_{j=0}^{N-1}
 \left(1-\zeta((K+j)s)^{-1}\right)
 +N\left(\zeta((K+N)s)^{-1}-1\right).
 \tag{FDP.19}
\]

The least-atom asymptotic implies

\[
 2^{(K+N)s}\left(\zeta((K+N)s)^{-1}-1\right)\longrightarrow-1.
\]

Exponential decay dominates `N`, so the terminal term in `(FDP.19)` tends to zero. The left side
converges absolutely by `(FDP.18)`. Moreover, the normalized least-atom asymptotic gives

\[
2^{(K+j)\operatorname{Re}s}\left|1-\zeta((K+j)s)^{-1}\right|\longrightarrow 1.
\]

Hence the normalized deficits are eventually bounded, and a constant multiple of the geometric
series `2^{-j Re s}` majorizes their tail. Thus the deficit series converges absolutely, and passage
to the limit proves `(FDP.15)`.

For real `u>1`, the Dirichlet series gives `zeta(u)>1`. Hence
`0<zeta(u)^{-1}<1`. Under `(FDP.16)`, `(K+j)s>1` for every `j`, so every deficit is positive. At
least the `j=0` deficit is nonzero, proving `(FDP.17)`.

## 6. Fusion across structurally different organs

One source operation now has four exact shadows:

| Organ | Source-depth shadow |
|---|---|
| complete arithmetic resolution | `h_(K,s)` and `sum h_j=1` |
| topology/admission | weighted graph domain `D_1` |
| longitudinal/transverse fusion | `c(Dh)` |
| global selection mechanics | proper gauge `Phi` and bounded-orbit exclusion |

Equation `(FDP.15)` is the fusion law: the topological generator current on the left equals the
analytic accumulated reciprocal-zeta deficit on the right. It is not an analogy and is not fitted
from a route endpoint.

## 7. Sharp boundaries

1. **Arbitrary completion fails.** On unweighted `ell^2`, `c` is nonclosable. The graph law selects
   its completion/domain.
2. **Codiagonal alone fails.** `c` has an infinite-dimensional kernel. Properness is joint in
   `(c,D)`.
3. **Depth alone fails at the head.** `D` kills coordinate zero. The normalized codiagonal recovers
   it.
4. **Unweighted `ell^1` is insufficient for the mixer.** It admits `c` but not every depth current;
   the first-moment domain is load-bearing.
5. **Fixed-ray selection is weaker.** Without `(FDP.4)`, adaptive unit escape can survive even when
   every fixed ray has positive response.
6. **No RH conclusion.** A remaining constitutive theorem must identify physical horizontal
   displacement with this pre-zero formation class and prove conservative/source-faithful landing.

## 8. Internal and external collision audit

The abstract ingredients are classical weighted `ell^1` graph norms, compact sequence-space
embeddings, closed diagonal operators, and ratio tests. Hardy--Sobolev/Fourier and weighted sequence
space literature contains broader embedding machinery. The exact source-specific contribution is
the coupling of:

- the literal complete Riemann resolution;
- its source depth generator;
- the normalized codiagonal;
- the cofinal reciprocal-zeta deficit identity;
- the global no-adaptive-escape selector.

This is classified `[BRIDGE]`, not new scientific knowledge.

## 9. RH-facing gate after this theorem

The formation/properness side is now explicit. The remaining selection gate is not another receiver
estimate. It is one pre-zero constitutive comparison:

\[
 \text{physical off-centre displacement}
 \longmapsto
 \text{nonneutral class in }(\mathcal D_1,\Phi),
\]

intertwining physical reflection/evolution with source formation and bounded below in the graph
gauge. Once such a comparison is proved, Theorem 3.1 and Section 4 force the displacement to vanish.
