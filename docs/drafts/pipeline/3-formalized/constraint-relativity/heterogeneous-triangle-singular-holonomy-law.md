# Heterogeneous triangle identity and singular-holonomy law

- **ID:** `heterogeneous-triangle-singular-holonomy-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRAINT RELATIVITY
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED IN LEAN] [NOT RH]`
- **Novelty status:** telescoping and norm estimates are elementary. Candidate new content is their
  use as the mandatory local law of a heterogeneous relation atlas; no external priority claim.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

Arithmetic, spectral, and geometric realizations live in different spaces. Saying “their
commutator is nonzero” is usually ill-typed. This card gives the minimal typed cycle law and proves
the exact uncertainty statement behind a recurring corpus fact:

> if every edge becomes exact but a nonzero cycle defect survives, some comparison must become
> singular or the three edge realizations do not belong to one common triangle.

The theorem is independent of zeta functions, divisors, `Ext`, positivity, and Hilbert adjoints.

## 2. A typed realization triangle

Let `E_0,E_1,E_2` be normed vector spaces. Let

\[
 T_{01}:E_0\to E_1,
 \qquad T_{12}:E_1\to E_2,
 \qquad T_{20}:E_2\to E_0
 \tag{2.1}
\]

be bounded linear maps, and choose declared realizations

\[
 x_0\in E_0,\qquad x_1\in E_1,\qquad x_2\in E_2.
 \tag{2.2}
\]

Define oriented edge defects

\[
 \begin{aligned}
 e_{01}&=T_{01}x_0-x_1,\\
 e_{12}&=T_{12}x_1-x_2,\\
 e_{20}&=T_{20}x_2-x_0,
 \end{aligned}
 \tag{2.3}
\]

and based cyclic defect

\[
 \Omega_0=T_{20}T_{12}T_{01}x_0-x_0.
 \tag{2.4}
\]

## 3. Exact triangle law

### Theorem 3.1 — transported-edge decomposition

One has the exact identity

\[
 \boxed{
 \Omega_0
 =T_{20}T_{12}e_{01}+T_{20}e_{12}+e_{20}.}
 \tag{3.1}
\]

Consequently,

\[
 \|\Omega_0\|
 \le
 \|T_{20}T_{12}\|\,\|e_{01}\|
 +\|T_{20}\|\,\|e_{12}\|
 +\|e_{20}\|.
 \tag{3.2}
\]

### Proof

Substitute `(2.3)` successively:

\[
 \begin{aligned}
 T_{20}T_{12}T_{01}x_0-x_0
 &=T_{20}T_{12}(x_1+e_{01})-x_0\\
 &=T_{20}(x_2+e_{12})+T_{20}T_{12}e_{01}-x_0\\
 &=e_{20}+T_{20}e_{12}+T_{20}T_{12}e_{01}.
 \end{aligned}
\]

This proves `(3.1)`. Triangle inequality and operator-norm bounds give `(3.2)`. QED.

### Corollary 3.2 — exact-edge flatness

If all three edge defects vanish, then `Omega_0=0`. Thus nonzero cyclic defect cannot coexist with
one selected triple of exactly compatible edge realizations.

This corollary distinguishes two phenomena often conflated:

1. **transport curvature:** compatible triples exist but errors are amplified around the cycle;
2. **selection horn:** every required pair exists, but no one triple realizes all edges.

Theorem 3.1 addresses the first. A missing common triple is a separate higher gluing obstruction.

## 4. Cofinal singular-holonomy theorem

For each `n`, let `(E_i,T_{ij}^{(n)},x_i^{(n)})` be a triangle as above. Put

\[
 \varepsilon_n=max\{
 \|e_{01}^{(n)}\|,\|e_{12}^{(n)}\|,\|e_{20}^{(n)}\|
 \}
 \tag{4.1}
\]

and

\[
 M_n=max\{1,\|T_{20}^{(n)}\|,
              \|T_{20}^{(n)}T_{12}^{(n)}\|\}.
 \tag{4.2}
\]

### Theorem 4.1 — singular amplification is necessary

For every `n`,

\[
 \|\Omega_0^{(n)}\|\le3M_n\varepsilon_n.
 \tag{4.3}
\]

Hence:

1. if `epsilon_n -> 0` and `sup_n M_n<infinity`, then `Omega_0^(n)->0`;
2. if `epsilon_n->0` and

   \[
   \liminf_{n\to\infty}\|\Omega_0^{(n)}\|\ge\kappa>0,
   \tag{4.4}
   \]

   then along every sufficiently large `n`,

   \[
   M_n\ge {\kappa\over6\varepsilon_n},
   \tag{4.5}
   \]

   after replacing `kappa` by any smaller positive lower bound if necessary. In particular,
   transport norms diverge at least reciprocally to edge accuracy.

### Proof

Each coefficient in `(3.2)` is at most `M_n`, while each edge defect is at most `epsilon_n`, so
`(4.3)` follows. Item 1 is immediate. Under `(4.4)`, eventually
`||Omega_0^(n)||>=kappa/2`; combining with `(4.3)` gives `(4.5)`. QED.

### Corollary 4.2 — no bounded precision miracle

Suppose finite-resource arithmetic, spectral, and geometric comparisons become arbitrarily exact.
If their selected cyclic defect stays nonzero, it cannot be explained by three uniformly regular
comparison maps. At least one of the following occurs:

1. an operator norm or inverse-domain cost diverges;
2. convergence is not uniform/equicontinuous on the relevant source orbit;
3. a range is nonclosed or the limiting map is relation-valued;
4. the three pairwise realizations cannot be selected simultaneously, so there is a horn rather
   than a triangle.

Only items 1--2 follow numerically from Theorem 4.1. Items 3--4 are distinct ways the hypotheses of
one normed selected triangle can fail; they are listed to prevent a false conclusion that every
singularity is norm blow-up.

## 5. Equicontinuous completion law

The norm theorem has a locally convex form.

### Theorem 5.1 — equicontinuous edge exactness kills holonomy

Let `E_0,E_1,E_2` be Hausdorff locally convex spaces. For each `n`, let the maps in `(2.1)` be
continuous linear. Assume the two families

\[
 \{T_{20}^{(n)}:E_2\to E_0\}_n,
 \qquad
 \{T_{20}^{(n)}T_{12}^{(n)}:E_1\to E_0\}_n
 \tag{5.1}
\]

are equicontinuous. If all three edge defects converge to zero in their respective spaces, then
`Omega_0^(n)->0` in `E_0`.

### Proof

Identity `(3.1)` remains algebraically valid. Equicontinuity sends every null sequence to a null
sequence uniformly in the family: given a zero-neighborhood `U` in `E_0`, choose
zero-neighborhoods `V_1,V_2` whose images under all maps in `(5.1)` lie in a chosen third of `U`.
Eventually `e_01^(n) in V_1`, `e_12^(n) in V_2`, and `e_20^(n)` lies in the remaining third.
Then `(3.1)` lies in `U`. QED.

### Corollary 5.2 — barrelled source diagnostic

When `E_1,E_2` are barrelled and `E_0` is a suitable locally convex target, pointwise boundedness
of the families `(5.1)` implies equicontinuity by Banach--Steinhaus. In that setting, a persistent
cyclic defect forces failure of pointwise boundedness or of a common completed source.

This corollary uses the standard uniform boundedness principle; it adds no new theorem about
barrelled spaces.

## 6. Sharpness and countermodels

### Countermodel 6.1 — arbitrarily accurate edges with fixed holonomy

For each `n`, let the underlying real vector space of every `E_i^{(n)}` be `R`. Give
`E_1^{(n)}` the norm `|z|/n` and give `E_0^{(n)},E_2^{(n)}` the usual norm. Put

\[
 x_0=1,
 \qquad x_1=-1,
 \qquad x_2=1,
 \tag{6.1}
\]

and define

\[
 T_{01}=0,
 \qquad T_{12}(z)=-z,
 \qquad T_{20}(z)=z.
 \tag{6.2}
\]

Then

\[
 e_{01}=1,
 \qquad e_{12}=0,
 \qquad e_{20}=0,
 \qquad \Omega_0=-1.
 \tag{6.3}
\]

Measured in the declared norms,

\[
 \|e_{01}\|_{E_1^{(n)}}={1\over n},
 \qquad
 \|T_{20}T_{12}\|=n,
 \qquad
 \|\Omega_0\|=1.
 \tag{6.4}
\]

Indeed `T_12 e_01=-1`, so `(3.1)` gives `Omega_0=-1`. Thus reciprocal amplification in
Theorem 4.1 is sharp up to the universal constant.

## 7. Scope and hostile significance audit

### What is proved

1. exact typed decomposition of cyclic defect into transported edge defects;
2. quantitative lower bound on singular amplification needed for persistent holonomy;
3. equicontinuity theorem for cofinal completion;
4. separation of transport singularity from a missing common selection triangle.

### What is not proved

1. no source relation is created;
2. no RH zero is placed on the critical line;
3. no black-hole geometry is constructed;
4. no nonadditive relation atlas is classified;
5. a horn obstruction requires separate simplicial/descent mathematics;
6. the identity is not externally novel as linear analysis.

### Falsifiers

The theorem is falsified by a correctly typed triangle violating `(3.1)`. The proposed field-level
interpretation is falsified if persistent corpus defects occur with a common selected triangle,
vanishing edge defects, and uniformly equicontinuous transports.

## 8. Future Lean notes — no action

Later formalization would require only normed-space linear maps, a three-term algebraic identity,
and operator-norm estimates. No Lean file was written, edited, or built in this turn.

## Formalized companion

`heterogeneous-triangle-singular-holonomy-law-formalized.md` (same directory).
