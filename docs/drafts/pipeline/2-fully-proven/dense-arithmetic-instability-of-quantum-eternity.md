# Dense arithmetic instability of quantum eternity

- **ID:** `dense-arithmetic-instability-of-quantum-eternity`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL FINITE QUANTUM RECURRENCE NO-GO / POSITIVE RANK CLASSIFICATION
- **Paper-proof status:** `[DEPENDENCY-CLOSED]`
- **Formal status:** `[OPEN — DO NOT MOVE TO STAGE 3]`
- **Novelty status:** `[EXTERNAL PRIORITY AUDIT INCOMPLETE]`
- **Parent conjecture:** `../1-in-progress/arithmetic-completion-of-quantum-time-conjecture.md`
- **Date:** 2026-07-30

## Public theorem

> **Every finite quantum system lies arbitrarily close to systems with every
> possible dimension of infinite-time recurrence.**

For systems with at least three energy levels:

> **Every quantum Hamiltonian is arbitrarily close both to a system that
> repeats exactly and to one that never repeats exactly. Their dynamics can
> remain uniformly indistinguishable for as long as any finite horizon fixed
> in advance.**

“Never repeats exactly” means no positive exact global projective return.
Approximate quantum recurrence remains.

## Theorem A — every rational temporal rank is dense

For \(n\ge1\), define
\[
  r_{\mathbb Q}(\omega)
  =
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\omega_1,\ldots,\omega_n\},
  \qquad \omega\in\mathbb R^n.
\]
Then for every \(1\le k\le n\), the exact-rank locus
\[
  \mathcal R_{n,k}
  =
  \{\omega:r_{\mathbb Q}(\omega)=k\}
\]
is dense in \(\mathbb R^n\).

More strongly, let \(\mathcal A\) be any finite collection of proper affine
hyperplanes defined over \(\mathbb Q\). Then
\[
  \mathcal R_{n,k}\setminus\bigcup_{A\in\mathcal A}A
\]
is dense. Thus exact rank \(k\) can be realized arbitrarily close to any gap
packet while retaining nonzero and pairwise distinct gaps.

For \(k<n\), \(\mathcal R_{n,k}\) is meagre and Lebesgue-null but dense. The
maximal-rank locus \(\mathcal R_{n,n}\) is dense, residual and
full-Lebesgue-measure, but it has empty interior because
\(\mathcal R_{n,1}\) is dense.

Consequently the function
\[
  r_{\mathbb Q}:\mathbb R^n\longrightarrow\{0,1,\ldots,n\}
\]
is continuous at no point when the codomain is discrete and \(n\ge1\).

## Proof of Theorem A

Fix \(1\le k\le n\). Choose a transcendental
\(\theta\in\mathbb R\) and put
\[
  V_k
  =
  \operatorname{span}_{\mathbb Q}
  \{1,\theta,\ldots,\theta^{k-1}\}.
\]
Transcendence makes the displayed powers linearly independent, so
\(\dim_{\mathbb Q}V_k=k\). Since \(\mathbb Q\subset V_k\) and
\(\mathbb Q\) is dense in \(\mathbb R\), \(V_k\) is dense in
\(\mathbb R\).

We need a full-spanning tuple in every open box
\(I_1\times\cdots\times I_n\). Choose
\(v_1,\ldots,v_k\) inductively. Suppose
\[
  W_{j-1}
  =
  \operatorname{span}_{\mathbb Q}
  \{v_1,\ldots,v_{j-1}\}
\subsetneq V_k.
\]
Choose \(a\in V_k\cap I_j\) and \(b\in V_k\setminus W_{j-1}\).
For a sufficiently small nonzero \(q\in\mathbb Q\),
\[
  v_j=a+qb\in I_j.
\]
If \(a\in W_{j-1}\), then \(v_j\notin W_{j-1}\); if
\(a\notin W_{j-1}\), all but at most one rational \(q\) retain
\(v_j\notin W_{j-1}\). Thus the first \(k\) entries can be chosen as a
\(\mathbb Q\)-basis of \(V_k\). Choose every remaining \(v_i\) in
\(V_k\cap I_i\). The resulting tuple spans exactly \(V_k\) and has rank
\(k\).

To avoid finitely many rational affine hyperplanes, first make the preceding
choice in a smaller open box whose closure lies in the target box. Regard the
tuple as a coefficient matrix over the fixed basis of \(V_k\). One
\(k\times k\) minor is nonzero. Choose a direction
\(d\in V_k^n\) on which none of the finitely many hyperplane normals
vanishes; a finite union of proper subspaces cannot cover a vector space over
the infinite field \(\mathbb Q\). Along \(v+qd\), each affine hyperplane is
hit for at most one \(q\in\mathbb Q\), while the selected spanning minor is a
nonzero polynomial in \(q\) and therefore vanishes for only finitely many
values. A sufficiently small rational \(q\) outside this finite exceptional
set keeps the tuple in the target box, preserves rank \(k\), and avoids every
hyperplane.

If \(k<n\), every rank-\(k\) vector obeys at least one nonzero rational
linear relation. Hence
\[
  \mathcal R_{n,k}
  \subseteq
  \bigcup_{0\ne q\in\mathbb Q^n}
  \{\omega:q\cdot\omega=0\}.
\]
The union is countable; every member is a closed nowhere-dense
Lebesgue-null hyperplane. This proves meagreness and nullity. Its complement
is the maximal-rank locus, proving residuality and full measure. Density of
rank one proves that maximal rank has empty interior.

## Theorem B — every Hamiltonian neighbourhood contains every eternity

Let \(H\) be any Hermitian operator on a complex Hilbert space of finite
dimension \(D\ge2\). For every \(\delta>0\) and every
\[
  1\le k\le D-1
\]
there exists a simple-spectrum Hermitian \(K_k\) such that
\[
  \|H-K_k\|<\delta
\]
and its projective temporal dimension is exactly
\[
  \tau(K_k)
  =
  \dim_{\mathbb Q}
  \operatorname{span}_{\mathbb Q}
  \{\lambda_j(K_k)-\lambda_0(K_k):1\le j<D\}
  =k.
\]

All \(K_k\) may be chosen with the same eigenvectors as \(H\).

## Proof of Theorem B

Use the spectral theorem to write
\[
  H=U\operatorname{diag}
  (\lambda_0,\ldots,\lambda_{D-1})U^*.
\]
Apply Theorem A to the gap packet
\[
  \omega_j=\lambda_j-\lambda_0,\qquad 1\le j<D,
\]
avoiding the rational hyperplanes
\[
  \omega'_j=0,\qquad
  \omega'_i=\omega'_j.
\]
Choose a rank-\(k\) packet \(\omega'\) sufficiently close to \(\omega\)
and define
\[
  K_k
  =
  U\operatorname{diag}
  (\lambda_0,\lambda_0+\omega'_1,\ldots,
  \lambda_0+\omega'_{D-1})U^*.
\]
The avoided hyperplanes give simple spectrum, projective rank is \(k\), and
unitary invariance of operator norm gives
\[
  \|H-K_k\|
  =
  \max_j|\omega_j-\omega'_j|
  <\delta.
\]

## Theorem C — uniform bounded-horizon indistinguishability

For the commuting pair \(H,K_k\) constructed above,
\[
  \boxed{
  \|e^{-itH}-e^{-itK_k}\|
  \le |t|\,\|H-K_k\|
  }
  \tag{1}
\]
for every \(t\in\mathbb R\).

Therefore, for every prescribed horizon \(T>0\) and error
\(\eta>0\), every Hamiltonian \(H\) has, for every
\(1\le k\le D-1\), a rank-\(k\) neighbour \(K_k\) satisfying
\[
  \boxed{
  \sup_{|t|\le T}
  \|e^{-itH}-e^{-itK_k}\|<\eta.
  }
  \tag{2}
\]

For every density matrix \(\rho\) and bounded observable \(O\),
\[
  \left|
  \operatorname{tr}
  \rho\left(
    e^{itH}Oe^{-itH}
    -
    e^{itK_k}Oe^{-itK_k}
  \right)
  \right|
  \le
  2|t|\,\|H-K_k\|\,\|O\|.
  \tag{3}
\]

## Proof of Theorem C

The two operators share eigenvectors. Scalar phase Lipschitz continuity gives
\[
  |e^{-it\lambda_j}-e^{-it\lambda'_j}|
  \le |t|\,|\lambda_j-\lambda'_j|.
\]
Taking the maximum diagonal entry proves `(1)`, and choosing
\(\|H-K_k\|<\eta/T\) proves `(2)`.

For `(3)`, insert and subtract
\(e^{itH}Oe^{-itK_k}\), use the triangle inequality, unitarity, `(1)`,
and
\[
  |\operatorname{tr}(\rho A)|\le\|A\|
\]
for a density matrix.

## Corollary 1 — exact repetition and exact nonrepetition are both dense

A simple finite spectrum has a positive exact global projective return iff
its gap rank is one.

Indeed, if all gaps lie in \(\alpha\mathbb Q\), clearing finitely many
denominators produces \(T>0\) with
\[
  T(\lambda_j-\lambda_0)\in2\pi\mathbb Z
\]
for every \(j\). Conversely, any positive exact projective return places all
gaps in
\[
  (2\pi/T)\mathbb Z,
\]
so their rational rank is at most one.

For \(D\ge3\), every Hamiltonian neighbourhood therefore contains:

- a simple exactly periodic Hamiltonian (\(\tau=1\)); and
- a simple Hamiltonian with no positive exact projective return
  (\(\tau\ge2\)).

They can be made uniformly indistinguishable on every finite horizon fixed
before the perturbation is chosen.

## Corollary 2 — every recurrence dimension is topologically interleaved

For a simple rank-\(k\) spectrum, closure of its projective phase orbit is a
compact connected abelian Lie group of dimension \(k\), hence a \(k\)-torus
up to a finite character presentation.

Theorem B implies that every Hamiltonian neighbourhood contains phase-orbit
closures of every dimension \(1,\ldots,D-1\). Thus no exact
recurrence-torus dimension defines an open Hamiltonian phase.

Maximal dimension remains residual and full measure. “Generic” and
“structurally stable” are therefore inequivalent:

```text
maximal recurrence dimension = typical by category and measure;
maximal recurrence dimension ≠ open under perturbation.
```

## Corollary 3 — dense local return-density exponents

Let \(R_K(\varepsilon)\) be the projective operator-norm return target in the
phase-orbit closure of a simple \(K\). Haar measure in the induced local
metric obeys
\[
  c_-(K)\varepsilon^{\tau(K)}
  \le
  m_K(R_K(\varepsilon))
  \le
  c_+(K)\varepsilon^{\tau(K)}
  \tag{4}
\]
for all sufficiently small \(\varepsilon>0\), with positive finite
constants depending on the integer embedding of the torus.

Consequently
\[
  \boxed{
  \lim_{\varepsilon\downarrow0}
  \frac{\log m_K(R_K(\varepsilon))}
       {\log\varepsilon}
  =
  \tau(K).
  }
  \tag{5}
\]

Every Hamiltonian neighbourhood contains every exponent
\(1,\ldots,D-1\).

For maximal rank \(D-1\), the full coordinate torus gives the exact law
\[
  m_K(R_K(\varepsilon))
  =
  \left(
    \frac{2\arcsin(\varepsilon/2)}{\pi}
  \right)^{D-1},
  \qquad 0<\varepsilon<2.
  \tag{6}
\]
No corresponding exact product formula is asserted for an arbitrary
lower-rank integer embedding.

## Proof of Corollary 3

The closure torus is a compact smooth \(k\)-dimensional Lie group. The
operator-norm phase metric restricted to it is locally bi-Lipschitz to a norm
on its Lie algebra because the character embedding has injective derivative
after quotienting its finite kernel. Haar measure has a smooth positive
translation-invariant density in exponential coordinates. Small metric balls
therefore satisfy `(4)`, and `(5)` follows.

Equation `(6)` is the existing maximal-rank coordinate-torus calculation.

## What this theorem changes

The usual statement “generic spectra are rationally independent” hides a
physically decisive topological fact:

> **The typical infinite-time phase is not stable under arbitrarily small
> Hamiltonian perturbation.**

Measure-one genericity predicts what a randomly parameterized exact model
does. It does not make exact recurrence dimension robust, experimentally
certifiable, or locally constant.

Theorem C shows that the instability is not accompanied by a bounded-time
dynamical singularity. Exact arithmetic completion and finite-horizon
dynamics are different layers.

## Why this is not yet the Nature law

Theorems A--C and their corollaries expose a universal obstruction. Their
ingredients—density of rational relations, Kronecker phase closure and phase
Lipschitz continuity—are individually elementary or classical.

A Nature-level paper needs the positive replacement:

> a canonical, perturbation-stable, observer-relative finite-scale temporal
> relation spectrum whose projections recover interaction birth,
> finite-horizon dimension, exact arithmetic completion, open-system
> persistence and return laws.

Without that replacement, “eternity is nowhere stable” is a strong no-go and
worldview statement, not yet a new complete physical law.

## Formalization obligations

1. Define finite rational coordinate rank.
2. Prove density of every exact rank \(k\).
3. Prove rational-hyperplane avoidance while preserving exact rank.
4. Lift to same-eigenvector Hermitian perturbations of every projective rank.
5. Prove scalar and diagonal-unitary bounded-horizon estimates.
6. Prove dense exact-periodic/nonperiodic separation.
7. Connect exact rank to compact phase-orbit dimension.
8. Formalize local Haar exponent `(5)` or use an existing covering-dimension
   theorem with an exact stated metric boundary.
9. Reuse the existing maximal-rank exact density theorem for `(6)`.
10. Run axiom and lint audit before promotion.

## External priority obligations

Audit:

- structural stability of almost-periodic and quasiperiodic flows;
- topology of rational-rank strata;
- quantum recurrence under Hamiltonian perturbations;
- exact versus approximate periodicity in finite quantum clocks;
- robust Diophantine dimension and frequency-map conditioning;
- phase-torus small-ball laws; and
- finite-horizon Hamiltonian discrimination.

Initial search found no source packaging dense realization of every temporal
rank, uniform bounded-horizon indistinguishability and dense return exponents
as one quantum-recurrence law. This is not a completed novelty claim.

## Gates

- [x] exact statement and dependency-closed paper proof
- [ ] unconditional Lean formalization
- [ ] positive finite-scale replacement law
- [ ] collision-complete external novelty audit
- [ ] feasible protocol with finite error analysis
- [ ] Nature hostile review

## Log

- 2026-07-30 — Extracted from the rational/irrational counterexample that
  killed the ordinary asymptotic-boundary conjecture.
- 2026-07-30 — Strengthened from dense rank-one/maximal-rank separation to
  dense realization of every rational rank and same-eigenvector
  bounded-horizon indistinguishability.
- 2026-07-30 — Corrected finite-\(\varepsilon\) density claim: exact product
  formula is retained only at maximal rank; arbitrary rank receives local
  exponent with lattice-dependent constants.
