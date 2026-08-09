# Marked-symmetry experiment quotient, recurrence, and lift law

- **ID:** ULF-MSQ-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** constitutive experimental mathematics
- **Statement:** Marking an intervention replaces the passive gauge group by its intervention stabilizer, and the homogeneous quotient controls identifiability, recurrence, and lifted memory.

## Goal

Extract a coordinate-free theorem from the Gaussian synthesis. This is the first general law proposed
by constitutive experimental mathematics.

## Gates

- [x] 0 → 1: compact-group/source-law formulation
- [x] 1 → 2: dependency-closed group-action proof
- [ ] 2 → 3: no Lean formalization
- [ ] 3 → 4: no novelty/priority claim

## Setup

Let a compact Hausdorff group (H) act continuously on a Hausdorff space (X). Let
(\mathcal P(X)) be a Hausdorff space of probability laws on (X), with the induced pushforward
action. Choose:

- a passive source law (\mu\in\mathcal P(X)) invariant under all (H);
- a marked intervention law (\nu\in\mathcal P(X)).

Define its stabilizer

\[
K=\operatorname{Stab}_H(\nu)=\{h\in H:h_*\nu=\nu\}.
\tag{1}
\]

The passive response at (h) is (h_*\mu). The marked intervention response is (h_*\nu).

## Theorem 1 — relative gauge and exact experiment quotient

1. Every (h\in H) is invisible to passive observation:
   \[
   h_*\mu=\mu.
   \tag{2}
   \]
2. Two transformations (g,h\in H) have the same marked intervention response exactly when they
   lie in the same right (K)-coset:
   \[
   g_*\nu=h_*\nu
   \quad\Longleftrightarrow\quad
   h^{-1}g\in K.
   \tag{3}
   \]
3. The response map induces a continuous injection
   \[
   \overline\rho:H/K\hookrightarrow\mathcal P(X),
   \qquad gK\longmapsto g_*\nu.
   \tag{4}
   \]
   Since (H/K) is compact and (\mathcal P(X)) is Hausdorff, this is a homeomorphism onto its
   image.

Thus passive gauge group (H) shrinks to (K) after marking the intervention, and the exact
experiment phase space is the homogeneous space (H/K).

### Proof

Equation (2) is invariance. For (3), apply (h^{-1}_*) to both sides; equality becomes
((h^{-1}g)_*\nu=\nu). This is precisely membership in (K). Hence (4) is well-defined and
injective. Continuity follows from the action; compact-to-Hausdorff continuous injections are
embeddings. ∎

## Theorem 2 — compact response recurrence

Let (\gamma:\mathbb R\to H) be a continuous one-parameter subgroup. Then the intervention
response orbit

\[
t\longmapsto \gamma(t)K\in H/K
\tag{5}
\]

has compact closure and returns arbitrarily close to its initial point at arbitrarily large positive
times. If (\gamma(T)\in K) for some (T>0), it is exactly periodic with period (T).

### Proof

The closure (L=\overline{\gamma(\mathbb R)}\) is a compact abelian subgroup of (H). The positive
semiorbit has the same closure as the full subgroup orbit: its closure is a compact cancellative
subsemigroup of (L), hence a subgroup. Therefore the identity is approached at arbitrarily large
positive times unless it is hit periodically, and projection to (H/K) gives recurrence. Exact
periodicity follows from (\gamma(t+T)K=\gamma(t)\gamma(T)K=\gamma(t)K). ∎

## Theorem 3 — closed response and open lifted history

Suppose a path (\gamma:[0,T]\to H) starts at the identity and ends in (K). Its projected
response is a loop in (H/K). Let

\[
[\overline\gamma]\in\pi_1(H/K,K)
\tag{6}
\]

be its homotopy class. The lift of the response loop to the universal cover of (H/K), starting at a
chosen basepoint, is closed if and only if ([\overline\gamma]=0). Iterating a non-torsion class gives
a recurrent response whose lifted endpoints escape through distinct deck transformations.

### Proof

This is the path-lifting classification for universal covers. The endpoint of the lifted loop is the
deck transformation represented by (6). Iteration raises that deck transformation to successive
powers. ∎

## Corollary — positive phase erasure

Let (\chi:H\to U(1)) be a continuous character. Its positive modulus satisfies

\[
|\chi(h)|^2=1
\tag{7}
\]

for every (h), while a loop can have nontrivial (\chi)-winding. Thus a positive character norm
cannot recover phase history; a marked lift or phase-sensitive intervention is required.

## 2. Exact instantiation

For the isotropic Gaussian theorem:

- (H=SO(2));
- (\mu=N(0,I_2));
- (\nu\) is the law supported on the marked (e_2)-axis after
  (\operatorname{do}(U_1=0));
- (K=\{I,-I\}\);
- (H/K\cong\mathbb{RP}^1\cong S^1).

The half-turn path gives one nontrivial response loop and an open angle lift.

## 3. Hostile scope

This is classical compact-group action and covering-space theory. It does not say every source has a
compact symmetry group, every intervention is probabilistic, or every recurrent law has a nontrivial
lift. Its field content is a precise relative-gauge principle:

> gauge equivalence is the stabilizer of the declared experiment family, not an intrinsic property of
> a source transformation.

Any universal-law claim that calls routes gauges without constructing this stabilizer relation fails.

## Log

- 2026-08-09 — coordinate-free marked-symmetry response theorem created; no Lean.
