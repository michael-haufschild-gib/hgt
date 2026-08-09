# Invariant-positivity reversibility wall and KMS irreversibility-measure law

- **ID:** ULF-IPKMS-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** hostile attack on antipode-defect bialgebraic law genesis
- **Statement:** Faithful invariant positivity forces a compact monoid to be a group, whereas positive-temperature KMS balance on a marked isometry retains and exactly measures the one-sided defect and cannot descend to the reversible quotient.
- **Status:** [PAPER-PROVED] [FIELD-LEVEL FAILURE/SURVIVOR] [CLASSICAL SEMIGROUP/KMS PARENTS] [NOT RH] [NO LEAN]

## 1. Faithful invariant positivity forces reversibility

Let (M) be a compact Hausdorff topological monoid. For (x\in M), write

\[
L_x(y)=xy.
\]

Let \(\mu\) be a Borel probability measure with full support and suppose

\[
(L_x)_*\mu=\mu
\qquad(x\in M).
\tag{1}
\]

### Theorem 1.1

Under these hypotheses, (M) is a compact topological group.

### Proof

For a continuous map from a compact space to a Hausdorff space,

\[
\operatorname{supp}(f_*\mu)=f(\operatorname{supp}\mu).
\]

Indeed, a point outside the compact image has a neighbourhood of zero pushforward measure; if
(f(z)) lies in an open set (U), then (f^{-1}(U)) is a neighbourhood of (z) and has positive
measure when (z\in\operatorname{supp}\mu). Applying this to (L_x), (1) and full support give

\[
M=\operatorname{supp}\mu
=\operatorname{supp}(L_x)_*\mu
=L_x(M).
\]

Thus every (L_x) is surjective, so there is (y\in M) with (xy=1). Surjectivity of (L_y)
gives (z\in M) with (yz=1). Then

\[
x=x(yz)=(xy)z=z,
\]

and hence (yx=yz=1). Every element is invertible. A compact Hausdorff monoid whose elements are
invertible is a topological group: inversion has closed graph and is continuous by compactness of
the domain and Hausdorffness of the codomain. QED.

### Sharp erasure countermodel

If (M) has an absorbing zero (0), then left invariance under (L_0) forces

\[
\mu=(L_0)_*\mu=\delta_0.
\tag{2}
\]

Thus a non-group compact monoid can possess a canonical invariant probability, but that probability
may erase every transient and irreversible state. Full support is load-bearing.

## 2. KMS balance measures rather than erases irreversibility

Let ((A,\alpha)) be a unital (C^*)-dynamical system and let (v\in A) be an analytic isometry
with positive energy (E>0):

\[
v^*v=1,
\qquad
\alpha_t(v)=e^{itE}v.
\tag{3}
\]

Fix inverse temperature \(\beta>0\), put (q=e^{-\beta E}\), and let \(\varphi\) be a
(\mathrm{KMS}_\beta\) state.

### Theorem 2.1

For every (n\ge0),

\[
\varphi(v^n v^{*n})=q^n,
\tag{4}
\]

\[
\varphi(1-v^n v^{*n})=1-q^n,
\tag{5}
\]

and, for the orthogonal history layers

\[
p_n=v^n(1-vv^*)v^{*n},
\]

one has

\[
\boxed{\varphi(p_n)=(1-q)q^n.}
\tag{6}
\]

In particular, no (\mathrm{KMS}_\beta) state can factor through a quotient in which the image of
(v) is unitary.

### Proof

The KMS identity applied to (a=v^n), (b=v^{*n}) gives

\[
\varphi(v^n v^{*n})
=\varphi\!\left(v^{*n}\alpha_{i\beta}(v^n)\right)
=q^n\varphi(v^{*n}v^n)
=q^n,
\]

proving (4). Equations (5) and (6) follow by subtraction. If the image (u) of (v) in a quotient
were unitary and a KMS state descended, the same calculation at (n=1) would give

\[
1=\varphi(uu^*)=q\varphi(u^*u)=q,
\]

contradicting (0<q<1). QED.

## 3. Universal Toeplitz realization and uniqueness

Let \(\mathcal T=C^*(V)\) be the Toeplitz algebra of the unilateral shift on
(\ell^2(\mathbb N_0)), with gauge dynamics

\[
\alpha_t(V)=e^{itE}V.
\tag{7}
\]

Let (N e_n=n e_n). Then

\[
\rho_\beta=(1-q)q^N
\]

is positive trace-class of trace one, and

\[
\varphi_\beta(a)=\operatorname{Tr}(\rho_\beta a)
\tag{8}
\]

is a faithful (\mathrm{KMS}_\beta) state on \(\mathcal T\).

It is the unique (\mathrm{KMS}_\beta) state. Indeed, every KMS state is invariant under the
dynamics, so

\[
\varphi(V^mV^{*n})=0\quad(m\ne n),
\]

while (4) gives (q^n) on the diagonal. These monomials have dense linear span. Faithfulness of
(8) follows because all diagonal weights of \(\rho_\beta\) are strictly positive: if (a\ge0) and
\(\varphi_\beta(a)=0\), then every \(\langle e_n,ae_n\rangle=0\), so (a^{1/2}e_n=0) for all (n)
and (a=0).

The reversible symbol quotient

\[
\mathcal T\longrightarrow C(S^1),
\qquad V\longmapsto u,
\tag{9}
\]

therefore admits no positive-temperature KMS state for the descended gauge dynamics. The same
rank-one defect that obstructs the antipode/group completion is assigned strictly positive thermal
mass (1-q).

## 4. Exact field consequence

The original conjecture that invariant positivity could canonically select a faithful one-sided
representation is false already for compact classical monoids:

- faithful invariant positivity forces reversibility;
- invariant positivity on a genuinely one-sided monoid can survive by erasing its irreversible
  sector;
- KMS positivity retains one-sidedness only after adding a time/energy grading;
- the resulting thermal state is incompatible with reversible completion rather than a state on it.

Thus the stronger surviving primitive is not a bare bialgebra with a preferred invariant state. It
is a **marked law object with incompatible completions**: reversible/Hopf completion and faithful
thermal/GNS completion cannot be jointly realized at positive temperature. Their incompatibility is
quantified by the full geometric history distribution (6), not only by a stable index.

## 5. Hostile scope

- Theorem 1.1 is classical compact-semigroup reasoning.
- Theorem 2.1 is the standard KMS calculation for an analytic isometry.
- Toeplitz gauge KMS states are established operator-algebra theory.
- The energy grading and inverse temperature are additional constitutive data; a bare bialgebra does
  not select them.
- This theorem does not establish a universal field. It kills invariant-state selection and exposes
  completion incompatibility as the positive survivor.
- No differential hypertranscendence, physical action, arithmetic selector, or RH statement follows.

## 6. Primary parents

- A. Van Daele, *The Haar Measure on a Compact Quantum Group*, Proc. AMS 123 (1995),
  https://doi.org/10.1090/S0002-9939-1995-1277138-0.
- M. A. Aukhadiev, S. A. Grigoryan, E. V. Lipacheva,
  *Infinite-dimensional Compact Quantum Semigroup*, https://arxiv.org/abs/1104.4820.
- A. an Huef, M. Laca, I. Raeburn, A. Sims,
  *KMS states on C*-algebras associated to higher-rank graphs*,
  https://arxiv.org/abs/1212.6811.

## Log

- 2026-08-09 — invariant-state rescue falsified; faithful KMS defect distribution extracted.
