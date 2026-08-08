# Resource-filtered relation typicality and recurrence no-go

- **ID:** `resource-filtered-relation-typicality-recurrence-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONSTRAINT RELATIVITY / DYNAMICAL MODEL
- **Scientific status:** `[PAPER-PROVED] [NO LEAN WRITTEN OR BUILT] [NOT RH]`
- **Novelty status:** the determinantal-stratification and recurrence ingredients are classical.
  Candidate-new content is their use as one exact law separating conserved full relations from
  resource-filtered relation visibility, together with the interaction tidal tensor. External
  priority remains open.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

A reversible evolution does not destroy exact relations. It transports them. What can disappear
is their intersection with a fixed low-resource observer language. This distinction is necessary
before comparing relation geometry with quantum complexity or recurrence.

This card proves four claims.

1. Exact relation rank is conserved under invertible evolution.
2. Low-resource exact-relation rank is generically minimal; relation-rich times form a proper
   determinantal analytic subset.
3. A recurrent finite system admits no nonconstant continuous monotone complexity law.
4. For unitary evolution, initial escape from a reporter sector has an exact second-order
   coefficient: the squared normal commutator. This gives a non-fitted interaction curvature.

## 2. Analytic relation transport

Let `V` be an `n`-dimensional real or complex vector space, `Q subset V` a fixed
`q`-dimensional resource-bounded observer space, and `R_0 subset V` an `r`-dimensional exact
relation space. Let `M` be a connected real-analytic manifold and

\[
 U:M\longrightarrow \operatorname{GL}(V)
 \tag{2.1}
\]

be real analytic. Put

\[
 R_x=U(x)R_0,
 \qquad
 d_Q(x)=\dim(R_x\cap Q).
 \tag{2.2}
\]

The full relation rank is always `r`. The resource-filtered relation rank `d_Q(x)` need not be
constant.

### Theorem 2.1 — determinantal typicality of accessible relations

Put

\[
 d_*=\min_{x\in M}d_Q(x).
 \tag{2.3}
\]

Then:

1. `d_Q(x) >= max(0,r+q-n)` for every `x`;
2. the generic stratum
   \[
   M_{\mathrm{gen}}=\{x:d_Q(x)=d_*\}
   \tag{2.4}
   \]
   is open and dense;
3. the exceptional set
   \[
   \Sigma_Q=\{x:d_Q(x)>d_*\}
   \tag{2.5}
   \]
   is a proper real-analytic determinantal subset, hence has empty interior and measure zero in
   every analytic coordinate chart;
4. if `M` is one-dimensional, `Sigma_Q` is discrete; if moreover `M` is compact without
   boundary, it is finite;
5. if the orbit contains one subspace transverse to `Q` in the dimensionally allowed sense, then
   \[
   d_*=\max(0,r+q-n).
   \tag{2.6}
   \]

#### Proof

Let `pi:V -> V/Q` be the quotient map. For every `x`, rank-nullity on `R_x` gives

\[
 d_Q(x)
 =\dim\ker(\pi|_{R_x})
 =r-\operatorname{rank}(\pi|_{R_x}).
 \tag{2.7}
\]

Since `dim(V/Q)=n-q`, equation `(2.7)` gives

\[
 d_Q(x)\ge r-(n-q)=r+q-n,
\]

and nonnegativity gives claim 1.

On any analytic coordinate neighborhood in `M`, the vectors `U(x)e_1,...,U(x)e_r`, for a fixed
basis of `R_0`, give an analytic frame of `R_x`. Relative to fixed coordinates on `V/Q`, the map
`pi|_{R_x}` is therefore an analytic `(n-q) x r` matrix `A(x)`. Put

\[
 m_*=r-d_*=\max_{x\in M}\operatorname{rank}A(x).
 \tag{2.8}
\]

The condition `d_Q(x)>d_*` is equivalent to `rank A(x)<m_*`, hence to simultaneous vanishing of
all `m_* x m_*` minors. At least one such minor is nonzero somewhere by definition of `m_*`.
Thus `Sigma_Q` is a proper real-analytic determinantal subset. Its complement is open. A proper
real-analytic subset of a connected real-analytic manifold has empty interior and measure zero;
therefore the complement is dense and claims 2 and 3 follow.

On a one-dimensional analytic manifold, zeros of a nonzero analytic minor are isolated. The
exceptional set is contained in that zero set, so it is discrete. A discrete closed subset of a
compact one-dimensional manifold is finite, proving claim 4.

Finally, a dimensionally transverse position is precisely one for which equality holds in the
lower bound of claim 1. If the orbit contains such a point, `(2.3)` and claim 1 give `(2.6)`.
QED.

### Structural defect

Put

\[
 \rho_*=\min(r,n-q),
 \qquad
 \rho=\max_x\operatorname{rank}(\pi|_{R_x}),
 \qquad
 s=\rho_*-\rho\ge0.
 \tag{2.10}
\]

Then

\[
 \boxed{d_*=\max(0,r+q-n)+s.}
 \tag{2.11}
\]

Moreover, `s>0` exactly when every `rho_* x rho_*` minor vanishes identically. Thus a symmetry or
conservation law can force a persistent excess above transverse dimension. Theorem 2.1 still says
that jumps above this actual generic baseline form a thin set. Structural defect and exceptional
return must not be conflated.

### Corollary 2.2 — Haar-typical resource rank

If `V` is a finite-dimensional Hilbert space and `U` is Haar distributed on its orthogonal or
unitary group, then

\[
 \dim(UR_0\cap Q)=\max(0,r+q-n)
 \tag{2.9}
\]

with probability one.

#### Proof

There exists a subspace of dimension `r` in dimensionally transverse position to `Q`. The
nontransverse locus in the Grassmannian is the proper determinantal locus from Theorem 2.1. Its
inverse image in the compact group is a proper real-analytic subset and therefore has Haar measure
zero. QED.

### Interpretation

`R_x` is the conserved full law bundle. `R_x cap Q` is the part possessing a certificate in one
bounded-cost language. The theorem says relation-poor observer states are typical; relation-rich
states are determinantal exceptions. It does not say time evolution is monotone.

## 3. Continuous visibility and exact jumps

Assume now that `V` is a Hilbert space and let `P_R(x)` and `P_Q` be orthogonal projections. Define
the soft visibility score

\[
 \nu_Q(x)=\operatorname{Tr}(P_R(x)P_Q).
 \tag{3.1}
\]

It is the sum of squared cosines of principal angles between `R_x` and `Q`. It varies continuously
(analytically along an analytic orbit), while `d_Q(x)` counts only principal angles equal to zero.
Thus an approximate recurrence restores `nu_Q` approximately without necessarily restoring an
exact relation or landing in `Sigma_Q`.

This distinguishes three notions which must not be conflated:

1. full exact relations: `R_x`, constant rank;
2. exact low-resource certificates: `R_x cap Q`, determinantal and discontinuous in rank;
3. approximate low-resource visibility: `nu_Q(x)`, continuous.

## 4. Recurrence forbids an exact monotone second law

### Theorem 4.1 — recurrence no-go

Let `X` be a topological space, `Phi_t:X->X` a continuous semiflow, and `x in X` recurrent: there
is a sequence `t_j -> infinity` with

\[
 \Phi_{t_j}(x)\longrightarrow x.
 \tag{4.1}
\]

If `C:X->R` is continuous and

\[
 t\longmapsto C(\Phi_t(x))
 \tag{4.2}
\]

is nondecreasing, then it is constant on the entire forward orbit of `x`.

#### Proof

Fix `s>=0`. For all sufficiently large `j`, `t_j>=s`, so monotonicity gives

\[
 C(x)\le C(\Phi_s(x))\le C(\Phi_{t_j}(x)).
 \tag{4.3}
\]

Continuity and `(4.1)` make the rightmost term converge to `C(x)`. Hence equality holds throughout
`(4.3)`, and `C(Phi_s(x))=C(x)`. QED.

### Corollary 4.2 — statistical form of a complexity second law

On a recurrent finite quantum orbit, no nonconstant continuous circuit-complexity surrogate can
be exactly nondecreasing for all time. Any Brown--Susskind-type second law must therefore be one
of the following:

1. a high-probability statement from a special low-complexity initial condition;
2. a coarse-grained or resource-bounded statement;
3. a pre-recurrence-time statement;
4. an open-system statement with irreversible structure.

This conclusion follows from recurrence alone and does not use holography.

## 5. Interaction tidal law

Let `mathcal H` be a finite-dimensional Hilbert space, `L subset mathcal H` a reporter sector with
orthogonal projection `P`, and `A` a skew-adjoint operator. For `x in L`, put

\[
 x(t)=e^{tA}x,
 \qquad
 h_x(t)=\|(I-P)x(t)\|^2.
 \tag{5.1}
\]

### Theorem 5.1 — exact normal acceleration

For every `x in L`,

\[
 h_x(0)=h_x'(0)=0,
 \qquad
 \boxed{h_x''(0)=2\|(I-P)Ax\|^2.}
 \tag{5.2}
\]

Equivalently, visible weight `v_x(t)=||Px(t)||^2` obeys

\[
 \boxed{v_x''(0)=-2\|(I-P)Ax\|^2.}
 \tag{5.3}
\]

#### Proof

Because `(I-P)x=0`, Taylor expansion gives

\[
 (I-P)x(t)=t(I-P)Ax+O(t^2).
\]

Squaring the norm proves `(5.2)`. Skew-adjointness makes `||x(t)||=||x||`, so
`v_x(t)+h_x(t)=||x||^2`; differentiating twice proves `(5.3)`. QED.

Define the **reporter tidal form**

\[
 \mathcal T_{A,L}(x)=\|(I-P)Ax\|^2.
 \tag{5.4}
\]

It is not chosen to fit the observed loss: it is forced by the normal component of the generator
and is experimentally recoverable as one half of initial hidden-weight acceleration.

### Corollary 5.2 — finite bipartite quantum classifier

Let `mathcal H=Herm_0(A tensor B)` with Hilbert--Schmidt metric and local reporter sector

\[
 \mathcal L=(Herm_0(A)\otimes I)\oplus(I\otimes Herm_0(B)).
\]

For Hamiltonian `H`, take `A_H(X)=i[H,X]`. Then the following are equivalent:

1. `mathcal T_{A_H,mathcal L}(X)=0` for every local reporter `X`;
2. `i[H,mathcal L] subset mathcal L`;
3. `H=H_A tensor I+I tensor H_B+cI`.

Hence every genuine interaction has strictly positive tidal form on some boundary reporter.

#### Proof

Theorem 5.1 makes 1 equivalent to 2. Equivalence of 2 and 3 is the interaction cross-fibre
classifier proved in `passive-relation-triangle-energy-and-interaction-cross-fibre-law.md`.
QED.

### Theorem 5.3 — aggregate tidal tomography

Let `a=dim A`, `b=dim B`, and decompose a Hermitian Hamiltonian orthogonally as

\[
 H=H_A\otimes I+I\otimes H_B+cI+H_{\mathrm{cross}},
 \qquad
 H_{\mathrm{cross}}\in Herm_0(A)\otimes Herm_0(B).
 \tag{5.5}
\]

Choose Hilbert--Schmidt orthonormal bases `{A_alpha}` and `{B_beta}` of the two traceless
Hermitian spaces. The normalized local reporter basis is

\[
 \mathcal E_{\mathcal L}
 =\left\{{A_\alpha\otimes I\over\sqrt b}\right\}_\alpha
 \cup
 \left\{{I\otimes B_\beta\over\sqrt a}\right\}_\beta.
 \tag{5.6}
\]

For `O in mathcal E_mathcal L`, let `h_O` be hidden weight from `(5.1)` under generator
`i ad_H`. Then

\[
 \boxed{
 \sum_{O\in\mathcal E_{\mathcal L}}h_O''(0)
 =4\left({a\over b}+{b\over a}\right)
 \|H_{\mathrm{cross}}\|_{\mathrm{HS}}^2.}
 \tag{5.7}
\]

Hence complete second-order boundary leakage determines the norm of the entire interaction sector
and is independent of all local Hamiltonian terms.

#### Proof

Expand

\[
 H_{\mathrm{cross}}=\sum_{\mu,\nu}h_{\mu\nu}A_\mu\otimes B_\nu,
 \qquad
 C_\nu=\sum_\mu h_{\mu\nu}A_\mu.
\]

For `O_alpha=A_alpha tensor I/sqrt b`, only the cross term has a normal component, and

\[
 \|(I-P)i[H,O_\alpha]\|^2
 ={1\over b}\sum_\nu\|[C_\nu,A_\alpha]\|^2.
 \tag{5.8}
\]

For every traceless Hermitian `C in M_a(C)`, the adjoint Casimir identity is

\[
 \sum_\alpha\|[C,A_\alpha]\|^2=2a\|C\|^2.
 \tag{5.9}
\]

To verify `(5.9)`, diagonalize `C=diag(c_1,...,c_a)`. Diagonal basis elements contribute zero;
the normalized symmetric and antisymmetric matrix units for each `i<j` contribute twice
`(c_i-c_j)^2`. Therefore the sum is

\[
 2\sum_{i<j}(c_i-c_j)^2
 =2\left(a\sum_i c_i^2-(\sum_i c_i)^2\right)
 =2a\|C\|^2,
\]

using `Tr C=0`. Summing `(5.8)` over `alpha` gives

\[
 {2a\over b}\|H_{\mathrm{cross}}\|^2.
\]

The `B` reporters analogously give `2b/a` times the same norm. Theorem 5.1 multiplies the total
normal-velocity square by two, proving `(5.7)`. QED.

### Example 5.4 — two-qubit interaction

For `H=Z tensor Z` and `X=X tensor I`,

\[
 e^{itH}Xe^{-itH}
 =\cos(2t)X\otimes I-\sin(2t)Y\otimes Z.
\]

Thus hidden weight is `sin^2(2t)||X||^2`, and its second derivative at zero is
`8||X||^2`. The reporter tidal form is `4||X||^2`, exactly half that acceleration.

## 6. New predictions and falsifiers

### Prediction 1 — plateau as a generic stratum

For a fixed resource language `Q`, a generic analytic orbit spends almost every parameter value
on the minimum-intersection stratum. Exact low-cost relation revivals occur only on a thin
determinantal set unless symmetry forces a persistent rank excess.

### Prediction 2 — near recurrence differs from exact relation recurrence

Long-time near recurrence can restore the continuous visibility `nu_Q` without restoring
`d_Q`. A theory predicting exact algebraic relation revival from phase proximity alone is false.

### Prediction 3 — coupling is visible as normal acceleration

A genuinely nonlocal Hamiltonian can be detected without reconstructing the hidden cross-fibre:
some local reporter has negative initial visible-weight acceleration, whose magnitude is twice
the tidal form.

### Prediction 4 — aggregate leakage measures total interaction strength

Complete initial boundary tidal data determine `||H_cross||_HS` by `(5.7)` without reconstructing
local Hamiltonian terms. Any physical realization of the relation bridge that gives a different
coefficient falsifies this finite bipartite model.

### Fatal tests

This card does not supply:

1. a canonical choice of resource filtration `Q_k`;
2. a complexity metric or a theorem identifying `-log nu_Q` with circuit complexity;
3. irreversible dynamics in a closed recurrent system;
4. a gravitational or wormhole realization;
5. an RH selector;
6. novelty for determinantal stratification, principal angles, or operator growth separately.

Any claimed general field must derive the resource filtration from source relations and prove an
operational comparison with complexity. Supplying `Q_k` by hand leaves background mechanics in
place.

## 7. Lean handoff notes

No Lean code was written or built. A later formalization can likely use finite-dimensional
subspace dimension/rank-nullity for the algebraic core. Real-analytic determinantal geometry and
measure-zero claims may require substantial new infrastructure; formalize the finite polynomial
or one-parameter matrix versions first. The recurrence no-go has elementary order/topology
dependencies and should be isolated from quantum definitions.
