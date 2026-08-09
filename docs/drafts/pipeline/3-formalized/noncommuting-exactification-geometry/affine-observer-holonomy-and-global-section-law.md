# Affine observer holonomy and the global-section field equation

- **ID:** `affine-observer-holonomy-and-global-section-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper proof)
- **Program:** `noncommuting-exactification-geometry`
- **Scientific status:** `[UNCONDITIONAL] [GENERAL REPRESENTATION LAW]`
- **Scope:** unitary affine comparison data on connected graphs, finite or countably exhausted
- **Novelty discipline:** graph holonomy, spanning-tree gauges, least squares, and fixed-vector
  descriptions of flat sections are classical. New payload is the affine exactification field
  equation, its source-current decomposition, and the exact capacity criterion for cofinal observer
  consistency. No claim is made that local systems or graph Laplacians are new.

## 1. Setup

Let \(G=(V,E)\) be a connected graph. Every oriented edge \(e:u\to v\) carries:

- Hilbert spaces \(H_u,H_v\);
- a unitary linear comparison \(U_e:H_u\to H_v\);
- a translation/source defect \(b_e\in H_v\).

The affine observer transport is

\[
\Phi_e(x)=U_ex+b_e.                                            \tag{1.1}
\]

Reverse orientation is required to satisfy

\[
U_{\bar e}=U_e^{-1},
\qquad
b_{\bar e}=-U_e^{-1}b_e,                                      \tag{1.2}
\]

so \(\Phi_{\bar e}=\Phi_e^{-1}\).

An **exact global presentation** is a family \(x=(x_v)_{v\in V}\) such that

\[
x_v=U_ex_u+b_e                                                  \tag{1.3}
\]

for every edge \(e:u\to v\).

The linear case is \(b_e=0\). The affine term is essential: it records source mismatch instead of
placing all obstruction in the connection.

## 2. Spanning-tree reduction

Choose a root \(o\in V\) and a spanning tree \(T\). Unique tree paths give a unitary

\[
A_v:H_o\longrightarrow H_v                                   \tag{2.1}
\]

and a vector \(a_v\in H_v\) such that satisfying all tree-edge equations is equivalent to

\[
x_v=A_vx_o+a_v.                                                \tag{2.2}
\]

For a chord \(e:u\to v\), define its based linear holonomy and affine source current by

\[
H_e=A_v^{-1}U_eA_u,                                            \tag{2.3}
\]

\[
c_e=A_v^{-1}(U_ea_u+b_e-a_v).                                  \tag{2.4}
\]

Both live in the root Hilbert space \(H_o\).

## 3. Global-section theorem

### Theorem 3.1 — unified objects are affine holonomy fixed points

Restriction to the root gives a bijection between exact global presentations and solutions
\(x\in H_o\) of

\[
(I-H_e)x=c_e                                                   \tag{3.1}
\]

for every chord \(e\in E\setminus T\).

In the linear case,

\[
\{\text{exact global presentations}\}
\cong
\bigcap_{e\notin T}\operatorname{Fix}(H_e).                   \tag{3.2}
\]

#### Proof

Every root value \(x_o=x\) extends uniquely along the tree by (2.2), so all tree-edge equations
hold. For a chord \(e:u\to v\), its remaining equation is

\[
A_vx+a_v=U_e(A_ux+a_u)+b_e.
\]

Multiplying by \(A_v^{-1}\) and rearranging gives

\[
(I-A_v^{-1}U_eA_u)x
=A_v^{-1}(U_ea_u+b_e-a_v),
\]

which is exactly (3.1). Thus a root value extends to a global presentation if and only if it
satisfies all chord equations. The correspondence is bijective because tree extension is unique.
Setting every \(b_e\), hence every \(a_v,c_e\), equal to zero gives (3.2). ∎

### Meaning

The combined constraint is not located at a preferred vertex. It is the affine fixed locus of
observer holonomy. Choosing a different route to the same observer produces a loop; exact unification
requires invariance under its holonomy.

## 4. The observer field equation

Assume first that \(G\) has finitely many chords. Define

\[
D:H_o\longrightarrow\bigoplus_{e\notin T}H_o,
\qquad
Dx=((I-H_e)x)_{e\notin T},                                    \tag{4.1}
\]

and \(c=(c_e)_{e\notin T}\). The affine precision energy is

\[
\mathcal E(x)=\|Dx-c\|^2
=\sum_{e\notin T}\|(I-H_e)x-c_e\|^2.                          \tag{4.2}
\]

Define

\[
\Delta_{\mathrm{hol}}=D^*D
=\sum_{e\notin T}(I-H_e)^*(I-H_e),                             \tag{4.3}
\]

and

\[
J_{\mathrm{src}}=D^*c
=\sum_{e\notin T}(I-H_e)^*c_e.                                \tag{4.4}
\]

### Theorem 4.1 — affine observer field equation

Every exact global presentation satisfies

\[
\Delta_{\mathrm{hol}}x=J_{\mathrm{src}}.                      \tag{4.5}
\]

Conversely, a solution of (4.5) is an exact global presentation if and only if

\[
\mathcal E(x)=0.                                               \tag{4.6}
\]

If an exact global presentation exists, the set of all such root values is

\[
x_0+\ker\Delta_{\mathrm{hol}}                                 \tag{4.7}
\]

for any one solution \(x_0\).

#### Proof

Differentiating the quadratic functional (4.2), or expanding its first variation, gives

\[
\frac12d\mathcal E_x(h)
=\operatorname{Re}\langle D^*(Dx-c),h\rangle.
\]

Thus its critical points satisfy

\[
D^*Dx=D^*c,
\]

which is (4.5). If \(x\) is exact, then \(Dx=c\), so it satisfies both (4.5) and (4.6).
Conversely, (4.6) says \(Dx=c\), hence all chord equations hold; Theorem 3.1 gives a global
presentation.

If \(Dx_0=c\), then all other exact solutions are \(x_0+\ker D\). Since
\(\ker D=\ker D^*D=\ker\Delta_{\mathrm{hol}}\), this is (4.7). ∎

### Warning

The normal equation alone is not the exact constraint. If \(c\notin\operatorname{ran}D\), (4.5)
can have a least-squares solution with positive residual. Exactness requires the separate provenance
condition (4.6). This is the affine analogue of retaining \(B\subseteq Z\) instead of only a
quotient spectrum.

## 5. Linear holonomy uncertainty

In the linear case, put

\[
W=\bigcap_{e\notin T}\operatorname{Fix}(H_e)
=\ker\Delta_{\mathrm{hol}}.                                   \tag{5.1}
\]

Define

\[
\mu_{\mathrm{hol}}
=\inf_{\substack{x\perp W\\\|x\|=1}}
\langle\Delta_{\mathrm{hol}}x,x\rangle.                       \tag{5.2}
\]

### Corollary 5.1 — exact, hard, and almost-invariant regimes

1. \(W\neq0\) exactly when nonzero linear global presentations exist.
2. \(\mu_{\mathrm{hol}}>0\) exactly when the holonomy defect map \(D\) has closed range.
3. If \(W=0\) and \(\mu_{\mathrm{hol}}=0\), there are unit vectors \(x_n\) with

   \[
   \|(I-H_e)x_n\|\longrightarrow0                              \tag{5.3}
   \]

   simultaneously for every chord in the finite graph, although no nonzero exact global
   presentation exists.

#### Proof

This is Theorem 3.1 of
`constraint-laplacian-uncertainty-and-capacity-horizon.md` applied to the closed subspaces
\(\operatorname{Fix}(H_e)\), or directly to the bounded operator \(D\). Equation (4.3) gives
\(D^*D=\Delta_{\mathrm{hol}}\). ∎

The last regime is observer contextuality with almost-global sections. It is mathematically distinct
from a positive uncertainty gap.

## 6. Gauge covariance

Let \(G_v:H_v\to H'_v\) be unitary changes of observer frame. Define

\[
U'_e=G_vU_eG_u^{-1},
\qquad
b'_e=G_vb_e.                                                   \tag{6.1}
\]

### Proposition 6.1 — frame covariance

The map \(x_v\mapsto G_vx_v\) bijects exact global presentations before and after (6.1).
At the root, based holonomies and currents transform by

\[
H'_e=G_oH_eG_o^{-1},
\qquad
c'_e=G_oc_e,                                                   \tag{6.2}
\]

after the corresponding tree gauge is chosen. Consequently,

\[
\Delta'_{\mathrm{hol}}
=G_o\Delta_{\mathrm{hol}}G_o^{-1},
\qquad
J'_{\mathrm{src}}=G_oJ_{\mathrm{src}},                        \tag{6.3}
\]

and (4.5)--(4.6) are observer-frame invariant.

#### Proof

Applying \(G_v\) to (1.3) gives

\[
G_vx_v=G_vU_eG_u^{-1}(G_ux_u)+G_vb_e,
\]

which is the primed edge equation. Tree transports telescope, leaving only \(G_o\) at the
basepoint, proving (6.2). Substitution into (4.3)--(4.4) proves (6.3). ∎

### Remark on affine frame shifts

One can also allow \(x'_v=G_vx_v+d_v\). Then \(b_e\) acquires the usual affine coboundary
\(d_v-U'_ed_u\). Loop translations change by affine conjugacy, and the exact-section set remains
invariant. The linear-frame case above is enough for the present theorem and avoids unnecessary
notation.

## 7. Independence from spanning tree

The equations depend on a tree gauge; existence does not.

### Proposition 7.1 — tree-independent exactness and gap type

For a finite graph, changing root or spanning tree:

1. preserves the affine global-section set up to the canonical root transport;
2. conjugates the holonomy group;
3. preserves whether the linear transverse gap is positive or zero, although its numerical value
   may change with the finite generating-loop set.

#### Proof

Part 1 follows because both tree reductions are bijections with the same edgewise global sections.
Based loop holonomies at different roots are conjugate by path transport, proving part 2.

Two spanning trees give two finite generating sets for the same finitely generated fundamental
group. Every generator in one set is a word of bounded length in generators and inverses from the
other. For a unitary representation and a word \(g=s_1\cdots s_L\), telescoping gives

\[
\|\pi(g)x-x\|
\leq\sum_{k=1}^L\|\pi(s_k)x-x\|.                              \tag{7.1}
\]

Hence the two finite sums of squared generator defects bound each other up to positive constants.
They have the same kernel, and one has a positive lower bound on its kernel complement exactly when
the other does. ∎

## 8. Countable contexts and the capacity criterion

Now let the chord set be countable, enumerated \(e_1,e_2,\ldots\). Define finite-context solution
sets

\[
C_n=\left\{x\in H_o:(I-H_{e_k})x=c_{e_k}
\text{ for }1\leq k\leq n\right\}.                            \tag{8.1}
\]

Each \(C_n\) is a closed affine subspace and
\(C_1\supseteq C_2\supseteq\cdots\).

### Theorem 8.1 — cofinal observer globalization

Assume every finite observer problem is consistent, so \(C_n\neq\varnothing\) for all \(n\).
Then a global presentation for all countably many contexts exists if and only if

\[
\sup_n\operatorname{dist}(0,C_n)<\infty.                      \tag{8.2}
\]

#### Proof

The global root values are exactly \(\bigcap_n C_n\) by Theorem 3.1. Apply the nested closed
convex capacity criterion proved in
`constraint-laplacian-uncertainty-and-capacity-horizon.md`. ∎

### Corollary 8.2 — finite-consistency mirage has one exact cause

If every finite observer family has an exact unified presentation but the countable family does
not, then

\[
\operatorname{dist}(0,C_n)\longrightarrow\infty.              \tag{8.3}
\]

Thus the obstruction is not hidden finite inconsistency. Compatible root data escape every bounded
capacity set.

## 9. Interpretation for heterogeneous mathematics

The theorem applies after constructing typed comparison maps between observer fibers. Its roles are:

- \(U_e\): change of exact representation between arithmetic, spectral, geometric, or topological
  charts;
- \(b_e\): literal source/provenance mismatch that cannot be absorbed into homogeneous transport;
- \(H_e\): route holonomy around a comparison loop;
- \(c_e\): accumulated source current around that loop;
- \(\Delta_{\mathrm{hol}}\): observer-space metric/normal operator;
- \(J_{\mathrm{src}}\): source term forced by affine mismatch;
- \(\mathcal E=0\): exact integrability, not merely stationary least squares.

This is the first closed field equation of noncommuting exactification geometry:

\[
\boxed{\Delta_{\mathrm{hol}}x=J_{\mathrm{src}},
\qquad \mathcal E(x)=0.}                                      \tag{9.1}
\]

It is kinematic, not yet an RH theorem. Its scientific content appears only when \(U_e,b_e\) are
constructed from a source rather than chosen to encode the desired answer.

## 10. Hostile review

### Attack A — spanning-tree choice inserts the result

False. The tree only gauges away contractible comparisons. Theorem 7.1 proves exactness and gap type
are invariant.

### Attack B — the normal equation always produces a fake solution

The paper explicitly forbids that inference. Exactness is (4.5) **and** zero residual (4.6).
Positive-residual least squares is not a global section.

### Attack C — affine source terms can be gauged away locally

Tree-edge terms can; loop translations \(c_e\) survive. Their affine conjugacy class is the
source-current holonomy. That is exactly why the reduction keeps chords.

### Attack D — finite consistency should imply countable consistency

Not without bounded capacity. Theorem 8.1 gives the exact missing hypothesis.

### Attack E — this solves RH by calling a holonomy fixed point the answer

No. No canonical RH observer graph or affine comparisons have yet been constructed. Equation (9.1)
is a general representation law and a strict target for route synthesis.

## 11. Novelty and significance verdict

- **Classical pieces:** graph connection, holonomy, spanning-tree gauge, fixed vectors, normal
  equations, weak compactness.
- **New assembly:** heterogeneous exactification as an affine observer local system; literal source
  defects become translational holonomy; unified objects are global sections; the source field
  equation and zero-residual integrability are separated; countable globalization is exactly bounded
  solution capacity.
- **Significance:** provides a precise mathematical location for the “combined constraint” without
  assuming it is an object in any one field. It also predicts two distinct failure modes: holonomy
  incompatibility and capacity escape.
- **Current ceiling:** no source-native arithmetic--spectral--geometric observer graph has yet been
  built, so direct RH leverage remains open.

## 12. Lean return notes

Do not write Lean in this phase. Later formalization can use finite graphs first:

1. affine edge transports and tree extension;
2. chord-equation equivalence;
3. finite direct-sum normal operator and kernel;
4. two spanning-tree generating-set comparison;
5. nested affine capacity theorem as a separate analytic import.

Search the existing formal corpus for graph spanning trees, unitary maps, affine isometries, and
positive operators before selecting files. No path is guessed here.
