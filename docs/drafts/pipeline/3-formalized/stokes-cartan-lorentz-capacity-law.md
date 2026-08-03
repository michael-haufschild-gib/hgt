# Stokes--Cartan Lorentz-capacity law

## Metadata

- **Status:** Stage 3 -- exact core, capacity, corona, full-leg, and dimension laws formalized
- **Area:** irregular Riemann--Hilbert theory; wild nonabelian Hodge diagrams; fission trees;
  ultrametric matrices; Kac--Moody signatures
- **Created:** 2026-08-03
- **Rule:** existing contact tomography is prior research and input, never the novelty claim
- **Novelty label:** `[NEW]` for the Stokes--Cartan one-defect/global Lorentz law, subject to
  final hostile review; abstract ultrametric linear algebra remains `[BRIDGE]`

## 1. Target universal law

Let `B` be the core matrix of an arbitrary type-A irregular class after a one-pole reading,
let `r_i` be the ramification orders, and put `C=2I-B`.  Define complementary contact

\[
 K_{ij}=\begin{cases}
 1+B_{ij}/(r_i r_j),&i\ne j,\\
 1+(B_{ii}-1)/r_i^2,&i=j.
 \end{cases}
\]

Existing contact tomography realizes `K` on a finite rooted contact tree.  Extend its root to a
height `H>max(1,K_ij)`.  For every oriented edge `e`, let `ell_e>0` be its contact length and let
`A_e` be the descendant leaf set.  Write

\[
 u_e=(r_i\mathbf 1_{A_e}(i))_i,\qquad r=(r_i)_i,\qquad \lambda=H-1.
\]

`[CONJECTURE L -- EXACT ONE-DEFECT LAW]`

\[
 \boxed{\quad C=I+\sum_e\ell_e u_eu_e^{T}-\lambda rr^{T}.\quad}       \tag{L}
\]

Equivalently, for every real vector `x`,

\[
 \boxed{\quad x^TCx=\sum_i x_i^2+
 \sum_e\ell_e\Bigl(\sum_{i\in A_e}r_ix_i\Bigr)^2-
 (H-1)\Bigl(\sum_i r_ix_i\Bigr)^2.\quad}                              \tag{Q}
\]

This is the proposed universal law.  It has one and only one negative channel: total ramified
rank.  Every local fission/conormal channel is a positive square.

## 2. Immediate hard consequences

Let

\[
 P_H=I+\sum_e\ell_eu_eu_e^T,
 \qquad c_H=r^TP_H^{-1}r>0,
 \qquad \Omega=c_H^{-1}-(H-1).
\]

`[CONJECTURE L1 -- LORENTZ TRICHOTOMY]`  The core Cartan form is positive definite if
`Omega>0`, positive semidefinite of corank one if `Omega=0`, and has exactly one negative
eigenvalue if `Omega<0`.  In particular it never has two negative eigenvalues and never has
nullity greater than one.

`[CONJECTURE L2 -- ROOT-EXTENSION INVARIANCE]`  Extending the root by `t>0` sends

\[
 P_H\mapsto P_H+t rr^T,\quad H-1\mapsto H-1+t,\quad
 c_H\mapsto \frac{c_H}{1+t c_H},
\]

so `Omega` and `det(P_H)c_H` are independent of the artificial root extension.  Moreover

\[
 \det C=\det(P_H)c_H\Omega.                                           \tag{D}
\]

`[CONJECTURE L3 -- FULL-DIAGRAM LAW]`  Attach one type-A leg of length `l_i` to core vertex
`i`.  If `A_l` is the type-A Cartan matrix, block Gaussian elimination gives a positive leg
square plus the reduced core form

\[
 S=\operatorname{diag}\!\left(\frac1{l_i+1}\right)
   +\sum_e\ell_eu_eu_e^T-\lambda rr^T.                               \tag{F}
\]

Thus every full nonabelian Hodge Cartan matrix on the Riemann sphere obeys the same Lorentz
trichotomy.  For a graph this is equivalently the spectral law `lambda_2(B)<=2`.

`[CONJECTURE L4 -- DIMENSION CONSERVATION]`  Substitution of (F) into
`dim M_B=2-d^T C d` expresses the wild-character-variety dimension as one global rank-square
budget minus a sum of positive leg and fission-conormal defects.  This is an identity, not an
estimate.

## 3. Heavy falsification

### 3.1 Stronger positivity conjecture is false

`[FALSIFIED]`  “Every nonabelian Hodge core Cartan form is positive semidefinite.”  Doucot's
published twisted example has

\[
 B=\begin{pmatrix}2&4&12\\4&0&8\\12&8&6\end{pmatrix}.
\]

For `x=(1,1,1)`, one has `x^T(2I-B)x=-50<0`.  The surviving law must allow one negative
direction.

### 3.2 Two-negative-direction falsifier

One example of a realized irregular class whose `2I-B` is negative on a two-dimensional
subspace kills (L), (L1), and (L3).  No such example is known.  All published examples checked
so far are compatible with exactly one negative direction at most.

### 3.3 Typed-object falsifier

If the complementary-contact tree does not admit a single common root extension with
`H-K_ij` equal to common root-path length for every diagonal and pair, then the Gram step is
invalid.  This must be proved from the rooted contact realization, not inferred from weak
ultrametricity by pictures.

### 3.4 Leg falsifier

If full diagrams may attach a non-type-A or multiply coupled leg, formula (F) does not follow.
The geometric application must quote the exact diagram definition and restrict the theorem if
necessary.

## 4. Proof spine

1. Rooted-tree telescoping gives
   `K_ij=H-sum_e ell_e 1_Ae(i)1_Ae(j)`.
2. The definitions of diagonal and off-diagonal contact combine without cases as
   `B_ij=delta_ij+r_i r_j(K_ij-1)`.
3. Substitution proves (L) entrywise and (Q) by polarization.
4. `P_H` is positive definite.  On the hyperplane `r^T x=0`, (Q) reduces to
   `x^T P_H x>0`; hence at most one nonpositive direction.
5. Decompose uniquely `x=z+aP_H^{-1}r` with `r^Tz=0`.  Then
   `x^TCx=z^TP_Hz+a^2 c_H^2 Omega`, proving the trichotomy and affine kernel.
6. Apply the matrix determinant lemma and Sherman--Morrison formula to prove (D) and root
   invariance.
7. For a leg of length `l`, solve `A_l z=e_1` to obtain
   `(A_l^{-1})_11=l/(l+1)`.  Complete the square for all legs and prove (F).
8. Use Fourier--Laplace invariance of the diagram and the generic one-pole reading to pass from
   local infinity data to arbitrary global meromorphic connections on the Riemann sphere.

## 5. Prior-art boundary

- Doucot (2021) defines global diagrams, proves Fourier/symplectic invariance, and proves
  `dim M_B=2-(d,d)` for `C=2I-B`.  No signature theorem was found there.
- Doucot (2025) proves rescaled ultrametric and loop-edge inequalities.  No eigenvalue,
  determinant, capacity, or Lorentzian consequence was found there.
- Boalch (2025) counts fission trees/graphs and identifies their Kac--Moody role.  No Cartan
  signature theorem was found there.
- Martinez--Michon--San Martin, Nabben--Varga, and McDonald--Neumann--Schneider--Tsatsomeros
  prove positivity/inverse-M-matrix theorems for (generalized) ultrametric matrices.  Their
  linear algebra is parent theory.  Novelty, if it survives, is the exact Stokes--Cartan
  one-defect factorization, its full-diagram extension, and the universal signature/dimension
  consequences in irregular nonabelian Hodge geometry.
- Existing repository contact tomography and energy-tree results are prior inputs.  They did
  not state `C=P-lambda rr^T`, the Lorentz trichotomy, capacity invariant, full-leg law, or
  adjacency second-eigenvalue obstruction.

## 6. Stage gates

- [x] Universal hard conjecture stated
- [x] Stronger false conjecture killed by a published example
- [x] Exact falsifiers recorded
- [x] Local algebraic proof spine identified
- [x] Verify full-leg scope in primary diagram sources
- [x] Complete external signature/ultrametric-matrix novelty audit
- [x] Write dependency-closed paper proof
- [x] Move to Stage 2 before any Lean implementation
- [x] Formalize exact one-defect identity and `sigNeg <= 1`
- [x] Formalize capacity determinant wall and `sigNeg = 1` in the Lorentz phase
- [x] Formalize arbitrary type-A leg completion and dimension conservation
- [x] Formalize corona parallel completion and root-extension invariance
- [x] Wire all new modules into the `HTGeometry` umbrella

## 7. Dependency-closed paper proof

### 7.1 Tree Gram lemma

Let `T` be a finite rooted tree with labelled leaves `N` and a strictly decreasing potential
`Kappa` from root to leaves.  Extend the root, if necessary, to a new root of height
`H>max(1,Kappa)`.  Orient every edge away from the root.  For an edge `e`, let `A_e` be the
set of descendant leaves and let `ell_e>0` be the potential drop along `e`.

For leaves `i,j`, an edge belongs to both root--leaf paths exactly when both leaves lie in
`A_e`.  Their common root path ends at their meet.  Therefore

\[
 H-\Kappa(i\wedge j)
 =\sum_e\ell_e\mathbf 1_{A_e}(i)\mathbf 1_{A_e}(j).           \tag{7.1}
\]

If `Q_ij=H-Kappa(i meet j)`, (7.1) gives the Gram decomposition

\[
 Q=\sum_e\ell_e a_ea_e^T,
 \qquad a_e=(\mathbf 1_{A_e}(i))_i.                           \tag{7.2}
\]

Thus `Q` is positive semidefinite.  No appeal to a drawing or to pairwise independent
witnesses occurs: (7.1) is simultaneous on the single rooted tree.

### 7.2 Core one-defect identity

For a decorated Stokes core, established contact tomography identifies
`K_ij=Kappa(i meet j)`.  The diagonal and off-diagonal definitions combine into the single
entrywise identity

\[
 B_{ij}=\delta_{ij}+r_ir_j(K_{ij}-1).                         \tag{7.3}
\]

Indeed, for `i ne j` this is the definition of `K_ij`, while for `i=j` it reads
`B_ii=1+r_i^2(K_ii-1)`, which is the diagonal definition.  Since `C=2I-B`, equations
(7.1)--(7.3) imply

\[
\begin{aligned}
 C_{ij}
 &=\delta_{ij}+r_ir_j(1-K_{ij})\\
 &=\delta_{ij}+\sum_e\ell_e
   \bigl(r_i\mathbf1_{A_e}(i)\bigr)
   \bigl(r_j\mathbf1_{A_e}(j)\bigr)
   -(H-1)r_ir_j.
\end{aligned}
\]

This proves (L) entrywise.  Multiplication by `x_i x_j` and summation proves (Q).  In
particular, on the ramified-rank-zero hyperplane

\[
 \mathcal H_r=\{x:r^Tx=0\}
\]

one has

\[
 x^TCx=\sum_i x_i^2+\sum_e\ell_e(u_e^Tx)^2>0
 \quad(0\ne x\in\mathcal H_r).                               \tag{7.4}
\]

Thus `C` is positive definite on a canonical codimension-one hyperplane before any capacity
calculation.

### 7.3 One-scalar inertia theorem

Set

\[
 P=P_H=I+\sum_e\ell_eu_eu_e^T,
 \qquad \lambda=H-1,
 \qquad c=r^TP^{-1}r.
\]

The matrix `P` is positive definite and `c>0`.  Every `x` has a unique decomposition

\[
 x=z+aP^{-1}r,
 \qquad r^Tz=0,
 \qquad a=\frac{r^Tx}{c}.                                    \tag{7.5}
\]

The cross term vanishes because `z^TP(P^{-1}r)=z^Tr=0`.  Hence

\[
\begin{aligned}
 x^TCx
 &=x^T(P-\lambda rr^T)x\\
 &=z^TPz+a^2c-\lambda a^2c^2\\
 &=z^TPz+a^2c^2\bigl(c^{-1}-\lambda\bigr).                   \tag{7.6}
\end{aligned}
\]

Writing `Omega=c^{-1}-lambda`, (7.6) proves all three cases:

- `Omega>0`: `C` is positive definite;
- `Omega=0`: `C` is positive semidefinite with kernel
  `R P^{-1}r` and therefore has corank one;
- `Omega<0`: the first summand is positive on a codimension-one space and the second is
  negative on `R P^{-1}r`, so `C` has exactly one negative eigenvalue and is nonsingular.

In particular the total number of nonpositive eigenvalues is at most one.

### 7.4 Determinant and root-extension invariance

The matrix determinant lemma gives

\[
 \det C=\det(P)\bigl(1-\lambda r^TP^{-1}r\bigr)
       =\det(P)c\Omega.                                      \tag{7.7}
\]

Extend the artificial root by length `t>0`.  Its descendant set is all of `N`, so

\[
 P_t=P+t rr^T,\qquad \lambda_t=\lambda+t.                    \tag{7.8}
\]

Sherman--Morrison (whose denominator is positive) yields

\[
 c_t=r^TP_t^{-1}r=\frac{c}{1+tc}.                            \tag{7.9}
\]

Consequently

\[
 c_t^{-1}-\lambda_t=c^{-1}+t-(\lambda+t)=\Omega.             \tag{7.10}
\]

Also `det(P_t)=det(P)(1+tc)`, so

\[
 \det(P_t)c_t=\det(P)c.                                     \tag{7.11}
\]

Equations (7.10)--(7.11) prove that both factors in (7.7) are independent of the arbitrary
root extension.  Notice also directly from (7.8) that
`P_t-lambda_t rr^T=P-lambda rr^T=C`.

### 7.5 Type-A leg elimination

Let `A_l` be the `l x l` type-A Cartan matrix, with diagonal entries two and adjacent entries
minus one.  For `l>=1`, solve `A_l v=e_1`.  The unique solution is

\[
 v_k=\frac{l+1-k}{l+1},\qquad 1\le k\le l,
\]

as is checked by the second-difference equation, the first equation `2v_1-v_2=1`, and the
last equation `2v_l-v_{l-1}=0`.  Therefore

\[
 (A_l^{-1})_{11}=\frac{l}{l+1}.                              \tag{7.12}
\]

The matrix `A_l` is positive definite: its leading principal minors obey
`Delta_0=1`, `Delta_1=2`, and `Delta_l=2Delta_(l-1)-Delta_(l-2)`, so
`Delta_l=l+1>0`; Sylvester's criterion applies.

Attach a leg of length `l_i` to each core vertex `i`.  Put
`L=direct sum_i A_(l_i)` and let `E` send the core coordinate `x_i` to the first coordinate
of its leg (with the zero map when `l_i=0`).  The full Cartan form is

\[
 \widehat C=\begin{pmatrix}C&-E^T\\-E&L\end{pmatrix}.          \tag{7.13}
\]

For core variables `x` and leg variables `y`, completing the square gives

\[
\begin{aligned}
 \binom{x}{y}^{T}\widehat C\binom{x}{y}
 &=(y-L^{-1}Ex)^TL(y-L^{-1}Ex)\\
 &\quad+x^T(C-E^TL^{-1}E)x.                                 \tag{7.14}
\end{aligned}
\]

By (7.12),

\[
 E^TL^{-1}E=\operatorname{diag}\left(\frac{l_i}{l_i+1}\right).
\]

Combining this with (L), the Schur complement is

\[
 S=D+\sum_e\ell_eu_eu_e^T-\lambda rr^T,
 \qquad D=\operatorname{diag}\left(\frac1{l_i+1}\right)>0.  \tag{7.15}
\]

Replace `I` by `D` in Sections 7.3--7.4.  Every proof is unchanged because
`P=D+sum_e ell_e u_eu_e^T` remains positive definite.  Congruence (7.14) adds only the
positive leg block `L`.  Therefore the full Cartan matrix has the same trichotomy: positive
definite, positive semidefinite of corank one, or exactly one negative eigenvalue.  Its nullity
is never greater than one, and a negative and a zero eigenvalue cannot coexist.

### 7.6 Universal dimension conservation

Expand (7.14)--(7.15).  With

\[
 M=r^Tx=\sum_i r_ix_i,
 \qquad \nu_e(x)=u_e^Tx=\sum_{i\in A_e}r_ix_i,
\]

one obtains the exact identity

\[
\begin{aligned}
 \widehat q(x,y)
 &=\|y-L^{-1}Ex\|_L^2
 +\sum_i\frac{x_i^2}{l_i+1}
 +\sum_e\ell_e\nu_e(x)^2
 -(H-1)M^2.                                                  \tag{7.16}
\end{aligned}
\]

For an actual core dimension vector, `M` is total ramified rank.  The functionals `nu_e`
are the principal conormals of the cluster hyperplanes `nu_e=0`; their supports form the
laminar family of fission cuts.  Thus (7.16) is a precise conormal statement: the positive
local defect is the weighted squared norm of all principal cluster conormals, and the only
negative channel is total rank.  No characteristic-cycle or vanishing-cycle multiplicity is
asserted here.

The established dimension formula for a genus-zero wild character variety is

\[
 \dim\mathcal M_B=2-\widehat q(d).
\]

Substitution of (7.16) gives

\[
\boxed{
 \dim\mathcal M_B
 =2+(H-1)M^2
 -\|y-L^{-1}Ex\|_L^2
 -\sum_i\frac{x_i^2}{l_i+1}
 -\sum_e\ell_e\nu_e(x)^2.}                                 \tag{7.17}
\]

This proves L4 as an equality.  It is independent of root extension because extending the
root adds `t M^2` to both the positive cut sum and the displayed global term.

### 7.7 Passage to arbitrary genus-zero diagrams

The global diagram theorem for algebraic connections on a Zariski-open subset of the affine
line constructs `Gamma(E,nabla)` and proves it invariant under the relevant symplectic
`SL_2(C)` action, including Fourier--Laplace transform.  A generic transformation produces a
reading whose modified formal data are supported at infinity, without changing the diagram.
Its core is therefore the core of one finite irregular class at infinity, to which Sections
7.1--7.4 apply.  The full diagram is obtained by gluing to each core node the type-A leg
determined by its conjugacy class, so Section 7.5 applies.  This proves L--L4 for every
type-A genus-zero nonabelian Hodge diagram, not merely for a selected local normal form.

### 7.8 Graph-spectral corollary

If the full diagram is a graph with adjacency matrix `B`, its Cartan matrix is `2I-B`.
The number of adjacency eigenvalues strictly greater than two equals the negative index of
`2I-B`, and the multiplicity of the adjacency eigenvalue two equals its nullity.  Section 7.5
therefore gives

\[
 \lambda_2(B)\le2,                                          \tag{7.18}
\]

with the sharper trichotomy:

- spectral radius `<2`: finite/positive phase;
- spectral radius `=2`: affine phase, with eigenvalue two simple;
- spectral radius `>2`: Lorentz phase, with exactly one eigenvalue above two and no eigenvalue
  equal to two.

Thus higher-signature Kac--Moody root systems cannot occur as genus-zero type-A nonabelian
Hodge graphs.

## 8. Proof audit

- No analytic existence theorem is inferred from matrix conditions.
- No pairwise witness is substituted for a simultaneous tree realization.
- Root extension is explicitly shown to cancel from the law.
- Twisted loops and negative edge multiplicities are allowed in the core identity.
- Graph terminology is used only for the nonnegative loopless specialization.
- Full-diagram claim uses only one ordinary type-A leg per core node, exactly the published
  diagram construction.
- Plane-branch and ultrametric-matrix results are cited as parent theory, not claimed new.
- The novel theorem surface is the global Stokes--Cartan factorization and its geometric,
  signature, capacity, full-leg, and dimension consequences.

## 9. Formalization record

New unconditional modules:

- `formal/GaloisForLFunctions/HTGeometry/StokesCartanLorentzCapacity.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesCartanTypeALegs.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesCartanCoronaCapacity.lean`

The formal surface proves the exact entry and quadratic identities, positivity of the Gram part,
strict positivity on the ramification-zero hyperplane, negative inertia at most one, the capacity
completion and determinant factorization, the affine null line, an explicit Lorentz negative
vector, exact negative inertia one below the wall, arbitrary type-A leg completion, full-leg
hyperplane positivity, wild-dimension conservation, the finite parallel/corona completion law,
and scalar root-extension invariance.  All principal capstones have only `propext`,
`Classical.choice`, and `Quot.sound` in `#print axioms`.  The authoritative formal lint passes.
