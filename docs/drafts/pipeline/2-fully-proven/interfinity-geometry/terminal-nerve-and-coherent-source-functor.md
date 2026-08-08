# Terminal nerve and coherent source functor

- **ID:** `terminal-nerve-and-coherent-source-functor`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md` · Theorems
  XIII, XIV, XVI
- **Statement:** Coherent boundary formation is equivalent to a forward-stable one-particle
  primitive; joint source synchronizations form a Gram-labelled persistent simplicial set with
  nonfillable horns and a gauge-invariant cyclic phase satisfying a Bianchi identity.

## Goal

Separate individual endpoint existence from joint representability.  Retain the actual limiting
Gram chart so pairwise limits cannot be silently assembled from incompatible source subnets.

## Gates

- [x] 0 → 1 in-progress: common-clock rule and Gram labels fixed
- [x] 1 → 2 fully-proven: complete paper proof and explicit horn below
- [ ] 2 → 3 formalized: no Lean work authorized in source task
- [ ] 3 → 4 publication-ready: package priority review remains at program level

## Part I: coherent source functor

Let `Phi -> H -> Phi'` be a complex test--Hilbert--dual triple, with `Phi` Frechet and `Phi'`
weak-star.  Let `T_V` act continuously on `Phi'`, preserve `H`, and satisfy `T_Vh->0` in `H` for
every `h`.  Let `b_V in H` be a semigroup cocycle which is a coboundary in `Phi'`.  Define

\[
 \psi_V=e^{-\lVert b_V\rVert^2/2}\epsilon(b_V),
 \qquad
 \widetilde\psi_V
 ={\psi_V\over\langle\Omega,\psi_V\rangle}
 =\epsilon(b_V).
\tag{1}
\]

A coherent boundary is a functional `S_infinity(f)=exp(L(f))`, `L in Phi'`, such that

\[
 S_V(f)=\langle\epsilon(f),\widetilde\psi_V\rangle
 =e^{\langle f,b_V\rangle}
\tag{2}
\]

converges locally uniformly on every finite-dimensional complex subspace of `Phi`.

### Theorem A

The following are equivalent:

1. `b_V=(T_V-I)eta` for a primitive `eta in Phi'` with `T_Veta->0`;
2. `b_V` converges weak-star in `Phi'`;
3. `(2)` has a coherent boundary.

When they hold,

\[
 \eta=-\lim_Vb_V,
 \qquad
 S_\infty(f)=e^{-\eta(f)}.
\tag{3}
\]

#### Proof

Stable exactness gives `b_V->-eta`.  Conversely, if `b_V->ell`, the cocycle identity gives, for
fixed `W`,

\[
 \ell=b_W+T_W\ell.
\]

Thus `eta=-ell` is a primitive and `T_Veta=b_V+eta->0`.  This proves `1 iff 2` and `(3)`.

Weak-star convergence gives uniform convergence of the linear forms on compact subsets of every
finite-dimensional subspace, hence convergence of their exponentials.  Conversely, on the line
`t f`, local uniform convergence of the holomorphic functions
`exp(t <f,b_V>)` permits differentiation at zero, giving `<f,b_V>->L(f)`.  Thus `2 iff 3`. `QED`

## Part II: Gram-labelled terminal nerve

Let `A` be a set of source experiments.  At observer `o`, experiment `a` has a source-time cocycle
`b^a` and clocked normalized vector `v_i^a`.  Define `N_o[k]` to consist of an ordered tuple
`(a_0,...,a_k)` together with a specified Hermitian matrix `G=(g_rs)` such that:

1. every `b^(a_r)` has a stable primitive at `o`; and
2. one allowed common source synchronization makes the entire Gram matrix

   \[
   (\langle v_i^{a_r},v_i^{a_s}\rangle)_{r,s}
   \longrightarrow G.
   \tag{4}
   \]

Faces delete a label and its row and column; degeneracies repeat them.  For a joint triangle with
all three overlaps nonzero, define

\[
 \Omega(a,c,d)
 ={g_{ac}g_{cd}g_{da}\over|g_{ac}g_{cd}g_{da}|}.
\tag{5}
\]

### Theorem B

1. Every `N_o` is a simplicial set.
2. If observer strengthening preserves stable primitives, vectors, and common clocks, then
   `N_o -> N_o'` is simplicial.  Hence `N` is a persistence object.
3. The death region `D(sigma)={o:sigma in N_o[k]}` is upward closed and satisfies
   `D(sigma) subset D(tau)` for every face `tau`.  On a calibrated numerical observer line,
   `d(tau)<=d(sigma)` for the corresponding infimum cuts.
4. `Omega` is invariant under independent vertex phase gauges and obeys

   \[
   \Omega(1,2,3)\Omega(0,2,3)^{-1}
   \Omega(0,1,3)\Omega(0,1,2)^{-1}=1
   \tag{6}
   \]

   wherever all six edge overlaps are nonzero.
5. Pairwise terminal Gram charts need not fill a two-dimensional horn, even when their proposed
   full Gram matrix is strictly positive definite.
6. More strongly, stable-exactness topology together with the entire Gram-labelled one-skeleton
   does not determine `N[2]`.

#### Proof

Deleting or repeating rows and columns in `(4)` uses the same synchronization and obeys the usual
simplicial identities.  Observer strengthening carries a common realization forward.  Both
claims prove items 1 and 2.  The same facts show upward closure; a realization of a simplex realizes
every principal face, proving item 3.

For item 4, put `u_ac=g_ac/|g_ac|`.  Then `u_ca=u_ac^(-1)` and
`Omega(a,c,d)=u_ac u_cd u_da`.  Vertex phase gauges cancel in each cyclic product.  Expanding the
four factors in `(6)` cancels every oriented edge phase with its inverse.

For item 5, let `I=N`, `H=C^3`, and `e_1,e_2,e_3` be orthonormal.  Put `A_n=e_1`.  At even `n`,
put

\[
 B_n={1\over2}e_1+{\sqrt3\over2}e_2,
 \qquad C_n=e_3,
\]

and at odd `n` interchange these two displayed vectors.  Then `BC` overlap is always zero, while
`AB=1/2` occurs exactly on even indices and `AC=1/2` exactly on odd indices.  The proposed matrix

\[
 G=\begin{pmatrix}1&1/2&1/2\\1/2&1&0\\1/2&0&1\end{pmatrix}
\]

has determinant `1/2>0`.  Each specified edge is realized on a cofinal synchronization.  Any
subnet on which `AB->1/2` is eventually even, and any subnet on which `AC->1/2` is eventually odd;
no common subnet realizes both.  Therefore the two-edge horn has no filler.

For item 6, call the preceding parity system `X`.  Its possible edge limits are exactly
`g_AB in {0,1/2}`, `g_AC in {0,1/2}`, and `g_BC=0`.  Construct `Y` with three periodic states.
On `n=1 mod 3` use the even state of `X`; on `n=2 mod 3` use its odd state; and on `n=0 mod 3`
use `B_n=(1/2)e_1+(sqrt(3)/2)e_2` and

\[
 C_n={1\over2}e_1-{1\over2\sqrt3}e_2+\sqrt{2\over3}e_3.
\]

The last state has Gram matrix `G` displayed above.  Both systems have zero cocycles, hence the
same stable-exactness topology.  Their complete labelled edge sets agree, because the three-periodic
system introduces no edge value beyond `0,1/2`.  But only `Y` realizes the `G`-labelled triangle.
Thus their one-skeleta agree and their two-simplices differ. `QED`

## Covariance

A source-clock equivalence which is a topological isomorphism on test duals and unitary on clocked
Hilbert vectors induces isomorphisms of stable-primitive groups and of the Gram-labelled nerves.
It preserves fixed residue rays and `(5)`.  Numerical widths require preservation of the chosen
observer calibration; order-theoretic death regions do not.

## Lean handoff notes

Formalize Part II first: finite matrices, face/degeneracy operations, parity horn, and phase
cancellation are finite algebra.  Part I needs exponential-vector inner products and a theorem
that locally uniform convergence of holomorphic functions preserves the derivative at zero.

## Boundary

Bosonic coherent vectors, simplicial sets, persistence, Gram matrices, and Bargmann phases are
parents.  Candidate-new content is the gluing rule: vertices are stable-exactness deaths and a
higher simplex requires one source synchronization carrying its specified Gram data.
