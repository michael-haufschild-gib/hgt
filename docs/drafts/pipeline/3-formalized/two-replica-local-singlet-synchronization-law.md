# Two-replica local-singlet synchronization law

- **Stage:** 3 — formalized in Lean 4
- **Status:** `[FORMALIZED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4 planar replica cavity
- **Lean:** `HTGeometry/TwoReplicaLocalSingletSynchronization.lean`

## Exact statement

Let `sigma_1,sigma_2,sigma_3` be the Pauli matrices, normalized by

\[
 \operatorname{Tr}(\sigma_a\sigma_b)=2\delta_{ab}.
\]

At one physical qubit, regard the two-replica operator space
`HS(C^2) tensor HS(C^2)` as the Hilbert--Schmidt operators on
`C^2 tensor C^2`. Put

\[
 A=\sum_{a=1}^3\sigma_a\otimes\sigma_a,
 \qquad
 u={I\otimes I\over2},
 \qquad
 z={A\over2\sqrt3},
 \qquad
 f={u+\sqrt3z\over2}.
\tag{1}
\]

Then `u,z` are orthonormal and `f=F/2`, where `F` swaps the two
replicas.  The local diagonal-`SU(2)` invariant space is

\[
                         L=\operatorname{span}\{u,z\}.
\tag{2}
\]

For two physical sites `i,j`, put

\[
 R_{ab}=\sigma_a^{(i)}\sigma_b^{(j)},\qquad
 G_{ab}=R_{ab}^{(1)}+R_{ab}^{(2)},\qquad
 B_{ab}=\operatorname{ad}_{G_{ab}},
\]

and define the two-site collective commutator Casimir

\[
                         K_{ij}=\sum_{a,b=1}^3 B_{ab}^2.
\tag{3}
\]

On `L_i tensor L_j`, in the orthonormal ordered basis
`u_i u_j,u_i z_j,z_i u_j,z_i z_j`, its matrix is

\[
 K_{ij}=
 \begin{pmatrix}
 0&0&0&0\\
 0&48&0&-16\sqrt3\\
 0&0&48&-16\sqrt3\\
 0&-16\sqrt3&-16\sqrt3&32
 \end{pmatrix}.
\tag{4}
\]

Consequently

\[
 \operatorname{Spec}(K_{ij}|_{L_i\otimes L_j})
     =\{0,0,48,80\},
 \qquad
 \ker K_{ij}
     =\operatorname{span}\{u_i\otimes u_j,
                            f_i\otimes f_j\}.
\tag{5}
\]

Equivalently, a two-site Pauli block annihilates precisely the two local
replica choices “swap neither endpoint” and “swap both endpoints”; every
local-swap mismatch costs at least `48` in the Casimir quadratic form.

Let `G=(V,E)` be any finite connected graph and let

\[
 L_V=\bigotimes_{i\in V}L_i,
 \qquad \widehat K_{ij}=K_{ij}\otimes I_{V\setminus\{i,j\}}
 \quad\hbox{on }L_V.
\tag{6}
\]

In the Hilbert coefficient realization of the physical identity/swap tensor
basis, form the finite positive master constraint

\[
 \mathfrak M_G=\sum_{(i,j):\,\{i,j\}\in E}
          \widehat K_{ij}^{\dagger}\widehat K_{ij}.
\tag{6a}
\]

The ordered-pair convention only duplicates positive summands.

Then

\[
 \boxed{
 \ker\mathfrak M_G
   =\operatorname{span}\left\{
       \bigotimes_{i\in V}u_i,
       \bigotimes_{i\in V}f_i
     \right\}.
 }
\tag{7}
\]

These are exactly the identity and global two-replica swap modes.  Thus
connected two-site interactions synchronize the entire `2^|V|`-dimensional
one-site singlet algebra down to the two global permutation modes.

## Proof

All Hilbert--Schmidt inner products below are unnormalized traces.  The swap
identity

\[
             F={1\over2}\left(I\otimes I+A\right)
\tag{8}
\]

gives `Tr A=0` and `Tr A^2=12`.  Hence `u,z` are orthonormal and (1) gives
`f=F/2`.  Schur--Weyl duality for two copies of the defining `SU(2)`
representation gives (2); this also follows directly because `I` and `F`
span the commutant.

For a local two-replica operator `X`, define

\[
 D(X)=\sum_a\sigma_a^{(1)}X\sigma_a^{(1)},
 \qquad
 C(X)=\sum_a\sigma_a^{(1)}X\sigma_a^{(2)}.
\tag{9}
\]

Pauli conjugation and (8) give the four exact identities

\[
 D(I)=3I,\qquad D(A)=-A,
 \qquad C(I)=A,\qquad C(A)=3I+2A.
\tag{10}
\]

For the last one,

\[
 \sum_a\sigma_a^{(1)}A\sigma_a^{(2)}
 =2\sum_a\sigma_a^{(1)}F\sigma_a^{(2)}-A
 =6F-A=3I+2A,
\]

using `(X tensor I)F=F(I tensor X)`.

Let `M_A` denote left multiplication by `A`.  Since
`A^2=3I-2A`, on `span{I,A}` the three maps satisfy

\[
\begin{array}{c|cc}
 &I&A\\ \hline
 D&3I&-A\\
 C&A&3I+2A\\
 M_A&A&3I-2A.
\end{array}
\tag{11}
\]

Now `G_{ab}^2=2I+2R_{ab}^{(1)}R_{ab}^{(2)}`.  Summing in `a,b`, using
that every vector in `L_i tensor L_j` commutes with `A_iA_j`, and expanding
the four terms in `G_{ab}XG_{ab}`, gives

\[
 K_{ij}|_{L_i\otimes L_j}
 =36I+4M_A\otimes M_A
      -4(D\otimes D+C\otimes C).
\tag{12}
\]

Substituting (11) into (12) and converting from `I,A` to the normalized
basis `u,z` yields (4).  The antisymmetric vector
`(u z-z u)/sqrt 2` has eigenvalue `48`.  On
`span{(u z+z u)/sqrt 2,z z}`, the remaining matrix is

\[
 \begin{pmatrix}48&-16\sqrt6\\-16\sqrt6&32\end{pmatrix},
\]

whose eigenvalues are `0,80`.  Together with the zero vector `u u`, this
proves the spectrum in (5).  Its second zero vector is `f f`, by (1), so the
kernel formula and the lower Casimir cost `48` follow.

Every term in (6a) is positive semidefinite and
`ker(C^\dagger C)=ker C`.  Therefore

\[
 \ker \mathfrak M_G
   =\bigcap_{\{i,j\}\in E}\ker \widehat K_{ij}.
\tag{13}
\]

For each site, the invertible linear map `S_i:C^2 -> L_i` defined by
`S_i|0>=u_i`, `S_i|1>=f_i` sends the edge kernel in (5) to
`span{|00>,|11>}`.  Write a vector in the transformed global space as

\[
                         \sum_{x\in\{0,1\}^{V}}c_x|x\rangle.
\]

Membership in the edge kernel for `{i,j}` forces `c_x=0` whenever
`x_i != x_j`.  Connectedness forces every surviving bit string to be
constant.  Hence only the all-zero and all-one strings remain.  Applying
`tensor_i S_i` proves (7).

## Hostile audit: what this does not prove

This theorem closes replica local-singlet synchronization at the exact
fixed-space and Casimir levels.  It does **not** by itself prove that the
matrix space spanned by the collective commutators is noncommutatively full.
Positive Casimir plus zero common kernel is insufficient.

Indeed, on `C^3` let

\[
 A_1=E_{13}+E_{31},\qquad A_2=E_{23}+E_{32}.
\]

Both are Hermitian and

\[
 A_1^2+A_2^2=\operatorname{diag}(1,1,2)>0,
 \qquad \ker A_1\cap\ker A_2=0.
\]

Nevertheless `span{e_1,e_2}` is sent by both matrices into `span{e_3}`.
It is a one-dimensional shrunk-subspace defect, so the associated completely
positive covariance is not rank non-decreasing.  Therefore neither (7), a
positive global Casimir gap, nor Lie generation authorizes the matrix-
semicircle fullness conclusion.

The exact remaining algebraic statement is the **Pauli Hall-expansion law**:
after quotienting the identity and global-swap modes, prove for every
subspace `U` that

\[
 \dim\operatorname{span}\{A_p^{(2)}U:\operatorname{wt}(p)\le2\}
 \ge \dim U.
\tag{14}
\]

Equation (14), not common-kernel synchronization, is equivalent to the
rank-nondecreasing condition needed by operator scaling and the matrix-
semicircle theorem.  The full Pauli multiplets and their nine-dimensional
edge output are extra structure absent from the star counterexample; the
next proof must use that expansion quantitatively.

## Novelty boundary

The two-copy invariant-space interpretation and frustration-free moment-
Hamiltonian mechanism have established representation-theoretic parents.
No novelty is claimed here.  Value is exact removal of a false implication
inside the static-Hamiltonian growth route and reduction of the first replica
obstruction to the sharply stronger Hall law (14).

## Formalization status — 2026-08-04

Exact formalization is verified in
`HTGeometry/TwoReplicaLocalSingletSynchronization.lean` and wired into the
`HTGeometry` umbrella.  The module proves:

- the exact nine-generator physical double-commutator Casimir;
- its four raw invariant-space actions and faithful coefficient
  intertwining;
- the invariant eigenbasis with eigenvalues `0, 0, 48, 80`;
- the physical local kernel classification after an injective
  Hilbert--Schmidt Gram embedding, with Gram diagonal
  `16, 48, 48, 144`;
- the physical identity/swap change of coordinates and exact intertwining of
  its coefficient action with the nine-generator double commutator;
- the tensor edge action, whose kernel is exactly vanishing of every
  mismatched endpoint coefficient;
- preconnected-graph coefficient synchronization: edge-mismatch vanishing is
  equivalent to support on the all-identity and all-swap configurations;
- the finite Hilbert master constraint and its exact physical-state kernel:
  on every finite nonempty preconnected graph only the all-identity and
  all-swap coefficient vectors survive.

The complete module passes `lake env lean` without warnings.  Axiom audits of
`twoReplicaEdgeCasimir_intertwines_swapCoeff`,
`twoReplicaGlobalEdgeCasimirCoeff_eq_zero_iff`, and
`physicalState_twoReplicaGraphMasterConstraint_iff` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  No Hall-expansion claim is implied by
this synchronization theorem.
