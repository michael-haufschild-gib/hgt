# Complete atomic Fourier--Hankel order and inertia fusion law

- **ID:** ULF-CTCM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / THREE-ORGAN FUSION / FOURTH-ORGAN PREDICTION
- **Statement:** For finitely many distinct real source atoms with Hermitian matrix interventions,
  full Fourier packets, the order-`N` block Hankel packet, and atomwise matrix order reconstruct one
  another; their compensation gauges and inertia triples are identical.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [FINITE COMMUTATIVE SOURCE]
  [JOINT RECONSTRUCTION] [EXACT GAUGE CONSERVATION] [EXACT INERTIA CONSERVATION]
  [NONCOMMUTATIVE BOUNDARY EXPLICIT] [FINITE FUSION CORE LEAN-CERTIFIED]
  [EXACT INERTIA COUNT LEAN OPEN] [NOT RH]

## 1. Setup

Let `X={1,...,N}` with `N>=1`.  Let

\[
  \lambda_x\in\mathbb R\qquad(x\in X)
\]

be pairwise distinct.  Fix a channel dimension `d>=1`.  For each `x`, let `W_x,H_x` be Hermitian
`d x d` matrices and assume `W_x` is positive definite.  For `c in R`, put

\[
  A_x(c)=cW_x-H_x.
\tag{CFH.1}
\]

The `H_x` are one generated matrix-valued intervention.  The `W_x` are its positive source
calibration.

Define moments

\[
  M_r(c)=\sum_{x\in X}\lambda_x^rA_x(c),
\tag{CFH.2}
\]

and the order-`N` block Hankel matrix

\[
  \mathcal H_N(c)_{(i,a),(j,b)}=M_{i+j}(c)_{ab},
  \qquad 0\le i,j<N.
\tag{CFH.3}
\]

Choose `tau != 0` so that

\[
 z_x=e^{-i\tau\lambda_x}
\tag{CFH.4}
\]

are pairwise distinct.  Such a `tau` exists: take it small enough that
`|tau(lambda_x-lambda_y)|<2pi` for every pair.  Define the complete finite Fourier block

\[
  \mathcal F_{N,\tau}(c)_{(i,a),(j,b)}
  =\sum_{x\in X}\overline{z_x^i}z_x^jA_x(c)_{ab}.
\tag{CFH.5}
\]

Finally define three positive-compensation gauges:

\[
\begin{aligned}
 \kappa_{\rm at}&=\inf\{c\ge0:A_x(c)\succeq0\ \forall x\},\\
 \kappa_{\rm H}&=\inf\{c\ge0:\mathcal H_N(c)\succeq0\},\\
 \kappa_{\rm F}&=\inf\{c\ge0:\mathcal F_{N,\tau}(c)\succeq0\}.
\end{aligned}
\tag{CFH.6}
\]

All three feasible sets are nonempty because there are finitely many positive-definite `W_x`.

## 2. Two exact quadratic fusion identities

For a channel-valued polynomial

\[
  p_v(t)=\sum_{j=0}^{N-1}t^jv_j,
  \qquad v_j\in\mathbb C^d,
\tag{CFH.7}
\]

one has

\[
 \boxed{
 v^*\mathcal H_N(c)v
 =\sum_{x\in X}p_v(\lambda_x)^*A_x(c)p_v(\lambda_x).}
\tag{CFH.8}
\]

For the Fourier polynomial

\[
  q_v(z)=\sum_{j=0}^{N-1}z^jv_j,
\tag{CFH.9}
\]

one has

\[
 \boxed{
 v^*\mathcal F_{N,\tau}(c)v
 =\sum_{x\in X}q_v(z_x)^*A_x(c)q_v(z_x).}
\tag{CFH.10}
\]

### Proof

Insert `(CFH.2)` into `(CFH.3)`, interchange finite sums, and factor the two polynomial sums.  The
same calculation with `(CFH.5)` factors the Fourier powers.  No positivity is used.  QED.

## 3. Joint reconstruction and complete order reflection

### Theorem 3.1

For every real `c`, the following are equivalent:

\[
\boxed{
 A_x(c)\succeq0\ \forall x
 \quad\Longleftrightarrow\quad
 \mathcal H_N(c)\succeq0
 \quad\Longleftrightarrow\quad
 \mathcal F_{N,\tau}(c)\succeq0.}
\tag{CFH.11}
\]

Moreover, either the full block Hankel response or the selected Fourier block reconstructs every
matrix `A_x(c)` and hence every intervention matrix `H_x`.

### Proof

If every `A_x(c)` is positive semidefinite, `(CFH.8)` and `(CFH.10)` make both fused quadratic forms
nonnegative.

Conversely, let `ell_x` be the Lagrange polynomial of degree less than `N` satisfying

\[
  \ell_x(\lambda_y)=\delta_{xy}.
\]

For arbitrary `u in C^d`, substitute the vector-valued polynomial `p(t)=ell_x(t)u` into
`(CFH.8)`.  Hankel positivity gives

\[
  u^*A_x(c)u\ge0.
\]

Thus each atom matrix is positive semidefinite.

The same argument applies to `(CFH.10)` because the scalar Vandermonde matrix

\[
  (z_x^j)_{x,j=0}^{N-1}
\]

is invertible.  Equivalently, there are Fourier interpolation polynomials `m_x` with
`m_x(z_y)=delta_xy`; use `q(z)=m_x(z)u`.

These substitutions give every atom quadratic form.  Complex polarization reconstructs every
matrix entry.  Since `H_x=cW_x-A_x(c)` and `W_x` is marked, either fused response reconstructs
`H_x`.  QED.

### Corollary 3.2 — exact gauge conservation

\[
 \boxed{\kappa_{\rm at}=\kappa_{\rm H}=\kappa_{\rm F}.}
\tag{CFH.12}
\]

### Proof

Theorem 3.1 says the three feasible subsets of `[0,infinity)` are identical, not merely that their
infima agree.  QED.

This is the conservation identity required by the field programme.

## 4. Matrix amplification collapses in this chamber

Let `C^X` be the finite commutative source algebra and define

\[
  \Phi_c(f)=\sum_x f(x)A_x(c).
\tag{CFH.13}
\]

### Theorem 4.1

The following are equivalent:

1. `Phi_c` is positive;
2. every `A_x(c)` is positive semidefinite;
3. `Phi_c` is completely positive;
4. either fused matrix in `(CFH.11)` is positive semidefinite.

### Proof

Positivity applied to the minimal projection `1_{x}` gives `A_x(c)>=0`.  Conversely, positive
linear combinations of the atom matrices are positive.  If the atoms are positive, then at matrix
level `k`,

\[
  (\operatorname{id}_{M_k}\otimes\Phi_c)([f_{ij}])
  =\sum_x [f_{ij}(x)]\otimes A_x(c),
\]

and every summand is positive.  Hence `Phi_c` is completely positive.  Complete positivity implies
positivity.  Theorem 3.1 supplies the fourth equivalence.  QED.

Thus amplification is not always an independent axis.  It becomes redundant when an invertible
test calculus resolves a finite commutative atom algebra.

## 5. Fourth-organ prediction: exact inertia conservation

For a Hermitian matrix `B`, write

\[
  \operatorname{In}(B)=(n_+(B),n_-(B),n_0(B))
\]

for its positive, negative, and null indices.

### Theorem 5.1

For every real `c`,

\[
 \boxed{
 \operatorname{In}(\mathcal H_N(c))
 =\operatorname{In}(\mathcal F_{N,\tau}(c))
 =\sum_{x\in X}\operatorname{In}(A_x(c)),}
\tag{CFH.14}
\]

where the sum is componentwise.

### Proof

Let `D(c)=directsum_x A_x(c)`.  Equations `(CFH.8)` and `(CFH.10)` are matrix congruences

\[
  \mathcal H_N(c)=(V_\lambda\otimes I_d)^*D(c)(V_\lambda\otimes I_d),
\]

\[
  \mathcal F_{N,\tau}(c)=(V_z\otimes I_d)^*D(c)(V_z\otimes I_d),
\tag{CFH.15}
\]

up to the harmless transpose convention determined by whether coefficient or evaluation vectors
are columns.  Both Vandermonde matrices are invertible.  Sylvester's law of inertia makes inertia
invariant under invertible congruence.  The inertia of a block direct sum is the componentwise sum
of block inertias.  QED.

### Prediction delivered

Existing passive matrix-density Hankel theory proves the forward statement “positive atom density
implies positive block Hankel matrices.”  The present theorem predicts and proves the withheld
finite-atomic converse and the stronger signed statement:

> At full interpolation depth, negative spectral channels cannot cancel between atoms.  The block
> Hankel negative-square count is exactly the sum of the atom negative-square counts.

This lies in the Krein/inertia organ and was not assumed in the Fourier or moment construction.

## 6. Sharp boundaries

1. **Insufficient depth.**  With fewer than `N` polynomial or Fourier coordinates, the evaluation
   map need not be onto; negative atom directions can be invisible.
2. **Repeated nodes.**  Distinctness is load-bearing.  Repeated nodes require confluent jets and a
   confluent Vandermonde theorem.
3. **Noncommutative source.**  A positive map out of `M_n` need not be completely positive.  The
   reduction pencil has exact level-`k` threshold `min(k,n)` and complete threshold `n`.
4. **Infinite support.**  No finite interpolation depth isolates every atom.  Tightness, closure,
   and uniform admission become independent.
5. **No source selection.**  The theorem reconstructs and localizes a supplied source tangent.  It
   does not construct the arithmetic tangent or prove it is positive.
6. **Inertia is not RH.**  An RH implication requires an independently built arithmetic
   realization identifying off-criticality with a negative atom channel before zero
   specialization.

## 7. Role in the five-step field programme

1. **Common grammar:** generated intervention, complete test closure, reconstruction, order
   reflection, cofinal admission.
2. **Three-organ fusion:** Fourier phase, block Hankel moment, and matrix complete order.
3. **Exact conservation:** `(CFH.12)` plus joint reconstruction.
4. **Fourth prediction:** exact Krein inertia additivity `(CFH.14)`.
5. **RH only afterward:** source realization and uniform cofinal positivity remain explicit gates.

## 8. Literature boundary

Finite matrix-valued Bochner theorems, Choi's theorem, block moment problems, Vandermonde
interpolation, Sylvester inertia, and positive maps on commutative C*-algebras are classical or
current parent mathematics.  Recent finite inverse-semigroup Fourier theory makes the
Bochner--Choi bridge explicit; locally compact quantum-group theory shows that scalar and complete
positive definiteness separate without coamenability-type hypotheses.  The result here is used as
one exact field mechanism, not as a priority claim for its ingredients.

## 9. Lean certification

The dependency-closed finite core is certified in

`GaloisForLFunctions.HTGeometry.CompleteTestClosureFusion`:

1. atomwise nonnegativity is equivalent to nonnegativity of every complete fused response;
2. the complete fused response reconstructs every atom quadratic;
3. compensation feasibility is invariant under every complete invertible test fusion;
4. existence of a strict negative atom witness is equivalent to a strict negative fused witness;
5. invertible matrix congruence preserves and reflects positive semidefiniteness;
6. pairwise-distinct real Vandermonde evaluation gives an invertible congruence and therefore exact
   finite Hankel order reflection.

The exact numerical inertia triple `(CFH.14)` remains paper-level because the present Lean surface
certifies noncancellation/existence of negative directions, not Sylvester inertia multiplicities.
Under the project epistemic rule, only the six clauses above currently count as truly proved.

## Log

- 2026-08-11 — paper proof closed after witness-bundle/properness pivot was found to duplicate RBD.
- 2026-08-11 — noncommutative amplification retained as a sharp counterchamber, not silently
  collapsed into scalar positivity.
