# Path-local centralizer tangent-rigidity law

- **ID:** `path-local-centralizer-tangent-rigidity-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / deterministic local-centralizer classification / Brown-frontier advance
- **Parent:** `centralizer-phase-bandwidth-shortcut-extraction-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-10

## Public sentence

For an open qubit chain with generic full-rank two-site couplings, time is the only nontrivial
two-local direction inside the Hamiltonian's moving centralizer: every other two-local Hermitian
operator commuting with the Hamiltonian is an affine function of the Hamiltonian itself.  The
remaining Brown-complexity obstruction is therefore genuinely finite and transverse; it cannot be
another hidden two-local conserved flow.

## Why this theorem is the next required layer

The phase-bandwidth theorem proves that every approximate shortcut to `exp(-itH)` contains a
nearby exact unitary in the moving spectral centralizer.  It also proves that a circuit constrained
to stay inside that centralizer must pay the intrinsic phase bandwidth.  The open loophole is an
ambient local circuit which leaves the centralizer and returns with a large spectral phase.

The first infinitesimal question is therefore exact:

> How many genuinely local Hamiltonian directions lie in the centralizer of a generic local
> Hamiltonian?

For the ordinary open-chain two-local Pauli shell, the answer is exactly one, modulo the scalar
identity.  The proof is local and constructive.  Three-body coefficients on consecutive edges
first synchronize every two-site coupling; one anisotropic edge then removes every residual
one-site field.

## Setup

Let `n>=3`.  At site `v`, write

\[
 \boldsymbol\sigma_v=(X_v,Y_v,Z_v).                                  \tag{1}
\]

The real Hermitian open-chain two-local shell is

\[
 \mathcal L_n=\left\{
 cI+\sum_{v=1}^n h_v\mathbin\cdot\boldsymbol\sigma_v
 +\sum_{v=1}^{n-1}\sum_{a,b=1}^3
       (J_v)_{ab}\sigma_v^a\sigma_{v+1}^b
 :c\in\mathbb R,\ h_v\in\mathbb R^3,\ J_v\in M_3(\mathbb R)
 \right\}.                                                           \tag{2}
\]

Fix `H in L_n`, with coefficients `c,h_v,J_v`, and assume

\[
 J_v\in GL_3(\mathbb R)\qquad(1\le v<n).                              \tag{3}
\]

For a coupling matrix `J`, define the local-field commutator map

\[
 \mathcal R_J(a,b)
 =\left[
   \sum_{p,q=1}^3J_{pq}\sigma^p\otimes\sigma^q,
   a\mathbin\cdot\boldsymbol\sigma\otimes I
    +I\otimes b\mathbin\cdot\boldsymbol\sigma
  \right].                                                            \tag{4}
\]

Call `J` **field rigid** when

\[
 \ker\mathcal R_J=\{(0,0)\}.                                        \tag{5}
\]

Assume at least one edge coupling `J_q` is field rigid.

## Lemma A -- the cross-product synchronization identity

Let `A,B:R^3->R^3` be linear.  If

\[
 x\times(By)=(Ax)\times y\qquad(x,y\in\mathbb R^3),                  \tag{6}
\]

then there is `lambda in R` such that

\[
 \boxed{A=B=\lambda I_3.}                                            \tag{7}
\]

### Proof

In coordinates, `(6)` is

\[
 \varepsilon_{k i q}B_{qj}
 =\varepsilon_{k p j}A_{pi}.                                        \tag{8}
\]

Contract `(8)` with `epsilon_(k i r)` and sum over `k,i`.  The standard contraction identity for
the Levi--Civita tensor gives

\[
 2B=(\operatorname{tr}A)I-A.                                        \tag{9}
\]

Contract instead with `epsilon_(k j r)` and sum over `k,j`; this gives

\[
 2A=(\operatorname{tr}B)I-B.                                       \tag{10}
\]

Taking traces in `(9)` shows `tr A=tr B=:T`.  Substitute `(9)` into `(10)`:

\[
 2A=TI-{TI-A\over2},
\]

so `3A=TI`.  Equation `(9)` then gives the same formula for `B`.  Put `lambda=T/3`. `square`

## Lemma B -- field-rigid couplings form an open dense set

If

\[
 J=\operatorname{diag}(d_1,d_2,d_3),\qquad
 d_i\ne0,\qquad d_i^2\ne d_j^2\ (i\ne j),                            \tag{11}
\]

then `J` is field rigid.  Consequently field rigidity is a nonempty Zariski-open, hence Euclidean
open dense, condition on `M_3(R)`.

### Proof

Let `R_J(a,b)=0`.  For an ordered pair `p!=q`, let `r` be the remaining coordinate.  The
coefficients of `sigma^p tensor sigma^q` and `sigma^q tensor sigma^p` give, up to one common
nonzero scalar and orientation sign,

\[
 d_q a_r-d_p b_r=0,\qquad
 -d_p a_r+d_q b_r=0.                                                 \tag{12}
\]

The determinant is `d_q^2-d_p^2`, so `(11)` forces `a_r=b_r=0`.  The three unordered coordinate
pairs give `a=b=0`.

In fixed Pauli bases, `(4)` is a `9 by 6` real matrix whose entries are linear in `J`.  Field
rigidity is rank six.  The diagonal witness makes at least one `6 by 6` minor nonzero.  Nonvanishing
of that minor is Zariski open and is contained in the field-rigid set; the rank-deficient set is the
common zero locus of all such minors. `square`

## Theorem C -- exact two-local centralizer classification

Under `(3)` and the existence of one field-rigid edge,

\[
 \boxed{
 \{K\in\mathcal L_n:[H,K]=0\}
 =\operatorname{span}_{\mathbb R}\{I,H\}.}                           \tag{13}
\]

Thus the non-scalar kernel of

\[
 \operatorname{ad}_H:\mathcal L_n\longrightarrow
 \operatorname{Herm}(2^n)                                          \tag{14}
\]

has dimension one.

### Proof

Write an arbitrary `K in L_n` as

\[
 K=dI+\sum_{v=1}^n k_v\mathbin\cdot\boldsymbol\sigma_v
 +\sum_{v=1}^{n-1}\sum_{a,b=1}^3
       (L_v)_{ab}\sigma_v^a\sigma_{v+1}^b.                           \tag{15}
\]

#### Step 1 -- consecutive-edge three-body coefficients

Fix `v` with `1<=v<=n-2`.  Only the pair of edges `(v,v+1)` and `(v+1,v+2)` contributes to Pauli
strings supported on exactly these three consecutive sites.  Vanishing of that part of `[H,K]`
is, for every row `x` of `J_v` and column `y` of `J_(v+1)`,

\[
 x\times \bigl(\text{corresponding column of }L_{v+1}\bigr)
 =\bigl(\text{corresponding row of }L_v\bigr)\times y.               \tag{16}
\]

Invertibility in `(3)` says the rows of `J_v` and columns of `J_(v+1)` are bases.  There are unique
linear maps `A_v,B_(v+1)` sending those bases to the corresponding rows and columns of `L_v` and
`L_(v+1)`.  Bilinearity extends `(16)` to every `x,y in R^3`.  Lemma A gives a scalar `lambda_v`
such that

\[
 L_v=\lambda_vJ_v,\qquad
 L_{v+1}=\lambda_vJ_{v+1}.                                           \tag{17}
\]

Apply `(17)` at `v` and `v+1`.  Since `J_(v+1)` is nonzero, the two scalars agree.  Induction down
the connected edge path produces one `lambda` with

\[
 \boxed{L_v=\lambda J_v\quad(1\le v<n).}                             \tag{18}
\]

#### Step 2 -- remove the synchronized two-site part

Put `K'=K-lambda H`.  Then `[H,K']=0`, all two-site coefficients of `K'` vanish, and

\[
 K'=d'I+\sum_{v=1}^n r_v\mathbin\cdot\boldsymbol\sigma_v.             \tag{19}
\]

The weight-two coefficient of `[H,K']` on edge `v` is exactly

\[
 \mathcal R_{J_v}(r_v,r_{v+1}).                                     \tag{20}
\]

At the field-rigid edge `q`, equations `(5)` and `(20)` give

\[
 r_q=r_{q+1}=0.                                                       \tag{21}
\]

If `J` is invertible, then `R_J(a,0)=0` forces `a=0`: its three independent columns cannot all
commute with one nonzero Pauli direction.  Likewise `R_J(0,b)=0` forces `b=0`.  Starting from
`(21)` and propagating `(20)` left and right along the path gives

\[
 r_v=0\qquad(1\le v\le n).                                          \tag{22}
\]

Thus `K'=d'I`, proving `K=lambda H+d'I`.  The reverse inclusion in `(13)` is immediate. `square`

## Corollary D -- exact and quantitative tangent rigidity

If `A in L_n` generates a one-parameter unitary group commuting with `H`,

\[
 [e^{-isA},H]=0\qquad(s\in\mathbb R),                                \tag{23}
\]

then

\[
 \boxed{A=\lambda H+\mu I}                                          \tag{24}
\]

and its flow is only a global phase times a reparametrization of physical time.

Equip `L_n` and the ambient Hermitian matrices with Hilbert--Schmidt norm, and let `S_H` be the
orthogonal complement of `span{I,H}` inside `L_n`.  The number

\[
 \gamma_H=\inf\{\|[H,A]\|_{\rm HS}:A\in S_H,\ \|A\|_{\rm HS}=1\}   \tag{25}
\]

is strictly positive.  Every `A in L_n` therefore obeys

\[
 \boxed{
 \operatorname{dist}_{\rm HS}(A,\operatorname{span}\{I,H\})
 \le {\|[H,A]\|_{\rm HS}\over\gamma_H}.}                           \tag{26}
\]

On every compact family satisfying `(3)` and `(5)` with uniform distance from their failure
loci, `gamma_H` has a positive uniform lower bound.

### Proof

Differentiating `(23)` at zero gives `[H,A]=0`, so Theorem C proves `(24)`.  Theorem C also says
that `ad_H` is injective on the finite-dimensional unit sphere of `S_H`.  Its norm has a positive
minimum there, which is `(25)`.  Projecting any `A` orthogonally to `S_H` proves `(26)`.  Continuity
and compactness give the uniform statement. `square`

## Conjecturing / falsification ledger

### C0 -- the moving centralizer contains many alternative two-local flows

**Verdict:** `[FALSIFIED GENERICALLY AND CLASSIFIED EXACTLY]` by Theorem C.  Modulo scalar phase,
the only two-local commuting generator is `H` itself.

### C1 -- invertible edge couplings alone remove all local fields

**Verdict:** `[FALSE]`.  An isotropic edge admits simultaneous spin rotations.  One field-rigid
edge is load-bearing.  Lemma B proves that this extra condition is open dense rather than an
integrability assumption.

### C2 -- tangent rigidity proves circuit undistortion

**Verdict:** `[FALSE]`.  A finite circuit may leave the centralizer and return.  Products and
commutators of two-local generators also create higher-locality effective Hamiltonians, including
`H^2`-type functional calculus.  Theorem C excludes hidden local tangent directions, not transverse
holonomy.

### Strongest survivor

The moving-centralizer undistortion conjecture from the parent card now has a proved infinitesimal
base case:

> On the generic open-chain shell, the cheap tangent cone intersects the moving centralizer in
> exactly the physical time line.  Any nontrivial shortcut must be a finite transverse excursion,
> and its return to the centralizer must create the large resolved bandwidth extracted by the
> parent theorem.

The next quantitative object is therefore not another spectral gap.  It is the transverse
holonomy of local-control words relative to the one-dimensional local kernel `(13)`.

## Hostile audit

1. **Not the Brown ramp.**  The theorem classifies time-independent two-local commuting
   generators.  It gives no lower bound for an arbitrary finite circuit which leaves the shell.
2. **Open chain.**  Unique three-site supports make `(16)` pairwise.  Triangles allow cancellation
   among three edge pairs and require a separate graph theorem.
3. **Full-rank edges.**  Singular coupling matrices can support decoupled axes or classical
   carriers.  They belong to the explicit determinant failure locus.
4. **One rigid edge.**  This is necessary for the proof and generically true.  Isotropic symmetry
   points are genuine counterexamples, not technical omissions.
5. **No uniform condition number yet.**  Equation `(26)` is exact for each retained `H`, but no
   quenched lower tail for `gamma_H` is proved.  Such a tail is only a tangent estimate and cannot
   replace finite-word holonomy control.
6. **Relation to Hamiltonian learning.**  Generic recovery of a local Hamiltonian up to scale from
   steady-state or eigenstate data is established in the Hamiltonian-learning literature.  The
   theorem here is an operator identity derived directly from consecutive-edge Pauli coefficients;
   no state, measurements, covariance matrix, or reconstruction premise occurs.  Priority of this
   exact path classification remains unverified.
7. **Lean deferred.**  No Lean file or process was touched during the shared refactor.  The theorem
   cannot enter a final manuscript before exact formalization and axiom audit.

## External boundary

- Qi--Ranard study generic recovery of local Hamiltonians from one eigenstate
  (`arXiv:1712.01850`).
- Evans--Harper--Flammia formulate recovery from a steady state through a correlation-matrix kernel
  and emphasize that generic uniqueness is only up to scale (`arXiv:1912.07636`).
- The commuting-local-Hamiltonian literature classifies families of mutually commuting local terms;
  it does not, in the targeted search, state the consecutive-edge synchronization theorem
  `(13)` for two arbitrary full-shell open-chain Hamiltonians.

## Exact next move

Let `P_H` be Hilbert--Schmidt projection onto `span{I,H}` inside `L_n`.  For a local-control word,
track its logarithmic increments in the moving frame and split each increment into `P_H` and
`I-P_H` parts.  Theorem C makes the first part literal time reparametrization.  Prove that a word
returning within fixed operator-norm resolution of `T_H` cannot create parent-card bandwidth
`Omega(s)` unless the accumulated transverse Magnus brackets have `Omega(s)` local-control cost.
That is the finite holonomy theorem still missing from the Brown law.
