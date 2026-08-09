# Fast-forwardable-stratum codimension obstruction

- **ID:** fast-forwardable-stratum-codimension-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM / sharp obstruction for autonomous no-shortcut laws
- **Stage:** 3-formalized
- **Formalized companion:** `./fast-forwardable-stratum-codimension-obstruction-formalized.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4

## Exact statement

Let `V=R^m` with its Euclidean norm, let

\[
 H:V\longrightarrow\operatorname{Herm}(\mathcal H)
\]

be real-linear, and fix a normalized initial state `Phi_0`.  Assume constants
`L_H,lambda_->0` and a homogeneous direct-simulation scale `Lambda` satisfy

\[
 \|H(x)-H(y)\|\leq L_H\|x-y\|,
 \qquad
 \Lambda(H(x))\geq\lambda_-\|x\|.                    \tag{1}
\]

Fix `0<=epsilon_-<epsilon_+`, `a>0`, and a positive polynomial cost divisor
`p(n)`.  Let `F<=V` have dimension `0<f<m`.  Suppose there is a radial-
independent integer `B` such that

\[
 C_{\epsilon_-}(e^{-iH(y)}\Phi_0)\leq B
 \qquad (y\in F).                                      \tag{2}
\]

The bound must be supplied by a finite-format synthesis certificate, not by
defining `F` as a subset of the shortcut locus.  For a fixed finite universal
gate set, (2) can be a bounded word dictionary; for continuously adjustable
local gates it can be a fixed architecture with variable parameters.

Put `d=m-f`, choose

\[
 0<r\leq\min\left\{1,{\epsilon_+-\epsilon_-\over L_H}\right\},
\]

and let `J` be standard Gaussian in `V`.  For

\[
 t\geq T_0:=\max\left\{2r,1,
 {2Bp(n)\over a\lambda_-}\right\},                    \tag{3}
\]

one has

\[
 \begin{split}
 &\mathbb P\left\{
 C_{\epsilon_+}(e^{-itH(J)}\Phi_0)
 \leq {a\Lambda(H(tJ))\over p(n)}
 \right\}\\
 &\qquad\geq
 p_f(2\pi)^{-d/2}e^{-1/2}v_dr^d\,t^{-d},              \tag{4}
 \end{split}
\]

where

\[
 p_f=\mathbb P\{1\leq\|\pi_FJ\|\leq2\}>0
\]

and `v_d` is the volume of the Euclidean unit ball in `R^d`.

Consequently, any uniform upper no-shortcut law of the form `K t^{-kappa}` on
an unbounded pre-capacity double-scaling range must obey

\[
 \boxed{\kappa\leq m-f.}                               \tag{5}
\]

Deterministically, after the same error and budget margins, the radial
shortcut locus contains a fixed-radius tube about `F` and therefore has

\[
 \operatorname{vol}(\mathfrak S_{\epsilon_+,a}\cap
 \{x:R\leq\|x\|\leq2R\})\geq cR^f                   \tag{6}
\]

for all sufficiently large pre-capacity `R`.

## Proof

Write `J=J_F+J_perp` using the orthogonal Gaussian decomposition along
`F direct-sum F^perp`.  Consider

\[
 E_t=\{1\leq\|J_F\|\leq2,\ \|J_\perp\|\leq r/t\}.     \tag{7}
\]

The two projections are independent.  On the `d`-ball of radius `r/t<=1`,
standard Gaussian density is at least `(2pi)^(-d/2)exp(-1/2)`.  Hence

\[
 \mathbb P(E_t)
 \geq p_f(2\pi)^{-d/2}e^{-1/2}v_dr^dt^{-d}.            \tag{8}
\]

For `J in E_t`, set `y=tJ_F in F`.  Linearity gives
`tH(J)=H(tJ)` and Duhamel continuity gives

\[
 \|e^{-itH(J)}\Phi_0-e^{-iH(y)}\Phi_0\|
 \leq t\|H(J)-H(J_F)\|
 \leq L_Ht\|J_\perp\|
 \leq\epsilon_+-\epsilon_-.                           \tag{9}
\]

By (2) and the triangle inequality, the circuit for `y` prepares the endpoint
at `tJ` to error `epsilon_+` with at most `B` gates.  Also

\[
 \|tJ\|\geq t\|J_F\|-t\|J_\perp\|\geq t-r\geq t/2.    \tag{10}
\]

Equations (1), (3), and (10) imply

\[
 {a\Lambda(H(tJ))\over p(n)}
 \geq {a\lambda_-t\over2p(n)}\geq B.                 \tag{11}
\]

Thus `E_t` is contained in the shortcut event, and (8) proves (4).  If an
upper bound `Kt^{-kappa}` held with `kappa>d` for arbitrarily large uniform
times, comparison with (4) would force `t^(kappa-d)` to remain bounded, a
contradiction.  This proves (5).

For (6), take the product of an `f`-dimensional shell in `F` with a fixed
`d`-ball in `F^perp`.  Its volume is `cR^f`.  The same Duhamel and budget
argument places it in the relaxed shortcut locus for large `R`.

## Exact recurrent refinement

Suppose a basis `P_1,...,P_m` for `H` has norm at most one and
`P_1,...,P_f` are commuting Hermitian involutions.  Put `delta=eta/m` for
`0<eta<=1`.  The event

\[
 \operatorname{dist}(tJ_j,2\pi\mathbb Z)\leq\delta\ (j\leq f),
 \qquad |tJ_j|\leq\delta\ (j>f)                       \tag{12}
\]

lies in the `eta`-ball about the identity.  Choosing the nearest integers,
commutativity gives an exact recurrent centre and Duhamel gives total error at
most `m delta=eta`.  For `t>=4pi`, disjoint phase intervals inside
`[-1/2,1/2]` yield

\[
 \mathbb P((12))\geq
 \left({\varphi(1)\delta\over2\pi}\right)^f
 \left(2\varphi(1)\delta\right)^{m-f}t^{-(m-f)}.       \tag{13}
\]

Thus the same codimension exponent is already forced by exact recurrence
mass, with the identity word as witness.

For all-to-all fixed-`q` Pauli coefficients,

\[
 f_Z(n,q)=\sum_{k=1}^q{n\choose k},\qquad
 m(n,q)=\sum_{k=1}^q3^k{n\choose k}.                  \tag{14}
\]

The `Z`-string sector is commuting and has uniform coefficient-independent
synthesis cost at fixed error.  Therefore every admissible Gaussian escape
exponent satisfies

\[
 \kappa\leq m(n,q)-f_Z(n,q).                           \tag{15}
\]

## What this changes

The prior O4 target treated `kappa` as an unspecified constant fraction of
`m` and called the resulting functional form optimal based on one periodic
ray.  That optimality statement was incomplete.  Every extensive
fast-forwardable sector contributes a radial tube, so its dimension must be
subtracted from the best possible no-shortcut exponent.  The upper frontier is
therefore an inverse theorem: prove that every larger family of shortcut
islands forces a larger uniformly synthesizable stratum.

## Hostile audit

1. This theorem is a lower bound on shortcut probability, not the Brown--
   Susskind upper bound.
2. `F` must have an independently checked uniform synthesis certificate.
   Taking `F` to be the shortcut set would make the statement circular.
3. Constants depend on `m,f,r`; exponent comparison is valid only under the
   uniform `n,t` quantifiers of the proposed pre-capacity law.
4. The fixed-`n`, `t->infinity` limit is excluded because finite circuit
   capacity eventually makes every endpoint easy.
5. A nonlinear or arithmetically scattered easy family may have larger radial
   growth than every linear `F`.  This theorem exposes that possibility; it
   does not classify it.

## Novelty status

The proof is elementary once the radial shortcut formulation is available.
No external source located in the current audit states the codimension ceiling
for static local-Hamiltonian complexity or its commuting-Pauli value (15).
Priority is not yet established; the result remains `[NOVELTY UNVERIFIED]` and
must not be promoted as the paper's headline theorem.

## Formalization status

Formalized in `HTGeometry/FastForwardableStratumCodimension.lean` together with the new
`HTGeometry/GaussianIntervalPositivity.lean`, reusing the corpus product-Gaussian small-ball
bound (`GaussianSmallBallLowerBound.lean`), the Duhamel transport
(`ObserverInvisibleTubeShortcut.lean`), the annular tube volume
(`ObserverKernelTubeVolume.lean`) and the approximate-complexity definition
(`ExactPenaltyCircuitBellman.lean`).  The four pieces named above are respectively
`measure_pi_gaussian_transverse_ball_lower`, `exists_witness_tube`, `le_cost_budget`, and
`zStringSectorDim` / `nonidentityPauliWeightCount_sub_zStringSectorDim`.  No external library is
used.  See the formalized companion.
