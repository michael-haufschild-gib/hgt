# Mixed periodic-synthesis carrier obstruction

- **ID:** mixed-periodic-synthesis-carrier-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM / sharp lower obstruction for autonomous no-shortcut laws
- **Stage:** 3-formalized
- **Formalized companion:** `./mixed-periodic-synthesis-carrier-obstruction-formalized.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4

## Exact statement

Let `V=R^m` be Euclidean, let

\[
 H:V\longrightarrow\operatorname{Herm}(\mathcal H)
\]

be real-linear, and fix a normalized state `Phi_0`.  Assume

\[
 \|H(x)-H(y)\|\leq L_H\|x-y\|,
 \qquad \Lambda(H(x))\geq\lambda_-\|x\|             \tag{1}
\]

for constants `L_H,lambda_->0` and a homogeneous direct-simulation scale
`Lambda`.

Let `W,G<=V` be orthogonal subspaces with

\[
 \dim W=d,\qquad \dim G=r,\qquad d+r\leq m,
\]

and let `Gamma<=G` be a full lattice.  Assume `d+r>0`.  Suppose there is a
radial-independent integer `B` and an independently supplied finite-format
synthesis certificate such that

\[
 C_{\epsilon_-}(e^{-iH(w+\gamma)}\Phi_0)\leq B
 \qquad(w\in W,\ \gamma\in\Gamma).                  \tag{2}
\]

Here `0<=epsilon_-<epsilon_+`.  Condition (2) is structural input; it may not
be obtained by defining `W+Gamma` to be part of the shortcut locus.

Fix `a>0` and a positive cost divisor `p(n)`.  Then there are positive
constants `c,R_0`, depending on the displayed data but not on `R`, such that

\[
 \operatorname{vol}\!\left(
  \mathfrak S_{\epsilon_+,a}\cap
  \{x:R\leq\|x\|\leq2R\}
 \right)\geq cR^{d+r}                               \tag{3}
\]

whenever

\[
 R\geq R_0,
 \qquad {a\lambda_-R\over p(n)}\geq B.              \tag{4}
\]

If `J` is standard Gaussian in `V`, the radial identity
`tH(J)=H(tJ)` consequently gives, for all sufficiently large admissible `t`,

\[
 \mathbb P\!\left\{
 C_{\epsilon_+}(e^{-itH(J)}\Phi_0)
 \leq {a\Lambda(H(tJ))\over p(n)}
 \right\}
 \geq c' t^{-(m-d-r)}.                              \tag{5}
\]

Every uniform upper no-shortcut exponent therefore obeys

\[
 \boxed{\ \kappa\leq m-d-r.\ }                     \tag{6}
\]

The continuous synthesis dimension and the discrete recurrence rank add.
Neither one alone is the correct obstruction.

## Structural sufficient condition

Condition (2) follows from the more recognizable hypotheses

\[
 [H(w),H(\gamma)]=0,
 \qquad e^{-iH(\gamma)}\Phi_0=e^{i\vartheta(\gamma)}\Phi_0
 \quad(w\in W,\gamma\in\Gamma),                    \tag{7}
\]

together with a `B`-gate synthesis certificate for
`e^{-iH(w)}Phi_0`, uniform in `w`.  Indeed, (7) gives

\[
 e^{-iH(w+\gamma)}\Phi_0
 =e^{i\vartheta(\gamma)}e^{-iH(w)}\Phi_0,            \tag{8}
\]

so the same projective-state circuit works.  A direct product of an
efficiently synthesizable subsystem and an independent periodic subsystem is
the canonical mixed example.

## Proof of the deterministic bound

Choose

\[
 0<\rho\leq {\epsilon_+-\epsilon_-\over L_H}.        \tag{9}
\]

Replace `Gamma` by a finite-index sublattice whose nonzero vectors have norm
greater than `4rho`.  This does not change its rank.  Standard fundamental-
domain comparison gives constants `c_G,R_G>0` such that this sublattice has at
least `c_G R^r` points in a radius-`R/8` ball for `R>=R_G`.  The corresponding
radius-`rho` transverse balls are disjoint.

First suppose `d>0`.  For every selected `gamma` with `||gamma||<=R/8`, take

\[
 {5R\over4}\leq\|w\|\leq {3R\over2},\qquad
 z\in W^\perp,\quad\|z\|\leq\rho,                   \tag{10}
\]

and put `x=w+gamma+z`.  For `R>=8rho`, the triangle inequality gives

\[
 R\leq\|x\|\leq2R.                                  \tag{11}
\]

The sets in (10) belonging to distinct selected lattice points are disjoint.
Their total volume is bounded below by

\[
 c_G R^r\,
 \operatorname{vol}_W\!\left\{w:{5R\over4}\leq\|w\|
                              \leq{3R\over2}\right\}
 v_{m-d}\rho^{m-d}
 \geq cR^{d+r}.                                      \tag{12}
\]

For every such `x`, (1), (2), (9), and Duhamel continuity imply

\[
 \|e^{-iH(x)}\Phi_0-e^{-iH(w+\gamma)}\Phi_0\|
 \leq L_H\|z\|\leq\epsilon_+-\epsilon_-.           \tag{13}
\]

The certified `B`-gate circuit is therefore an `epsilon_+` approximant.  By
(1), (4), and `||x||>=R`, it also lies within the relative shortcut budget.
This proves (3) when `d>0`.

If `d=0`, then `r>0`.  Fundamental-domain comparison in the lattice annulus

\[
 {5R\over4}\leq\|\gamma\|\leq {3R\over2}           \tag{14}
\]

supplies at least `c_G'R^r` separated lattice points.  Their disjoint
`rho`-balls lie in the annulus in (3) for large `R`; (13) and the same budget
argument apply.  Their total volume is `Omega(R^r)`, completing the proof of
(3).

## Proof of the Gaussian bound

Let `E_t` be the subset of the annulus in (3) constructed above with `R=t`.
The random vector `tJ` has density

\[
 (2\pi t^2)^{-m/2}\exp(-\|x\|^2/(2t^2)).             \tag{15}
\]

On `E_t subset {t<=||x||<=2t}`, this density is at least
`(2pi)^(-m/2)e^(-2)t^(-m)`.  Combining (3) and (15) gives

\[
 \mathbb P\{tJ\in E_t\}
 \geq (2\pi)^{-m/2}e^{-2}t^{-m}\operatorname{vol}(E_t)
 \geq c't^{-(m-d-r)}.                               \tag{16}
\]

The radial identity and the deterministic shortcut inclusion prove (5).
Comparison with any upper law `Kt^(-kappa)` on an unbounded uniform
pre-capacity double-scaling range proves (6).

## What this changes

The prior conjectural invariant used the largest dimension of a continuous
uniform synthesis chart.  That representation is incomplete.  A rank-`r`
period lattice transverse to a `d`-dimensional fast-forwardable family creates
`Theta(R^r)` disjoint copies of an `R^d` carrier, and the exponents add.  A
correct inverse theorem must classify mixed continuous-discrete carriers and
must also control proliferation across circuit architectures.

This theorem strictly extends the forced half of
`fast-forwardable-stratum-codimension-obstruction`: its `r=0` case recovers
that result, while `r>0` permits recurrence directions not already contained
in the continuously synthesizable chart.

## Hostile audit

1. This is a lower obstruction, not the required Brown--Susskind upper law.
2. The theorem assumes an explicit synthesis certificate on `W+Gamma`; it
   does not classify when one exists.
3. Lattice rank is not a substitute for circuit-architecture entropy.
   Unorganized isolated intersections could still outgrow every mixed
   carrier; excluding them is the inverse frontier.
4. The exponent comparison requires uniform constants in an unbounded
   `n,t` pre-capacity regime.  At fixed `n`, compact circuit capacity
   eventually makes every endpoint easy.
5. No novelty claim is made.  The result requires a dedicated priority audit
   before external scientific use.

## Formalization status

Formalized in `HTGeometry/MixedPeriodicCarrierObstruction.lean` on top of the new
`HTGeometry/LatticeGaussianDensity.lean` and the already-formalized
`HTGeometry/FastForwardableStratumCodimension.lean`.  See the formalized companion.

