# Krylov carrier-load shortcut dichotomy law

- **ID:** `krylov-carrier-load-shortcut-dichotomy-law`
- **Stage:** 3 — formalized
- **Type:** THEOREM / SELECTOR-SAFE REPLACEMENT
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Date:** 2026-08-06

## Public sentence

Before a bounded Hamiltonian can be captured by any member of a finite target
family, that family must already place detectable mass in the Hamiltonian's
finite Krylov history.  Everything outside that history is excluded by one
factorial causal bound, simultaneously for all targets.

## Exact universal law

Let `I` be finite, let `E_i in [-B,B]`, and equip `C^I` with its Euclidean
norm.  For `K>=0`, define

\[
 \mathcal K_K(E)=\operatorname{span}\{(E_i^k)_{i\in I}:0\le k\le K\},
 \qquad P_K=P_{\mathcal K_K(E)}.                              \tag{1}
\]

For `x in C^I`, write its normalized spectral amplitude as

\[
 A_x(t)=|I|^{-1/2}\sum_{i\in I}x_i e^{\mathrm i tE_i}.       \tag{2}
\]

If `|I|>0`, then for every real `t`,

\[
 \boxed{
 |A_x(t)|\le \|P_Kx\|_2+
 \|(I-P_K)x\|_2\,{(B|t|)^{K+1}\over(K+1)!}.}                \tag{3}
\]

In particular, if `||x||_2<=1`,

\[
 |A_x(t)|\le \|P_Kx\|_2+{(B|t|)^{K+1}\over(K+1)!}.          \tag{4}
\]

For a finite family `(x_w)_(w in W)`, define its aggregate Krylov load

\[
 \mathfrak L_K(W;E)=\sum_{w\in W}\|P_Kx_w\|_2^2.             \tag{5}
\]

Then every unit-bounded target obeys, simultaneously,

\[
 \boxed{
 |A_{x_w}(t)|\le \sqrt{\mathfrak L_K(W;E)}+
 {B^{K+1}|t|^{K+1}\over(K+1)!}.}                             \tag{6}
\]

Consequently, if

\[
 \sqrt{\mathfrak L_K(W;E)}+
 {B^{K+1}T^{K+1}\over(K+1)!}<\theta,                         \tag{7}
\]

then `|A_(x_w)(t)|<theta` for every `w` and every `|t|<=T`.
Unlike a targetwise `Z_r` estimate, `(7)` is one positive certificate for the
whole adaptive family.  The number of targets never appears as an external
union factor.

The form strong enough for exponentially large target families is the
growing-replica load

\[
 \mathfrak L_{K,r}(W;E)
 =\sum_{w\in W}\|P_Kx_w\|_2^{2r}.                              \tag{6r}
\]

If `|A_(x_w)(t)|>=theta` and the factorial remainder `eta_K(t)` is below
`theta`, then, unconditionally,

\[
 \boxed{
 (\theta-\eta_K(t))^{2r}\le\mathfrak L_{K,r}(W;E).}           \tag{7r}
\]

Thus the strict reverse inequality at `eta_K(T)` excludes every adaptive
target throughout `[-T,T]`.  Replica order amplifies the carrier angle
itself; it does not count positive near-action pairs and therefore has no
central-limit crowding floor.

## Static-Choi specialization

For a `d`-level Hamiltonian with spectral energies `E_i`, let

\[
 |\Phi_H(t)\rangle=d^{-1/2}\sum_i e^{-\mathrm i tE_i}|i,i\rangle
\]

and let `\phi_w` be normalized full-Choi targets.  Put
`x_(w,i)=\langle i,i|\phi_w\rangle` and use the frequency vector `-E` in
`(1)`--`(7)`.  Coordinate restriction is contractive, so `||x_w||_2<=1`,
and

\[
 A_{x_w}(t)=\langle\Phi_H(t),\phi_w\rangle.                   \tag{8}
\]

If the pure-state trace distance from `Phi_H(t)` to some `phi_w` is at most
`epsilon in [0,1]`, then

\[
 \sqrt{1-\epsilon^2}-{B^{K+1}|t|^{K+1}\over(K+1)!}
 \le \|P_Kx_w\|_2.                                          \tag{9}
\]

Thus no target in the family can capture the orbit anywhere in `[-T,T]`
whenever

\[
 \sqrt{\mathfrak L_K(W;-E)}+
 {B^{K+1}T^{K+1}\over(K+1)!}<\sqrt{1-\epsilon^2}.            \tag{10}
\]

More strongly, for every replica order `r`, no capture occurs if

\[
 \mathfrak L_{K,r}(W;-E)<
 \left(\sqrt{1-\epsilon^2}-
 {B^{K+1}T^{K+1}\over(K+1)!}\right)^{2r},                    \tag{11}
\]

with nonnegative parenthesis.

## Scalar recurrence charged once

For each normalized target, let

\[
 \alpha_w=\langle\Phi_H(0),\phi_w\rangle,
 \qquad
 \phi_w^\circ=\phi_w-\alpha_w\Phi_H(0),                       \tag{12}
\]

and let `x_w^circ` be the spectral diagonal of `phi_w^circ`.  This residual
is orthogonal to the identity Choi vector and has norm at most one.  Define

\[
 \mathfrak L_{K,r}^\circ
 =\sum_w\|P_Kx_w^\circ\|_2^{2r},
 \qquad
 R_H(t)=|\langle\Phi_H(t),\Phi_H(0)\rangle|.                   \tag{13}
\]

If `R_H(t)<rho` and target `w` captures at trace-distance `epsilon`, then

\[
 \boxed{
 \left(\sqrt{1-\epsilon^2}-\rho-
 {B^{K+1}|t|^{K+1}\over(K+1)!}\right)^{2r}
 \le\mathfrak L_{K,r}^\circ,}                                 \tag{14}
\]

whenever the parenthesis is nonnegative.  Hence, on the complement of the
single common return event `R_H(t)>=rho`, the strict reverse of `(14)` at
`|t|=T` excludes every circuit target simultaneously.  This is the exact
formal version of “isolate common recurrence mass once, then amplify every
remaining shortcut in replicas.”

## Proof

Let `r=(I-P_K)x`.  Orthogonal projection makes `r` perpendicular to every
energy-power vector through degree `K`, hence

\[
 \sum_i r_iE_i^k=0\qquad(0\le k\le K).                       \tag{11}
\]

The Krylov causal replica-sieve theorem applied at replica order one gives

\[
 |A_r(t)|\le\|r\|_2{(B|t|)^{K+1}\over(K+1)!};                \tag{12}
\]

the only normalization step is
`|I|^(-1/2) sum_i |r_i|<=||r||_2`.  Cauchy--Schwarz gives
`|A_(P_Kx)(t)|<=||P_Kx||_2`.  Adding the two amplitudes proves `(3)`.
Projection contractivity proves `(4)`.  For every `w`, positivity gives

\[
 \|P_Kx_w\|_2^2\le\sum_v\|P_Kx_v\|_2^2=\mathfrak L_K(W;E),
\]

which proves `(6)` and `(7)`.  Raising the capture-forced carrier inequality
to `2r` and retaining its one nonnegative summand proves `(7r)`.  Equation
`(8)` is the exact diagonal Choi overlap.  Pure-state trace distance implies
overlap at least `sqrt(1-epsilon^2)`, yielding `(9)`--`(11)`.  The exact
scalar/traceless decomposition bounds the scalar coefficient by one and
charges `R_H(t)` once.  Applying `(7r)` to the norm-one traceless residual
proves `(12)`--`(14)`.

## Why this moves the frontier

The positive near-action partition `Z_r` cannot be exponentially small: its
identity component has the universal central-limit floor on the companion
route-killer card.  Signed moment nullity closes only a residual target at a
time.  The present law performs the canonical orthogonal split and packages
the complete adaptive target family into one scalar load.  It therefore
removes both defects at once:

1. the common recurrence channel is not charged once per circuit;
2. the target selector is never commuted through an expectation or a signed
   cancellation estimate.

The new load is geometric rather than tautological: it is the trace of the
target frame operator compressed to the energy-moment Krylov flag,

\[
 \mathfrak L_K=\operatorname{Tr}\!\left(P_K
   \sum_w|x_w\rangle\langle x_w|\right).                      \tag{13}
\]

This gives a concrete interface for circuit-transfer, Pauli-walk, or random-
matrix estimates.

## Hostile audit

1. `(3)`--`(14)` are deterministic and unconditional.  They do not assume
   chaos, level repulsion, generic spectrum, or an ensemble limit.
2. This theorem is not a quenched local-Hamiltonian estimate on
   `mathfrak L_K`.  That is now the only probabilistic/dynamical input needed
   by this route.
3. The second-moment load `mathfrak L_K` is too weak for exponentially many
   targets.  This hostile failure forced the stronger
   `mathfrak L_(K,r)`.  Duplicated circuit words can still make either load
   large; the final application must use distinct endpoints, a resolved
   frame, or a Bellman recursion.
4. The factorial term is useful only while `K` is at least a constant larger
   than `BT`.  Thus a Brown--Susskind linear window requires a growing-K
   bound, not a fixed-moment theorem.
5. The Krylov carrier contains the true early orbit.  No argument may call it
   an exceptional remainder or infer circuit hardness from its dimension
   alone.
6. The theorem does not prove the Brown--Susskind law, a black-hole claim, or
   maximal complexity.  It closes the exact residual/selector reduction and
   exposes the remaining carrier estimate without hiding it.

**Verdict:** `PAPER-PROVED`, `LEAN-PROVED`, and a strict frontier reduction.
Nature-level manuscript use remains unauthorized until the ordinary local-
Hamiltonian growing-K load is bounded and external priority is audited.

## Exact open core

For the normalized fixed-`q>=2` Gaussian Pauli ensemble and the resolved
depth-`s` circuit frame, prove a quenched estimate on

\[
 \mathfrak L_{K,r}(\mathcal C_{n,s};E(H)),\qquad K\asymp \|H\|T,
\]

strong enough that `(11)` survives at replica order comparable to circuit
entropy through the desired linear-growth and plateau window.  The proof must
control the positive high-order compressed frame load directly.  Signed
fixed-target Wick cancellation, raw Krylov dimension, and linear Hall
expansion do not imply it.

## Formal trace

Modules:

- `formal/GaloisForLFunctions/HTGeometry/KrylovCarrierProjectionLaw.lean`
- `formal/GaloisForLFunctions/RHTower/StaticChoiKrylovCarrierDichotomyLaw.lean`
- `formal/GaloisForLFunctions/RHTower/ScalarRecurrenceKrylovReplicaDichotomyLaw.lean`

Capstones:

- `norm_normalizedSpectralAmplitude_le_krylovCarrier_add_factorial`
- `no_large_adaptive_amplitude_of_finiteKrylovLoad`
- `finiteKrylovCarrierReplicaLoad_ge_of_large_amplitude`
- `no_large_adaptive_amplitude_of_finiteKrylovReplicaLoad`
- `staticChoiTargetCapture_implies_krylovCarrier`
- `no_staticChoiTargetCapture_of_krylovCarrierLoad`
- `no_staticChoiTargetCapture_of_krylovCarrierReplicaLoad`
- `scalarRemovedKrylovReplicaLoad_ge_of_capture`
- `no_staticChoiTargetCapture_off_scalarReturn_of_krylovReplicaLoad`

Targeted `lake env lean` elaboration passes.  `#print axioms` for the moment-
null projection, universal amplitude bound, adaptive load law, exact Choi
identity, capture implication, and no-capture capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: exact selector-safe statement and hostile falsifiers
- [x] 1 -> 2: dependency-closed proof
- [x] 2 -> 3: exact Lean theorem and axiom audit
- [ ] 3 -> 4: growing-K local-H load bound and external priority audit

## Log

- 2026-08-06 — Replaced positive replica crowding by a canonical Krylov
  projection dichotomy and compressed frame-load certificate.
- 2026-08-06 — Hostile review killed second-moment load at exponential target
  entropy; proved its growing-replica replacement `(6r)--(11)`.
- 2026-08-06 — Combined the exact scalar/traceless split with replicated
  Krylov load, charging common recurrence once and proving `(12)--(14)`.
