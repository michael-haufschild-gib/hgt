# A logarithmic endpoint skeleton forces a continuous Brown ramp

- **ID:** `geometric-skeleton-brown-ramp-transfer-law`
- **Stage:** 3-formalized
- **Formalized companion:** `./geometric-skeleton-brown-ramp-transfer-law-formalized.md`
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN-PROVED]`
- **Type:** deterministic transfer theorem / frontier reduction
- **Parent:** `fixed-shell-transversality-onset-hardening-cone-law.md`
- **Child target:** `quenched-krylov-circuit-incidence-front-law.md`

## Claim

Pointwise circuit-complexity growth on every time of a static Hamiltonian ramp does **not** require
an anti-shortcut estimate on a linear time mesh.  Hardness at only a geometric skeleton of times
forces a continuous lower ramp by autonomous circuit composition.  A Brown interval whose duration
is exponential in the number of qubits therefore needs only linearly many hard endpoint events;
an exponentially decaying replica reporter needs replica order only logarithmic in the number of
qubits to survive their union.

This theorem does not prove those endpoint events for an ordinary static local Hamiltonian.  It
removes the formerly larger complete-mesh obligation and freezes the smaller exact open core.

## Setup

Let `(X,d)` be a metric space, let `U_t` be an isometric one-parameter group on `X`, and fix a seed
`chi in X`.  Write

\[
 \psi_t=U_t\chi .
\]

Let `G` be the allowed local gate family.  For `epsilon>=0`, let `C_epsilon(x)` be the least word
length of a `G`-circuit whose action on `chi` lies within `epsilon` of `x`.  Define the uniform
simulation complexity

\[
 S(u,\gamma)=\min\bigl\{|w|:\sup_{x\in X}d(W_wx,U_ux)\le\gamma\bigr\}.       \tag{1}
\]

Fix error budgets

\[
 0\le \epsilon_-<\epsilon_+,
 \qquad \gamma=\epsilon_+-\epsilon_- .                         \tag{2}
\]

Assume that, on the time interval of interest, a deterministic local-Hamiltonian simulator gives

\[
 S(u,\gamma)\le vu+A                                             \tag{3}
\]

for constants `v>0` and `A>=0`.  No randomness, spectral condition, or monotonicity of complexity
is assumed.

## Theorem A -- geometric endpoint skeleton implies a continuous ramp

Choose `c in (0,1]` and `q>1` with

\[
 q(1-c)<1, \qquad c':=1-q(1-c)>0.                              \tag{4}
\]

Let

\[
 0<T_0<T_1<\cdots<T_N,
 \qquad T_j/T_{j-1}\le q                                      \tag{5}
\]

and suppose that every skeleton endpoint obeys

\[
 C_{\epsilon_+}(\psi_{T_j})>cvT_j-K                            \tag{6}
\]

for one `K>=0`.  Then every time `t in [T_0,T_N]` obeys

\[
 \boxed{
 C_{\epsilon_-}(\psi_t)>c'vt-(K+A).}                           \tag{7}
\]

Thus endpoint hardness at a fixed positive fraction `c` of the local simulation speed forces a
pointwise linear lower ramp.  For example, `q=1+c/2` is always admissible and gives

\[
 c'={c(1+c)\over2}\ge {c\over2}.                              \tag{8}
\]

### Proof

Fix `t in [T_0,T_N]` and choose `j` with `t in [T_{j-1},T_j]`, taking `j=0` and `t=T_0` separately.
For `j>=1`, compose a circuit preparing `psi_t` to error `epsilon_-` with a circuit uniformly
simulating `U_(T_j-t)` to error `gamma`.  The group law and the triangle inequality give

\[
 C_{\epsilon_+}(\psi_{T_j})
 \le C_{\epsilon_-}(\psi_t)+S(T_j-t,\gamma).                   \tag{9}
\]

Equations `(3)` and `(6)` imply

\[
 \begin{aligned}
 C_{\epsilon_-}(\psi_t)
 &>cvT_j-K-v(T_j-t)-A\\
 &=vt-(1-c)vT_j-(K+A).                                         \tag{10}
 \end{aligned}
\]

Since `t>=T_(j-1)>=T_j/q`, we have `T_j<=qt`.  Substitution in `(10)` yields `(7)`.  At `t=T_0`,
use the endpoint hypothesis `(6)` directly; because `c'<=c`, it is stronger than `(7)`.  This
closes every time in the interval.  No interpolation or continuity of `C_epsilon` is used.

## Theorem B -- matching upper ramp from an easy seed

Suppose additionally that `C_eta(chi)<=b` and that, for a second simulator error `delta>=0`,

\[
 S(t,\delta)\le vt+A_+ .                                       \tag{11}
\]

Then

\[
 \boxed{
 C_{\eta+\delta}(\psi_t)\le vt+(b+A_+)}                        \tag{12}
\]

for every `t>=0`.  Consequently `(7)` and `(12)` give a two-sided linear ramp, with explicit
additive boundary layers and possibly different operational error budgets.

### Proof

Compose a `b`-gate preparation of `chi` with a simulator for `U_t`.  The errors add and the word
lengths add, proving `(12)`.

## Theorem C -- endpoint count and replica order

For a geometric skeleton `T_j=T_0q^j` truncated at `T_N<=T_max`, one may take

\[
 N+1\le 2+{\log(T_{\max}/T_0)\over\log q}.                     \tag{13}
\]

Suppose a common quenched Hamiltonian draw is required to satisfy `(6)` at all skeleton times and
that the failure probability at each time is at most

\[
 p_r\le Be^{-\kappa r}                                         \tag{14}
\]

for constants `B>=1`, `kappa>0`.  The union fails with probability at most

\[
 (N+1)Be^{-\kappa r}.                                          \tag{15}
\]

It is therefore enough to take

\[
 r\ge {\log(B(N+1)/\delta)\over\kappa}                         \tag{16}
\]

to obtain the entire continuous ramp with failure probability at most `delta`.  If
`T_max/T_0=exp(O(n))` and `c,q,kappa` are fixed, then `N=O(n)` and

\[
 r=O(\log n+\log(1/\delta)).                                   \tag{17}
\]

### Proof

Equation `(13)` is the elementary count of a geometric progression.  Equation `(15)` is the union
bound, and `(16)--(17)` follow by rearrangement.  Theorem A turns simultaneous endpoint hardness
into the uncountable-time conclusion, so no additional time mesh occurs.

## Full-law assembly and exact surviving open core

Assume the same fixed Hamiltonian also supplies:

1. a robust near-maximal hard block `[T_N,T_N+W]` beginning at the last skeleton time;
2. a later robust return to the easy seed;
3. a time-uniform local observable separating its propagator from Haar randomness.

Then Theorems A and B give growth, item 1 gives the plateau, item 2 gives recurrence, and item 3
proves that maximal complexity coexists with permanent non-Haar locality.  The already proved
static-local plateau, recurrence, and separator theorems provide items 1--3 only at uncontrolled
epochs; they do not yet align the plateau start with a Brown-scale endpoint skeleton.

The exact remaining dynamical target is therefore:

> For one ordinary fixed-strength time-independent local Hamiltonian ensemble, prove simultaneous
> robust hardness at `O(n)` prescribed geometric times up to `Theta(2^n/poly(n))`, and a
> near-maximal continuous plateau beginning at the last time, after one common return excision.

For the ramp part, replica order `O(n)` on a linear Brown mesh is retired.  A reporter with an
`exp(-kappa r)` tail needs only `r=O(log n)` for the complete geometric skeleton.  The prescribed
plateau onset, not interpolation between ramp times, remains the hard fixed-system reuse problem.

## Hostile audit

1. **No endpoint anti-concentration is proved here.**  The theorem is a deterministic transfer,
   not Brown closure.
2. **No monotonicity is assumed or obtained.**  Complexity may fluctuate above the lower envelope.
3. **The skeleton must be quenched.**  Choosing a different Hamiltonian at each `T_j` proves
   nothing about one physical history.
4. **Plateau onset must align.**  A hard block at an uncontrolled much later time leaves a delay
   not covered by the ramp theorem.
5. **Simulation model matters.**  Error budgets, ancillas, gate family, geometry, and simulator
   cost must match the state-complexity definition.
6. **Novelty is not claimed.**  Circuit composition, geometric meshes, and the union bound are
   standard.  New value inside this programme is the exact reduction of the static Brown ramp
   from a linear mesh to a logarithmic-replica geometric skeleton.
7. **Lean closed.**  Theorems A, B and C are formalized in
   `HTGeometry/GeometricSkeletonBrownRamp.lean` on top of the approximate-complexity layer of
   `HTGeometry/ExactPenaltyCircuitBellman.lean`.  See the formalized companion.

