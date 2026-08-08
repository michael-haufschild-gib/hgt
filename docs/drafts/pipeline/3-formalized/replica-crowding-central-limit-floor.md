# Replica crowding central-limit floor

- **ID:** `replica-crowding-central-limit-floor`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [ROUTE-KILLER]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Formalized companion:** `replica-crowding-central-limit-floor-formalized.md`
- **Statement:** Every finite spectral probability law has off-collision
  replica crowding at least its central-bin coincidence mass minus exact
  collisions; hence positive `Z_r` has a universal `delta/sqrt(r)` floor.

## Theorem

Let `I` be finite, let `w_i>=0` with `sum_i w_i=1`, and let `E_i` be real.
Write

\[
 \mu=\sum_iw_i\delta_{E_i},\qquad
 \bar E=\sum_iw_iE_i,\qquad
 \sigma^2=\sum_iw_i(E_i-\bar E)^2.                            \tag{1}
\]

For `r>=1`, let `P_r` be the law of a sum of `r` independent samples from
`mu`.  Define exact collision and strict near-action mass by

\[
 C_r=\sum_xP_r\{x\}^2,
 \qquad
 M_r(\delta)=
 \sum_{0<|x-y|<\delta}P_r\{x\}P_r\{y\}.                      \tag{2}
\]

Then, for every `delta>0`,

\[
 \boxed{
 M_r(\delta)\ge
 {9\delta\over16(\delta+4\sigma\sqrt r)}-C_r.}              \tag{3}
\]

Under maximal projective independence of the energies, `C_r` is exactly the
multinomial permutation floor.  For uniform weights `w_i=1/d`,

\[
 M_r(\delta)\ge
 {9\delta\over16(\delta+4\sigma\sqrt r)}-r!d^{-r}.           \tag{4}
\]

## Proof

Let `S_r=X_1+...+X_r` with the `X_j` independent and distributed by `mu`.
Then `E S_r=r bar E` and `Var(S_r)=r sigma^2`.  Chebyshev gives

\[
 \Pr\{|S_r-r\bar E|<2\sigma\sqrt r\}\ge {3\over4}.          \tag{5}
\]

Partition the interval in `(5)`, whose length is `4 sigma sqrt(r)`, into
`N` half-open cells of diameter strictly less than `delta`, where

\[
             N\le1+{4\sigma\sqrt r\over\delta}.              \tag{6}
\]

Let `b_j` be the `P_r`-mass of the `j`th cell.  By `(5)` and Cauchy--Schwarz,

\[
 \sum_{j=1}^N b_j^2\ge {1\over N}\left(\sum_jb_j\right)^2
 \ge {9\over16N}
 \ge {9\delta\over16(\delta+4\sigma\sqrt r)}.              \tag{7}
\]

If two independent copies of `S_r` lie in the same cell, their difference
has absolute value strictly below `delta`.  Splitting this event into exact
equality and strict nonzero difference gives

\[
             C_r+M_r(\delta)\ge\sum_jb_j^2.                  \tag{8}
\]

Equations `(7)` and `(8)` prove `(3)`.

For a multiplicity vector `p` of mass `r`, its probability is

\[
 a_p={r!\over\prod_i p_i!}\prod_iw_i^{p_i}.                  \tag{9}
\]

Maximal projective independence says equal energies of two mass-`r`
multiplicity vectors force equality of those vectors.  Hence
`C_r=sum_p a_p^2`, the exact permutation floor.  For uniform weights, the
existing factorial estimate `C_r<=r!d^{-r}` inserted into `(3)` proves `(4)`.

The argument also covers `sigma=0`: then `C_r=1`, so the right side of `(3)`
is nonpositive.

## Ordinary local-Pauli consequence

For

\[
 H_n(J)=m_{n,q}^{-1/2}\sum_PJ_PP
\]

with nonidentity Pauli words orthogonal in normalized Hilbert--Schmidt inner
product, the uniform spectral law has mean zero and

\[
                 \sigma_{H_n(J)}^2={\|J\|_2^2\over m_{n,q}}. \tag{10}
\]

Thus every realization with `||J||_2<=2 sqrt(m_(n,q))` and maximally
projective spectrum obeys

\[
 M_r(\delta)\ge
 {9\delta\over16(\delta+8\sqrt r)}-r!2^{-nr}.                \tag{11}
\]

This is quenched: `(11)` holds for each such fixed Hamiltonian, not merely
after ensemble averaging.

## Hostile audit

- `(3)` is a lower bound, not the requested upper anti-concentration law.
- It does not prove Brown--Susskind growth.  It proves that the present
  positive `Z_r` route cannot prove it at Haar scale.
- The `delta/sqrt(r)` order is forced by central-limit geometry and cannot be
  removed by stronger level repulsion: it concerns sums of `r` independently
  sampled levels, not only adjacent levels.
- The conclusion applies to any target whose induced spectral weights are
  uniform.  The identity Choi target has exactly those weights and belongs to
  every circuit dictionary containing the empty circuit.
- Therefore an upper bound that sums positive near-action mass independently
  over all circuit words necessarily charges the same recurrence channel
  repeatedly.  Scalar recurrence must be isolated before the circuit union.

## Mathematical delta

Growing replica order is not the cure for positive near-action crowding.
It creates a universal central concentration floor.  The correct frontier is
signed traceless cancellation after one common scalar recurrence channel has
been removed.

## Gates

- [x] 0 -> 1: well-posed and hostile-tested
- [x] 1 -> 2: complete finite proof above
- [x] 2 -> 3: Lean theorem and axiom audit — see
  `replica-crowding-central-limit-floor-formalized.md`
- [ ] 3 -> 4: manuscript use only after formalization and priority audit

## Log

- 2026-08-06 — Derived central-bin lower bound and local-Pauli specialization;
  killed exponential positive-`Z_r` strategy and isolated scalar recurrence.
- 2026-08-09 — Formalized unconditionally in Lean 4.  `(3)` is
  `fidelityReplicaNearActionMass_crowding_floor`, its `sigma sqrt r` form is
  `fidelityReplicaNearActionMass_crowding_floor_sigma_sqrt`, and `(4)` is
  `fidelityReplicaNearActionMass_microcanonical_floor`.  The variance step
  `Var(S_r) = r sigma^2` is proved combinatorially, without measure-theoretic
  independence, from a multinomial Pascal rule
  (`multinomial_sum_update_pred`) and the resulting amplitude recursion
  (`replicaAmplitudeMoment_succ`).
