# Replica-action crowding shortcut law

- **ID:** `replica-action-crowding-shortcut-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / finite-window near-resonance law
- **Status:** `[FORMALIZED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../3-formalized/direct-net-adaptive-static-choi-shortcut-action-law.md`
- **Date:** 2026-08-06

## Exact law

Let `I` be a nonempty finite spectral label set, let `r >= 1`, and let

\[
 \mathcal P_r=\{p:I\to\mathbb N:\sum_i p_i=r\}.
\]

For nonnegative spectral amplitudes `a_i`, put

\[
 u_p={r!\over\prod_i p_i!}\prod_i a_i^{p_i},
 \qquad
 \Omega_p=\sum_i p_iE_i.                                  \tag{1}
\]

Fix `delta>0`.  The order-`r` near-action graph joins `p` to `q` when

\[
 0<|\Omega_p-\Omega_q|<\delta .                            \tag{2}
\]

It is symmetric and loop-free.  Define its maximum degree

\[
 \kappa_r(E;\delta)
 =\max_{p\in\mathcal P_r}
   |\{q\in\mathcal P_r:0<|\Omega_p-\Omega_q|<\delta\}|.   \tag{3}
\]

The permutation floor and exact collision mass are

\[
 B_r(a)=\sum_{p\in\mathcal P_r}u_p^2,
 \qquad
 C_r(E,a)=\sum_{\Omega_p=\Omega_q}u_pu_q.                 \tag{4}
\]

Let `z_i` be arbitrary unit complex twists.  If `sum_i a_i <= 1`, then the
Gaussian scalar-time observer obeys, for every `T>0`,

\[
 \boxed{
 \left|\mathbb E_{X\sim N(0,1)}
   \left|\sum_i a_i z_i e^{iTXE_i}\right|^{2r}\right|
 \le C_r(E,a)+\kappa_r(E;\delta)B_r(a)
      +e^{-(T\delta)^2/2}.}
                                                                  \tag{5}
\]

The centered uniform observer obeys

\[
 \boxed{
 \left|{1\over2T}\int_{-T}^{T}
   \left|\sum_i a_i z_i e^{itE_i}\right|^{2r}dt\right|
 \le C_r(E,a)+\kappa_r(E;\delta)B_r(a)
      +\min\{1,(T\delta)^{-1}\}.}
                                                                  \tag{6}
\]

If the spectrum has maximal projective rational rank, zero action forces
`p=q`, so `C_r(E,a)=B_r(a)`.  For a direct normalized target against the
`d`-level Choi orbit,

\[
 a_i={|\langle i,i|\phi\rangle|\over\sqrt d},
 \qquad \sum_i a_i^2\le {1\over d},
\]

and therefore

\[
 B_r(a)\le r!\,d^{-r}.                                    \tag{7}
\]

Equations `(5)`--`(7)` give the target-uniform bound

\[
 \boxed{
 \text{Gaussian moment}
 \le (1+\kappa_r(E;\delta))r!d^{-r}
       +e^{-(T\delta)^2/2},}
                                                                  \tag{8}
\]

with the analogous uniform remainder.  Markov amplification and adaptive
finite circuit union are formalized with `(8)` replacing the
minimum-action-resolution bound.  No finite-net crowding theorem is claimed
on this card.

## Proof

Expanding the `2r`-th moment gives the pair coefficient `u_pu_q`; twists
have modulus one.  Split the pair set into zero, near, and far action.

The zero-action contribution is exactly `C_r(E,a)`.  On the far part,
the Gaussian characteristic kernel is at most
`exp(-(T delta)^2/2)` in modulus, while the uniform sinc kernel is at most
`min(1,(T delta)^(-1))`.  The total absolute coefficient mass is

\[
 \sum_{p,q}u_pu_q
 =\left(\sum_i a_i\right)^{2r}\le1,                       \tag{9}
\]

so the far contributions give the last terms of `(5)` and `(6)`.

It remains to control the near graph.  For every edge,

\[
 2u_pu_q\le u_p^2+u_q^2.                                  \tag{10}
\]

Sum `(10)` over directed near edges.  Symmetry makes the two square sums
equal, and every vertex occurs at most `kappa_r(E;delta)` times in each.
Consequently

\[
 \sum_{p,q:\,0<|\Omega_p-\Omega_q|<\delta}u_pu_q
 \le \kappa_r(E;\delta)\sum_pu_p^2
 =\kappa_r(E;\delta)B_r(a).                               \tag{11}
\]

Combining the three pieces proves `(5)` and `(6)`.

Under maximal projective rank, equal order and equal energy imply `p=q`,
which gives `C_r=B_r`.  Finally, multinomial domination gives

\[
 \begin{aligned}
 B_r(a)
 &=\sum_p {r!\over\prod_i p_i!}^{\!2}\prod_i a_i^{2p_i}\\
 &\le r!\sum_p {r!\over\prod_i p_i!}\prod_i(a_i^2)^{p_i}\\
 &=r!\left(\sum_i a_i^2\right)^r
 \le r!d^{-r},
 \end{aligned}
\]

proving `(7)`--`(8)`.

## Formalization

Generic graph, moment, and capture-measure laws:

- `formal/GaloisForLFunctions/HTGeometry/ReplicaActionCrowdingShortcutLaw.lean`

Direct normalized Choi targets, adaptive finite dictionaries, and padded
circuit words:

- `formal/GaloisForLFunctions/RHTower/DirectAdaptiveStaticChoiCrowdingLaw.lean`

The final operational theorem is
`gaussian_directAdaptivePaddedCircuitShortcut_crowdingProbability_le`, with
the centered uniform analogue
`uniform_directAdaptivePaddedCircuitShortcut_crowdingProbability_le`.
Both quantify over every finite gate alphabet, circuit depth, positive
replica order, positive observation scale and resolution, and every
capture radius in `[0,1]`.

## Mathematical delta

The parent law charges every nonzero replica action by the single smallest
action.  One isolated tiny action therefore destroys its finite-window
remainder even when that action carries negligible total weight.  The new
law proves that finite-scale failure is controlled instead by local additive
crowding of replica energy sums.  A tiny isolated action costs only one
additional permutation-floor unit.  This replaces a worst-gap invariant by
an optimizable weighted near-resonance profile without losing target
uniformity.

## External priority audit

A 2026-08-06 primary-source search found adjacent but non-identical results:

- Legramandi--Talwar, *The moments of the spectral form factor in SYK*
  (`arXiv:2412.18737`), studies higher spectral-form-factor moments and their
  model-specific deviations from random-matrix statistics.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones, *Saturation and recurrence of
  quantum complexity in random local quantum dynamics* (`arXiv:2205.09734`),
  proves complexity saturation and recurrence for random circuits and
  stochastic Hamiltonian evolution, not one ordinary fixed Hamiltonian.
- Ippoliti, *Provable random-matrix spectral ramp in a static, geometrically
  local Hamiltonian* (`arXiv:2606.30635`), proves a spectral ramp for a
  specially embedded static local family, not an adaptive circuit-shortcut
  bound or a target-uniform near-action crowding law.

No searched source stated the exact maximum-local-degree replica-action bound
or its adaptive full-Choi circuit consequence. This is evidence of separation,
not a complete priority proof; status remains `NOVELTY UNVERIFIED` pending
full-text citation chaining through additive-energy and higher-SFF literature.

## Hostile audit

1. The graph estimate is the finite Schur/AM--GM degree bound; it is not
   claimed as a new graph-theoretic inequality.
2. `kappa_r(E;delta)` can still be large.  No local-Hamiltonian ensemble
   theorem controlling it at growing replica order is proved here.
3. The theorem is a scalar-time finite-window law, not the fixed-time
   quenched coefficient-space anti-concentration required by O4.
4. Maximal projective rank excludes exact nonpermutation collisions but gives
   no quantitative bound on near-action crowding.
5. Scientific novelty, if any, lies only in the target-uniform replica-action
   synthesis and its use as the correct finite-scale obstruction.  Priority
   remains unverified against additive-energy and higher spectral-form-factor
   literature.

## Next open core

Prove a quenched local-Hamiltonian estimate for the crowding profile at the
replica orders required by the circuit union, or prove that excessive
crowding forces a low completed-orbit-capacity stratum.  This is strictly
weaker than controlling the minimum replica action and is the first estimate
that would remove the intrinsic-resolution collapse in the parent theorem.
