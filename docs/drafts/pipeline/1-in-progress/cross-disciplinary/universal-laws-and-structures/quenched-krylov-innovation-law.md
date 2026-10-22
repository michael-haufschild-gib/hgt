# Quenched Krylov innovation law

- **ID:** `quenched-krylov-innovation-law`
- **Stage:** 1 — in progress
- **Type:** FROZEN CONJECTURE / BROWN--SUSSKIND OPEN CORE
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR EXTRACTED] [NOT A PAPER CLAIM]`
- **Parent:** `static-local-complexity-law.md`
- **Date:** 2026-08-06

## Public sentence

An autonomous local Hamiltonian does not receive fresh random couplings as it
runs.  It receives fresh *operator directions*: successive Krylov innovations
spread the same finite disorder through an exponentially growing Pauli
alphabet, until the finite Hilbert space is exhausted.

## Ontological reversal

The missing primitive is not spectral chaos, a design time, or independent
noise at each instant.  It is the **innovation volume of the self-normalized
Krylov flag**.  A fixed local Hamiltonian reuses the same coefficient vector,
but multiplication by that Hamiltonian opens new noncommutative Pauli
directions.  Local growth, Haar-scale plateau behaviour, and finite spectral
saturation are proposed to be three ranges of this one innovation volume.

This is not “a local ensemble plus a sharper anti-concentration hypothesis.”
It identifies what the randomness is acting on: not eigenvectors directly,
but the new quotient exposed by each orthogonalized polynomial of the same
Hamiltonian.

## Frozen conjecture

Let

\[
 H_{n,q}(J)=m^{-1/2}\sum_{1\leq |P|\leq q}J_PP,
 \qquad J_P\stackrel{\rm iid}{\sim}N(0,1),\qquad q\geq2,
\]

on `n` qubits, with `m` nonidentity Pauli coefficients and `d=2^n`.
Condition on the coefficient direction, equivalently on a fixed interaction
rate.  Let `Q_1(H),...,Q_K(H)` be the orthonormal traceless Krylov innovations
obtained from `H,H^2,...,H^K` in normalized Hilbert--Schmidt norm.  For a
normalized unitary target `U`, put

\[
 \Gamma_K(H,U)=\sum_{k=1}^K
   |d^{-1}\operatorname{Tr}(U^*Q_k(H))|^2.              \tag{1}
\]

This is exactly the squared scalar-removed Krylov-carrier norm of the target's
diagonal Choi restriction.

Define the reachable Pauli volume

\[
 M_{n,q}(K)=\sum_{j=1}^{\min\{qK,n\}}3^j{n\choose j},   \tag{2}
\]

and cap it by the full nonidentity operator dimension `d^2-1`.  Let
`C_(n,s,epsilon)` be a canonically resolved, `epsilon`-separated family of
distinct Choi endpoints of circuits of at most `s` gates over a fixed finite
universal two-qubit alphabet.  The conjecture is that there are constants
depending only on `q`, the gate alphabet, and fixed resolution such that,
simultaneously in the pre-capacity range and for the stated admissible growing
replica orders,

\[
 \boxed{
 \sum_{U\in C_{n,s,\epsilon}}\Gamma_K(H,U)^r
 \leq
 \exp(C s)\left(
   {C rK\over \min\{M_{n,q}(K),d^2-1\}}
 \right)^r }
                                                               \tag{QKI}
\]

outside coefficient-direction mass `exp(-c m)`.  “Admissible” is part of the
frozen assertion: it must include the replica orders needed to make the right
side smaller than the scalar-removed capture threshold whenever
`s < c K log(min(M,d^2)/K)`; it may not be chosen after a proof route is
found.

Combined with the already proved factorial Krylov remainder, `(QKI)` predicts
ballistic no-shortcut growth until `K` reaches spectral capacity.  At
`qK>=n`, `(2)` saturates at the full Pauli alphabet, so the same law predicts
the Haar-scale plateau without asserting that the local ensemble is Haar.
At the exact finite-spectrum boundary the Krylov flag saturates and the
separate spectral recurrence law takes over.

## Why the hunch is informed

| Existing result or failure | Shadow of `(QKI)` |
|---|---|
| Exact scalar/traceless split | `Q_0=I` is not an innovation and must be charged once as recurrence. |
| Universal CLT floor for positive `Z_r` | Positive near-action counting mixes `Q_0` back into every target; `(QKI)` removes it before replication. |
| Krylov causal factorial sieve | Dynamics outside the first `K` innovations is uniformly small for `K` above the action horizon. |
| Exact Pauli connected-walk expansion | Multiplication by `H` opens only Pauli directions reachable by local products, giving `(2)`. |
| All-replica local Pauli Hall expansion | Apart from permutation modes, local words have no exact replicated invariant carrier preventing innovation. |
| Planar cavity fixed modes | Identity/permutation sectors are precisely the non-innovating modes removed or charged separately. |
| One-local linear-span no-go | Linear span can saturate in `O(n)` steps; `(QKI)` concerns normalized coefficient mass, not span. |
| Rare gapped easy boxes | They are allowed inside the `exp(-cm)` exceptional set; an annealed high moment would incorrectly amplify them. |
| Permanent locality/Haar separator | Innovation volume may reach Haar overlap scale while the generator labels remain permanently observable. |

## Risky predictions

1. **Exact first-layer scale.**  For `K=1`, scalar removal turns `(1)` into
   the squared correlation of the Gaussian coefficient direction with the
   target's local Pauli coefficient vector.  Its order-`r` moment is bounded
   by

   \[
    {2^r r!\over m(m+2)\cdots(m+2r-2)},                 \tag{3}
   \]

   uniformly over every normalized target.  Thus the first layer sees `m`,
   not `d^2`.
2. **Locality-to-Haar crossover.**  Innovation volume grows with Pauli word
   radius and reaches `d^2-1` once `qK` reaches system size, even though the
   Hamiltonian ensemble still has only `m=O(n^q)` independent coefficients.
3. **Quenched/annealed split.**  `(QKI)` can hold at replica orders for which
   its raw ensemble expectation fails, because rare coefficient caps dominate
   annealed high moments after `r` reaches order `m`.
4. **Integrable failure.**  `q=1` and commuting subfamilies must violate the
   innovation-volume growth before full Pauli saturation; the failed quotient
   identifies their fast-forwardable carrier.

## Hostile falsifiers

The conjecture is false if any of the following occurs outside mass
`exp(-cm)` in the stated range:

1. a noncommuting fixed-`q` carrier keeps a positive fraction of a new Krylov
   mode on `o(M_(n,q)(K))` Pauli directions;
2. Gram--Schmidt self-normalization coherently amplifies rare Pauli walks
   enough to beat `(QKI)`;
3. a resolved low-circuit family tracks those amplified directions with load
   larger than the circuit-entropy term;
4. the first-layer formula `(3)` fails for complex target coefficients;
5. a known simulation circuit enters below the claimed useful threshold;
6. Krylov saturation at `K=d-1` contradicts the asserted `d^2` operator-space
   scale.

The sixth attack does not immediately kill the conjecture: the saturated
spectral diagonal has dimension `d`, but a generic unitary target has only
order `d^{-1}` total diagonal Choi mass, so its per-direction Hilbert--Schmidt
scale remains `d^{-2}`.  This explanation is not a proof.

## First attack programme

1. Prove `(3)` exactly, including the complex two-real-dimensional target
   plane and the scalar-removed static-Choi normalization.
2. Compute and classify the complete `K=2` quotient: identity, first layer,
   commuting quadratic products, and genuinely new Pauli directions.
3. Replace raw monomials by orthogonal Krylov innovations before Wick
   expansion; test whether planar self-energy cancels in the quotient.
4. Prove or falsify a one-step conditional innovation inequality.  Iteration,
   not an assumed design theorem, must produce `(QKI)`.
5. Only after the mathematical statement survives, audit external priority.

## Paper boundary

`(QKI)` is false and is not authorized for any manuscript.  Only its exact
first-layer identity and the lag-resolution requirement below survive.

## Falsification

The first attack already kills `(QKI)` for two independent reasons.

First, Krylov carriers are nested.  A one-local Pauli target has order-one
carrier mass of order `1/m` under the Gaussian Pauli ensemble.  That same
mass remains inside every order-`K` carrier.  Hence the total carrier cannot
obey a bound whose scale is replaced by the much larger reachable volume
`M_(n,q)(K)`.  The conjecture confused the newest innovation with the entire
nested flag.

Second, and decisively for Brown--Susskind growth, carrier norm has forgotten
*when* a target is reached.  If a circuit dictionary contains a target which
captures the orbit at an earlier easy time `s`, the already proved
scalar-removed capture theorem gives

\[
 \left(\sqrt{1-\epsilon^2}-\rho-
 {B^{K+1}|s|^{K+1}\over(K+1)!}\right)^{2r}
 \leq \mathfrak L_{K,r}^{\circ}                         \tag{4}
\]

whenever the scalar return at `s` is below `rho`.  For `K` chosen for a much
later horizon, the factorial term at `s` is tiny, so the right-hand load is
forced close to one.  This remains true even when the overlap between that
past target and the late orbit is tiny.  Therefore a static upper bound on
`mathfrak L_(K,r)^circ` cannot certify late-time circuit hardness after the
dictionary contains any resolved earlier orbit segment.

This is not a constants problem, an annealed/quenched problem, or a missing
Pauli estimate.  It is an invariant mismatch: norm compression onto an
unoriented Krylov flag discards temporal phase.

## Positive survivor: lag-resolved innovation

Any viable theorem must retain target time orientation.  A shortcut at time
`t` which is close to an easy earlier orbit point at time `s` must be charged
once to the spectral return at lag `t-s`; it must not be charged as a large
time-independent carrier norm.  Only targets transverse to the complete
resolved easy-past orbit tube may enter the replicated anti-concentration
term.

Thus the next admissible object has two coordinates,

\[
 \mathfrak A_{K,r}(t,s;H,\mathcal C),                    \tag{5}
\]

with the covariance rule that an orbit target at `s` contributes exactly the
return kernel at `t-s`.  Summing `(5)` over targets before preserving the lag
is forbidden.  The required law is a nonlinear dichotomy:

1. **longitudinal branch:** target lies in the resolved easy-past orbit tube,
   and capture is a genuine lag recurrence;
2. **transverse branch:** target is separated from that tube and pays a
   selector-safe growing-replica bound.

Equation `(4)` is Lean-proved by
`scalarRemovedKrylovReplicaLoad_ge_of_capture`.  The exact first-layer
directional identity is Lean-proved in
`HTGeometry/OneStepKrylovCarrierLaw.lean` and
`RHTower/StaticChoiOneStepKrylovInnovationLaw.lean`.  The lag-resolved
two-branch theorem remains the new open core.
