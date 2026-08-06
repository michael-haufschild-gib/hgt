# Traceless replica sector cancellation law

- **ID:** `traceless-replica-sector-cancellation-law`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NEW MECHANISM]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Statement:** At every positive replica order, every signed sector of a
  traceless static-Choi target is exactly the negative of its complement.

## Universal algebraic theorem

Let `I` be finite and let `c_i in C`.  For every multiplicity vector `p` of
mass `r`, put

\[
 A_p(c)={r!\over\prod_i p_i!}\prod_i c_i^{p_i},
 \qquad B_{p,q}(c)=A_p(c)\overline{A_q(c)}.                  \tag{1}
\]

For an arbitrary relation `S(p,q)`, define its signed replica mass

\[
                \mathcal M_S(c)=\sum_{S(p,q)}B_{p,q}(c).     \tag{2}
\]

The multinomial theorem gives

\[
 \sum_{p,q}B_{p,q}(c)
 =\left|\sum_i c_i\right|^{2r}.                             \tag{3}
\]

Hence, if `r>0` and `sum_i c_i=0`, then for every `S`,

\[
 \boxed{\mathcal M_S(c)=-\mathcal M_{S^c}(c).}              \tag{4}
\]

No positivity, probability normalization, energy assumption, or special
choice of sector is used.

## Static-Choi specialization

For a finite static Hamiltonian with spectral basis `E_i`, decompose every
Choi target as

\[
 u=\langle a(0),u\rangle a(0)+u^\circ,
 \qquad \langle a(0),u^\circ\rangle=0.                      \tag{5}
\]

Its complex diagonal spectral coefficients are

\[
 c_i^\circ=d^{-1/2}u^\circ_{ii}.                            \tag{6}
\]

The formal development proves `sum_i c_i^circ=0`; therefore `(4)` applies to
every sector of the replicated action spectrum.  In particular it applies
when `S` is the strict near-action window

\[
             0<|(p-p')\cdot E|<\delta.                      \tag{7}
\]

Near-action, exact-collision, and far-action contributions are not
independent positive errors.  After scalar recurrence is removed, they are
parts of one exact signed cancellation identity.

## Why this moves the frontier

Previous shortcut bounds replaced each complex coefficient by its absolute
value and obtained the positive partition `Z_r`.  The companion
central-limit floor shows that `Z_r` cannot decay at Haar scale because it
contains common identity recurrence.  Equation `(4)` identifies the missing
structure after that channel is removed: tracelessness forces cancellation
at every replica order, for every possible near/far cut.

What remains hard is quantitative, not algebraic: prove that the quenched
local-Hamiltonian ensemble distributes the two cancelling sectors so their
finite-window remainder has Haar-scale size uniformly over shallow circuits.

## Lean certificate

Modules:

- `HTGeometry/TracelessReplicaCancellationLaw.lean`
- `RHTower/ScalarRecurrenceTracelessCircuitSplit.lean`

Core declarations:

- `complexReplicaMultiplicityAmplitude`
- `sum_complexReplicaMultiplicityAmplitude_eq_sum_pow`
- `complexReplicaPairAmplitude`
- `sum_complexReplicaPairAmplitude_eq_normSq_sum_pow`
- `complexReplicaSectorMass`
- `complexReplicaSectorMass_add_complement`
- `complexReplicaSectorMass_eq_neg_complement_of_sum_eq_zero`
- `staticChoiTracelessSpectralCoefficient`
- `sum_staticChoiTracelessSpectralCoefficient_eq_zero`
- `staticChoiTracelessReplicaSectorMass_eq_neg_complement`

Verification:

- both owning modules pass `lake env lean <file>`
- core axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`
- RHTower umbrella reaches the specialization

## Hostile audit

- Multinomial identity is classical; it is not itself a new combinatorial
  theorem.
- New content is the exact quotient-and-sector formulation for static-Choi
  recurrence and its consequence that positive `Z_r` is the wrong variable.
- Equation `(4)` supplies no quantitative cancellation rate.  Large sector
  masses can cancel each other exactly.
- No Brown--Susskind growth, plateau height, recurrence time, or ensemble
  anti-concentration is claimed from this theorem alone.

## Gates

- [x] 0 -> 1: exact law and falsifiers fixed
- [x] 1 -> 2: dependency-closed proof
- [x] 2 -> 3: Lean proof and axiom audit
- [ ] 3 -> 4: requires quantitative quenched signed-sector theorem

## Log

- 2026-08-06 — All-order sector/complement cancellation proved abstractly
  and specialized to the orthogonal static-Choi residual.
