# TG C9.29 — fixed physical meromorphic current continuation fails

- **ID:** TG-C9.29-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/tg-principal-polar-operator-cancellation.md
- **Statement:** The complete native von Mangoldt prime–polar current cannot have a meromorphic continuation on a fixed physical L2 carrier to any half-plane extending into negative damping.

## Failed conjecture

There exist b>=0, c<0 and a SoninL2-valued meromorphic F on Re z>c agreeing
with the literal current V_b throughout its absolute-convergence half-plane
Re z>1/2. An operator-valued version requires O(z)f0=V_b(z), for the literal
indicator f0 of [-1,1]. Both statements are false unconditionally.

## No-go closure

- **Exact killing theorem:** `RHTower.not_exists_meromorphic_soninDampedPrimePolarCurrentFrom` and `RHTower.not_exists_meromorphic_soninDampedCurrentOperatorFrom`, in `SoninDampedCurrentMeromorphicObstruction.lean`. The proof continues differences of two actual physical probes, then contradicts the genuine Hardy-zero pole. It does not assume a continued row at the negative point.
- **Strongest positive survivor:** The norm-admitted all-prime-power, two-leg physical current satisfies the exact formula `w ell_w(V_0(z))=-R(z+w-1)-R(z)` on Re z, Re w>1/2. Every finite lower polar segment is an entire physical vector, and its precise correction is retained for V_b. These are source formulas derived through the actual strong sum and integral, not a restated negation or scalar-probe construction.
- **New insight:** The expanding leg cancels between two continuous head probes before meromorphic uniqueness is applied. It therefore cannot hide the moving Hardy-zero obstruction. Changing the literal lower endpoint adds an entire physical vector and cannot repair this failure.
- **Status:** Paper proof dependency-closed; both production leaves pass final foreground `lake --old env lean` audits. All 27 public declarations pass a separate API/transitive axiom audit, with only propext, Classical.choice and Quot.sound. Imports wired; index refreshed. Final lint status is recorded on the positive card.

Positive theorem, complete argument and audit log:
`../3-formalized/tg-native-damped-current-carrier.md`.

## Scope

This retires only the fixed physical meromorphic half-plane continuation of
the current. It does not retire TG, refute RH, settle the original logarithmic
source's zero-damping boundary, or rule out a varying carrier or relative
quotient. Signed Q cancellation, completed Hardy compatibility and strict
sub-unit control remain open. No numerical experiment, hole, new axiom or
heartbeat override was used.

## Log

- 2026-10-04 — Exact current source formula and full meromorphic-family obstruction formalized together; strongest positive survivor retained.
