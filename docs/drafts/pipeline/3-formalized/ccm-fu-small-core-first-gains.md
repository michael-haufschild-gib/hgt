# CCM-FU: quotient-local control of first-gain magnitude

- **Stage:** 3-formalized
- **Type:** [BRIDGE], actual-source estimate
- **Parent:** [least-energy envelope extension](../1-in-progress/ccm-fu-greedy-envelope-extension.md).
- **Goal:** Complete signed Abel bound and RH remain open.

## Closed source comparison

Fix an actual processed prime set P and an active unprocessed prime p.
Choose `N>=floor(M/p)+1` and write `S={r in P : r<N}`. Let
`J_p=sum_R F_(M,P)(R+p)^2` over every p-free retained label R. Exact
prime interpolation shows that these child fibres use only the same
processed set at the two adjacent quotient cutoffs. Primes outside S
are inactive at both cutoffs, so every copied child agrees exactly with
its value at S, even when the parent field at P has arbitrary signs.

A contributing child requires `p*product(R)<M`. Distinct prime labels
have distinct positive prime products; at most `floor((M-1)/p)` can
contribute. The existing amplitude theorem at S gives each child square
at most `(9/25)*4^(max(card(S)-1,0))*M`. Hence

`J_p <= (9/25)*4^(max(card(S)-1,0))*M*floor((M-1)/p)`.

The complete signed first gain has its exact pairing
`Delta_p=2*sum_R F_(M,P)(R)*F_(M,P)(R+p)`.
Cauchy--Schwarz bounds its square by four times J_p times the p-free
parent square sum. That parent sum is at most the full actual Q_P.
Therefore

`Delta_p^2 <= (36/25)*4^(max(card(S)-1,0))*M*floor((M-1)/p)*Q_P`.

If `floor(M/p)<=L`, take N=L+1. The core has at most L+1 elements and
the support quotient is at most L. The explicit fixed-depth estimate is

`Delta_p^2 <= (36/25)*4^L*L*M*Q_P`.

These statements have no current-energy, parity or reserve hypothesis.
Current energy is an actual source value retained on the right side.
The estimate is independent of the total number of processed primes.
For states with a quadratic energy ceiling, fixed-depth first gains are
at most of order M^(3/2), with constants depending on that ceiling and L.

## What this leaves to prove

The [mixed-interaction theorem](ccm-fu-small-core-mixed-interactions.md)
already gives order M at fixed quotient depth when p*q>=M. Both first
and mixed gain magnitudes now avoid the growing factor from all of P
in that sector. Absolute magnitude still does not select signs or pay
all steps of a growing order. A least-energy p must satisfy
`Delta_p+Delta_q+E2(P;p,q)<=B-Q_P` simultaneously for every other q.
The all-cutoff selection comparison, unbounded quotient depths, and
overlapping pairs remain open. Complete extension, PE4, SD1 and RH are
not proved by these estimates or by the separate finite experiment.

## Lean surface

`GaloisForLFunctions/RHTower/MobiusDivisorSmallCoreFirstGain.lean` proves:

- `sum_mobiusDivisorPrimeFibre_sq_le_small_core`.
- `sq_mobiusDivisorSelectionEnergy_insert_le_small_core`.
- `sq_mobiusDivisorSelectionEnergy_insert_le_fixed_quotient`.

`MobiusDivisorSmallCoreInteractions.lean` exposes its existing partner
localization proof as `mobiusDivisorSelectionFibre_partner_filter_cutoff`
for use by the new leaf. Its three mixed capstones are unchanged. All
names are in namespace RHTower.

## Validation

Complete scratch proofs and exact-file checks passed without warnings;
only the changed source dependency and new leaf oleans were emitted.
The new module is wired into RHTower.lean. No umbrella build ran.
The three new public theorems and newly exposed partner identity were
axiom-audited once from an external scratch file. All depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No old public capstone
was re-audited. No experimental value or new axiom enters these proofs.

The declaration index refreshed successfully and `scripts/formal_tools.py lint`
passed, with only existing large-file warnings. All owned process handles
ended; the process check found no running Lean/Lake process. Four owned
scratch/log files were removed. The separate RunPod experiment completed,
was downloaded and hash-checked, and its owned files and workers were
cleaned up as documented in its computation record.

The targeted Lake build audit remains incomplete. The prior leaf build
attempt expanded into prerequisite rebuilds despite `--old`; that known
expensive path was not repeated. The successful checks here are exact-file
`lake env lean` checks, not a claimed passing Lake build. This task made
no frontier-map edit; concurrent changes there were left untouched.
