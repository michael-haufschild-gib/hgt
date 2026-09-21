# PW-B Schwarz real structure of literal CTP boundary source

- **ID:** pw-b-schwarz-ctp-real-structure
- **Stage:** 1-in-progress
- **Type:** HARD OPEN PREMISE
- **Proof chain:** literal cyclic Peierls CTP source → Schwarz real structure → critical-fibre CTP cancellation → normalized cap/lift-defect Ward magnitude → PW partner balance → RH

## Exact target

For unit physical amplitude, transport the closed literal finite-energy response
through the resulting two-branch full-circle ordered CTP field and prove its real
part is invariant under `xiZeroCopyConjEquiv`.
At a critical divisor copy, Lean already proves this is equivalent to
`Re CΣ = 0`.

## Why this is the hard premise

Functional reflection alone swaps `q` with `1-q` and reverses its nonzero
imaginary coordinate; it cannot force a critical-line zero.  The completed
Eisenstein cusp leg has exact conjugation covariance and the divisor has a
multiplicity-exact Schwarz lift, but no corpus theorem transports that real
structure through the literal ordered CTP integral.

## Required proof, not an assumption

1. **Completed energy-to-response part closed:**
   `ThetaCuspHawkingBMModularEnergySchwarz` constructs an anti-linear,
   isometric involution on the literal three-component energy frame and proves
   it preserves `energyDomain`, conjugates the complete forcing vector, and
   transports `WeakSolution`; nonreal-resolvent uniqueness proves
   `weakResponse_conj` without a new premise.
2. Transport circular direct-minus-image kernels and the ordered two-event
   integral; fix the physical phase frame rather than inserting a scalar.
3. Apply the closed critical-fibre equivalence.  Only then attack the separate
   cap/lift-defect magnitude identity with fixed-grade PW imbalance.

## Existing formal boundary

- `fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical`
  proves the exact final reduction.
- `weakResponse_conj` formally closes source-to-response Schwarz, via the
  antiunitary energy form, exact forcing-vector covariance, and existing
  nonreal-resolvent uniqueness.
- `cuspLeg_conj` and `xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half` are
  verified ingredients.
- No source-to-PW magnitude identity is claimed here.
