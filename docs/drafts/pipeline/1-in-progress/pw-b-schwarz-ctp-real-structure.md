# PW-B Schwarz real structure of literal CTP boundary source

- **ID:** pw-b-schwarz-ctp-real-structure
- **Stage:** 3-formalized (closed source-real-structure premise)
- **Type:** DISCHARGED BRIDGE
- **Proof chain:** literal cyclic Peierls CTP source → Schwarz real structure → critical-fibre CTP cancellation → normalized cap/lift-defect Ward magnitude → PW partner balance → RH

## Exact target

For unit physical amplitude, transport the closed literal finite-energy response
through the separately glued smooth field and resulting two-branch full-circle ordered CTP field, prove its Schwarz
real structure, and derive `Re CΣ = 0` on the critical fibre.

## Why this is the hard premise

Functional reflection alone swaps `q` with `1-q` and reverses its nonzero
imaginary coordinate; it cannot force a critical-line zero. This was the
obstruction. The new CTP theorem supplies the missing conjugation invariance
of the literal ordered integral, so the existing critical-fibre iff now forces
the cancellation.

## Required proof, not an assumption

1. **Completed energy-to-response part closed:**
   `ThetaCuspHawkingBMModularEnergySchwarz` constructs an anti-linear,
   isometric involution on the literal three-component energy frame and proves
   it preserves `energyDomain`, conjugates the complete forcing vector, and
   transports `WeakSolution`; nonreal-resolvent uniqueness proves
   `weakResponse_conj` without a new premise.
2. **Closed through the literal CTP pair:** `fullCircleSourcePairDensity_conj`
   transports both actual time legs, physical rates, and the direct-minus-image
   kernel. `fullCircleCrossBranchCausalPair_conj_unit` transports both ordered
   product integrals; branch completion preserves it.
3. **Critical cancellation closed:**
   `fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_on_critical` applies
   the previously formalized exact iff with no scalar phase insertion.
4. Remaining hard theorem: normalized cap/lift-defect magnitude identity with
   fixed-grade PW imbalance; it must yield partner balance, then RH.

## Existing formal boundary

- `fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical`
  proves the exact final reduction.
- `weakResponse_conj` formally closes forcing-to-weak-response Schwarz, via the
  antiunitary energy form, exact forcing-vector covariance, and existing
  nonreal-resolvent uniqueness.
- `globalResponse_conj`, `fullAngularField_conj`, and `angularDirichletKernel_conj`
  formally close the separately glued angular source field and its literal
  direct-minus-image circular kernel.
- `D4BMJointSource.timeReducedCoefficient_conj` formally closes the complete
  residual time source, including the differentiated onset term.
- `cuspLeg_conj` and `xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half` are
  verified ingredients.
- `ThetaCuspHawkingBMFullAngularCTPSchwarz` and
  `ThetaCuspHawkingBMFullAngularCTPCriticalCancellation` formally close the
  literal unit-amplitude CTP real structure and critical cancellation.
- No source-to-PW magnitude identity, partner balance, or RH is claimed here.
