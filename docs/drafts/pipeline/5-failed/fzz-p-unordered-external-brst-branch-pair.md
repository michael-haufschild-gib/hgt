# FZZ-P unordered external-BRST branch pair

- **ID:** fzz-p-unordered-external-brst-branch-pair
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** literal external-BRST branch charges in `FZZCigarParityExternalBRSTBranchChargeNoGo`
- **Statement:** Unoriented summation of both cyclic chambers of a nonzero-charge neutral `W⁺W⁻` external branch pair has zero compact current.

## Goal

Test whether the known literal opposite branch factors can produce the missing FZZ-P source orientation after integrating their two compact positions without a physical branch-sheet prescription.

## No-go closure

- **Exact killing theorem/mechanism:** forward and reverse cyclic chambers evaluate to `+(2π i p)⁻¹` and `-(2π i p)⁻¹`, respectively, for every `p ≠ 0`; their sum is exactly zero.
- **Strongest positive survivor:** one selected cyclic chamber has nonzero imaginary current and retains it after multiplication by literal diagonal radial covariance.
- **New insight:** the source obstruction is no longer “find a complex factor.” Literal branch data already gives one. The indispensable missing datum is a physical torus branch-sheet/chamber-selection law; otherwise symmetry cancels it.
- **Status:** dependency-closed Lean formalizations in `FZZCigarParityExternalBRSTOrderedBranchPrimitive.lean`, `FZZCigarParityExternalBRSTOrderedNeutralIntegral.lean`, `FZZCigarParityExternalBRSTOrderedNeutralCrossDepthCurrent.lean`, and `FZZCigarParityExternalBRSTNeutralSymmetrizationNoGo.lean`. Direct audits and required OLeans passed; audited claims use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella build intentionally not run under leaf-only audit policy.

## Log

- 2026-09-21 — closed unordered two-chamber external branch route; branch-sheet survivor retained.
