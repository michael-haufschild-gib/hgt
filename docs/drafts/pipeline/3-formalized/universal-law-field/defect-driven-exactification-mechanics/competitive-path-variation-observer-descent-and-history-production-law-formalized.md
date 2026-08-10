# Competitive path variation and observer descent -- Lean certification

- **ID:** ULF-DDE-2B
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/defect-driven-exactification-mechanics/competitive-path-variation-observer-descent-and-history-production-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCompetitivePathVariation`
- **Status:** [LEAN-PROVED] [UMBRELLA-WIRED] [NO SORRY] [NO ADDED AXIOMS]

## Certified declarations

- `constitutivePathWork`;
- `constitutivePathVariation`;
- `constitutiveEndpointChange`;
- `ConstitutiveClosedPath`;
- `ConstitutivePathConstant`;
- `constitutivePathWork_exact`;
- `constitutiveEndpointChange_eq_zero_of_closed`;
- `two_mul_max_eq_add_add_abs`;
- `two_mul_min_eq_add_sub_abs`;
- `constitutiveConjunctivePathWork_eq_endpoint_add_variation`;
- `constitutiveDisjunctivePathWork_eq_endpoint_sub_variation`;
- `constitutiveCompetitivePathWork_sub_eq_variation`;
- `constitutiveCompetitivePathWork_add_eq_endpoints`;
- `constitutiveConjunctivePathWork_closed_eq_half_variation`;
- `constitutiveDisjunctivePathWork_closed_eq_neg_half_variation`;
- `constitutivePathVariation_nonneg`;
- `abs_subdivision_eq_abs_of_between`;
- `constitutivePathVariation_eq_zero_iff_pathConstant`;
- `constitutiveConjunctivePathWork_closed_eq_zero_iff_pathConstant`;
- `constitutiveConjunctiveTwoCycle_eq_zero_iff_relative_eq`;
- `relativePotential_factorsThroughRange_iff_collapsedTwoCycle_zero`;
- `exists_collapsed_positive_competitive_memory_of_not_factorsThroughRange`;
- `constitutiveConjunctiveWork_add_common_potential`;
- `constitutivePathWork_add`;
- `constitutiveConjunctivePathWork_closed_add_common_potential`;
- `constitutiveConjunctivePathWork_swap`;
- `constitutiveCompetitiveHistoryProductionAndDescent`.

## Certified field law

For every finite path, mandatory maximum and permissive minimum of two scalar-exact work laws split
into the sum of endpoint changes and the positive/negative total variation of the relative
potential. On a closed path, mandatory work is exactly half that variation and permissive work its
negative half. Closed mandatory work vanishes exactly when the relative law is constant on every
path edge.

Lean also certifies the observer law: the relative potential factors through the attained range of
an observer exactly when every observer-collapsed competitive two-cycle has zero work. Failure of
factorization supplies an explicit collapsed pair with strictly positive invisible memory.

Common-potential changes and swapping competing presentations preserve closed mandatory history.
Monotone scalar subdivision preserves local variation.

## Verification

- direct source elaboration passed with
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCompetitivePathVariation.lean`;
- module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`;
- final foreground `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completed 11,420
  jobs;
- forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `native_decide`;
- `#print axioms` on all capstones reports only `propext`, `Classical.choice`, and `Quot.sound`;
- final foreground umbrella audit is recorded in the certification registry.

## Scope

Lean proves the finite path mechanism and exact observer-descent criterion. It does not decide
which competition rule is legal in an application, construct source work laws, solve the
multi-parent minimal-memory problem, explain every RH frontier class, or imply RH.

## Log

- 2026-08-09 -- paper theorem translated exactly; direct elaboration, forbidden-token scan, and
  axiom audit passed; umbrella wiring added.
