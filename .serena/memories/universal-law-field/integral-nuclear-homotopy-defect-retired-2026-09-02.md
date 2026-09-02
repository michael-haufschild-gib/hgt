# Integral-nuclear prime-mixed homotopy defect: final split (2026-09-02)

ULF-INHD-001 remains retired at `docs/drafts/pipeline/5-failed/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`.

## Exact verdict

No single bounded finite-core completion operator can be simultaneously pre-divisor, prime-mixed, integral, and nuclear with the required RH-closing bounds.

- Source survivor: `RoutePPrimitiveBurnolBaseNuclearSynthesis` constructs the unscaled literal all-prime Hilbert-Schmidt synthesis and covariance
  `S_base = A_base A_base^*`; it is Schatten-1 and `Re Tr S_base = B_base < 1`.
- Target survivor: `IntegralNuclearRelationIncidenceHorizon` constructs, after a strict-right Xi copy is supplied, the incidence-reduced rank-one horizon projector `T_q`; it is Schatten-1 with `Tr T_q = ||T_q||_1 = 1`.
- Bounded landing from finite horizon defects is impossible: finite defects vanish on the dense arithmetic core, so every bounded/contractive coherent extension is zero.
- Singular landing may retain the completion-born horizon, but then cannot inherit the Hilbert-Schmidt source budget.
- Relation-valued and weighted-topology alternatives are already classified as nonselective/full-vertical or scalar-ray admitting.

Thus there is no theorem identifying `S_base` and `T_q`; doing so is the missing RH statement itself. Maximal honest object is the non-liftability pair/square, not one operator.

## Formal status

Both new modules are wired into `GaloisForLFunctions.RHTower`. Targeted builds pass. Axiom audit gives only `propext`, `Classical.choice`, `Quot.sound`. Global lint has unrelated current failures from other un-wired RHTower/HTGeometry modules; touched files pass diff-check. Do not restore ULF-INHD-001 to Stage1 or reintroduce the obsolete `1/sqrt 2` normalization.

Future mechanism must change the finite arithmetic relation/topology before completion, act nontrivially at finite level, and establish a native sub-unit norm estimate.