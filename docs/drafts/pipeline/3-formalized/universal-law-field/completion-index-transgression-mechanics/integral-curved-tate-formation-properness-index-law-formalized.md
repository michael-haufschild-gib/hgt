# Integral curved Tate formation-properness index law — formalization certificate

- **Paper theorem:** `ULF-ICTFPI-1`
- **Lean module:**
  `GaloisForLFunctions.RHTower.IntegralCurvedTateFormationPropernessIndex`
- **Direct Lean check:** passed
- **Targeted build:** passed
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Certified declarations

- `deningerGammaSixXiFiniteFormationLanding_mem_boundary`
- `deningerGammaSixXiFiniteFormationState_escapeFree`
- `deningerGammaSixXiPhysicalFormationState_escapeFree_iff`
- `tendsto_deningerGammaSixXiFiniteFormationLanding`
- `deningerGammaSixXiFiniteFormationState_tendsto_iff`
- `deningerXiIntegralCofinalFormationIndex_eq_zero_iff`
- `deningerGammaSixXiFiniteFormationState_tendsto_iff_index_zero`
- `deningerGammaSixXiGreenBoundary_mem_formationCompletionBoundary_iff_index_ne_zero`
- `thetaXiPrimeModularCompactRecurrenceDescent_iff_index_zero`
- `deningerXiIntegralCofinalFormationIndex_fusion`
- `forall_deningerGammaSixXiFiniteFormationState_tendsto_iff_riemannHypothesis`
- `forall_deningerXiIntegralCofinalFormationIndex_eq_zero_iff_riemannHypothesis`

They prove ordinary Hilbert-graph convergence of literal finite Xi formation landings at every
grade, but source-marked provenance convergence exactly at zero integral completion index. The same
index detects completion-born vertical homology and failure of compact recurrence descent. The
topology records fixed-marker survival, not a compatible family of boundary primitives. The
universal convergence statement is equivalent to RH; the module does not assume or prove a source
properness law.
