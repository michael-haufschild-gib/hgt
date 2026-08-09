# Universal-law-field Lean certification boundary

Project rule: **paper proof does not count as proved until its exact significant theorem is closed in
Lean**.  Files remaining in this Stage-2 folder are therefore research claims awaiting certification,
even when their paper argument is dependency-closed.

Dedicated Lean umbrella:
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Certified and promoted to Stage 3

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PIR-1 | Positive doctrine, additive nondescendence, faithful response coframe, recurrence/open lift | `HTGeometry.ConstitutivePositiveResponse` |
| ULF-CFL-1 | Complete passive equivalence versus injective marked intervention | `HTGeometry.ConstitutiveInterventionSeparation` |
| ULF-SLOT-1 | Independent-slot transitivity; invariant phases trivial; invariants constant | `HTGeometry.ConstitutiveIndependentSlotNoGo` |
| ULF-RADIUS-2 | Serial-radius counterexample and hidden-pair/diameter survivor | `HTGeometry.ConstitutiveReconstructionNoGo` |
| ULF-AEEC-1 | Adaptive mimicry, coherent non-effective boundary, finite effectivity-classifier no-go | `HTGeometry.ConstitutiveAdaptiveProcompletion` |
| ULF-AMCC-1 | Minimal adaptive transcript support, universal additive-cost minimizer, exhaustive coercivity | `HTGeometry.ConstitutiveAdaptiveCost` |
| ULF-GCP-1 | Exact response-kernel persistence, Gamma Bockstein death set, critical survival, and lifetime | `HTGeometry.ConstitutiveGammaResponseLifetime` |
| ULF-RBD-PREFIX-1 | Prefix observer stabilization, non-effective horizon, recurrent phase, positive erasure, singleton production, open action | `HTGeometry.ConstitutiveEffectivityHorizon` |
| ULF-RBD-JET-1 | Exact DA/HT finite-jet double realization, mutual density, empty interiors, nonclosed strata, continuous-classifier no-go | `HTGeometry.ConstitutiveFiniteJetBoundary` |
| ULF-REG-KONIG-1 | Locally finite realization tower has a global section; finite-local/global gap requires noncoherence, nonproperness, or extra admission | `HTGeometry.ConstitutiveRealizationKonig` |
| ULF-REG-SEID-1 | Surjective erasure forces infinite dimension; fixed-corona Gamma-Bockstein death has no faithful finite-dimensional linear model | `HTGeometry.ConstitutiveSurjectiveErasure` |
| ULF-HISTORY-1 | Nonnegative additive groupoid costs vanish; complex real-cost part vanishes; directed histories admit nonzero additive cost | `HTGeometry.ConstitutiveHistoryPolarization` |
| ULF-PRD-PUMP-1 | Observer unitization forces recurrence, injective open history, linear action, and cost nondescendence | `HTGeometry.ConstitutiveObserverUnitization` |

Formalized cards and declaration-level records live in
`docs/drafts/pipeline/3-formalized/universal-law-field/`.

## Partially certified, not promoted

`ULF-EQG-1` has a certified local and finite core:

- `HTGeometry.QPochhammer`: q-Pochhammer convergence, shift, nonvanishing; normalized q-Gamma
  translation; positive local weights; mass one; every nonnegative-integral moment;
- `HTGeometry.EulerQGammaFiniteProcess`: finite response/divisor telescopes and genus-one exchange.

Its global prime probability, zeta ladder, meromorphic divisor, hypertranscendence, and recurrence
claims remain uncertified.  The card therefore stays in Stage 2.

## Rejected by formal attack

`ULF-DISTORTION-1` claimed monotonicity of internal-centre reconstruction radius under serial
postprocessing.  A Lean-certified three-point counterexample shows strict decrease from two to one.
The rejected card is in `docs/drafts/pipeline/5-failed/universal-law-field/`; ULF-RADIUS-2 records
the exact survivor.
