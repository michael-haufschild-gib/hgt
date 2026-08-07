# Canonical cyclic trace law for faithful Sonin principal shells — formalized

- **ID:** `sonin-principal-shell-cyclic-trace`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:**
  `sonin-principal-shell-cyclic-trace.md`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Lean modules

The trace law itself lives in
`formal/GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean`.  Its extension across the
relative ideal, the aperture flag law, the Burnol conductor, the logarithm of position, and the
refinement law are spread over the Sonin stack; the paper card carries the complete
statement-to-declaration table for all 554 named declarations.  The principal chapters are:

| Chapter | Module |
|---|---|
| the cyclic trace `(1)`–`(4)` | `SoninPrincipalShellCyclicTrace.lean` |
| Theorem G, the cyclic extension `(6)`–`(10)` | `SoninPrincipalRelativeCyclicExtension.lean` |
| Theorem G as a characterization | `SoninExtendedTraceUniqueness.lean` |
| Theorem H, the one-sided aperture flag law `(14)`–`(17)` | `SoninApertureExtendedTraceFlagLaw.lean` |
| Theorem J, the concrete Burnol conductor `(18)`–`(19)` | `SoninBurnolLogShellChannel.lean`, with the abstract conductor identities in `SoninBurnolConductorConcrete.lean` and `SoninBurnolConductorReflection.lean` |
| Theorems K and N, the dilation commutator `(20)`–`(23)` and the noncompact defect `(26)` | `SoninBurnolLogShellWeyl.lean` |
| Theorems L and O, the truncations `(24)`–`(25)` and stationarity `(27)` | `SoninBurnolLogBandComparison.lean` |
| Theorem P, band exhaustion and density `(28)`–`(30)` | `SoninBandSupportedDense.lean` |
| Theorem Q, refinement loss `(31)`–`(34)` | `SoninApertureFlagChain.lean`, `SoninFlagChainStrict.lean`, `SoninFlagChainQuantitative.lean` |
| Theorem R, the layer read by the extended trace `(54)` | `SoninApertureLayerExtendedTrace.lean` |
| Theorem S, the four mixed blocks `(57)`–`(59)` | `SoninMixedBlockPolarizationSplit.lean`, `SoninMixedPhysicalBlockNonvanishing.lean`, `SoninMixedFourierBlockNonvanishing.lean` |
| the terminal conductor no-go | `SoninBurnolConductorNoFloor.lean` |
| the completion no-gos and the summability criterion | `SoninBurnolCompletionNoFloor.lean`, `SoninFixedChannelNoFloor.lean`, `SoninChannelAnnulusBound.lean`, `SoninCompletionUnboundedRequirement.lean`, `SoninCompletionEnergyThreshold.lean`, `SoninCompletionSummabilityCriterion.lean` |

## Formal theorem chain

1. `soninLiveWindowCyclicLogWeight` and `soninWindowStateCyclicLogTrace` are the tropical trace
   `(1)`; `soninWindowStateCyclicLogTrace_compose_comm` is the cyclicity `(2)`, and
   `soninWindowStateCyclicLogTrace_eq_of_operator_compactEq` is its Calkin invariance.
2. `soninGramFactorPrincipalCyclicTrace_eq_ite` is the Gram diagonalization `(3)`, and
   `soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient` is the exact unsquared
   von-Mangoldt orbital coefficient `(4)`.
3. Theorem G: `SoninPrincipalRelativeOperator.toOperator_injective` is directness,
   `extendedTrace_ofState` / `..._ofRelative` the two restrictions,
   `toOperator_compose` the product realization, and `extendedTrace_compose_comm` cyclicity of the
   extended trace.  `soninPrincipalRelativeCarrier`, `soninExtendedTraceOn` and
   `existsUnique_soninExtendedTraceOn` make it the *unique* gluing of the two normalizations.
4. Theorem H: `extendedTrace_soninApertureRestrictionDefect_flag` and
   `re_extendedTrace_soninApertureRestrictionDefect_flag_le` give the one-sided flag law, with
   `im_extendedTrace_soninApertureRestrictionDefectPresentation` the reality `(17)`.
5. Theorem J: `evenLogShellChannel` is a nonzero self-adjoint channel commuting with the whole
   cutoff family (`ccmCommutator_evenLogShellChannel_evenIndicatorCutoff`,
   `ccmCommutator_evenLogShellChannel_evenFourierCutoff`, `adjoint_evenLogShellChannel`,
   `evenLogShellChannel_ne_zero`), and
   `pointedCutoffWardTrace_evenLogShellChannel_eq_burnolConductor` reads it as the conductor.
6. Theorems K and L: `evenDilationCLM_mul_evenLogShellChannel_eq_shift` is the exact Weyl relation
   and `norm_evenLogShellChannel_sub_soninBandLogMultiplier_le` the operator-norm approximation of
   the genuine logarithm of position.
7. Theorem N: `not_isCompactOperator_conductorDilationDefect` and
   `not_memSchattenClass_one_conductorDilationDefect` prove the archimedean defect is not
   absorbable by any trace-class counterterm.
8. Theorems O and P: `soninBandLogMultiplier_eq_of_bandSupported` is stationarity on the core,
   `soninBandSupported_logShellUnit` its nonemptiness, and
   `eq_zero_of_inner_bandSupported_eq_zero` its density — so the logarithm of position exists on a
   dense domain as the common value of the truncations.
9. Theorem Q: `soninApertureResidualTrace_chain`, `re_soninApertureResidualTrace_chain_le` and
   `re_soninApertureResidualTrace_chain_eq_iff` give the chain flag law, its subadditivity, and the
   exact equality case `(34)`; `exists_strict_soninApertureResidualTrace_chain` and
   `exists_soninApertureResidualTrace_chain_gap` show the inequality is strict at an actual flag,
   with explicit gap.
10. Theorem R: `soninApertureLayerPresentation` and
    `extendedTrace_soninApertureLayerPresentation` read the aperture layer itself, giving `(54)`.
11. Theorem S: `soninMixedPhysicalBlock_ne_zero`, `soninMixedFourierBlock_ne_zero` and
    `soninApertureCouplingMixedTerms_ne_zero` prove the four mixed polarization blocks do not
    cancel.
12. The completion gate is a quantitative statement, not an open disjunction:
    `bddBelow_soninCompletedPacketValueVar_iff` is an exact summability criterion, and
    `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove` together with
    `tendsto_hsNormSq_soninApertureCoupling_atTop` excludes every completion bounded above on the
    scales.
13. `exists_linear_hsNormSq_soninApertureCoupling` gives the coupling energy a positive slope in
    the scale, so `not_bddBelow_soninCompletedPacketValueVar_of_log_cap` closes every completion
    obeying a logarithmic cap.
14. `evenBurnolConductorChannel` is the full Burnol conductor — logarithm of position plus
    logarithm of frequency, each on its own tower at an independent and arbitrary height —
    self-adjoint by `adjoint_evenBurnolConductorChannel`, and
    `not_bddBelow_soninCompletedPacketValueVar_burnolConductorFamily` proves no completion
    assembled from it restores the floor.  `..._of_sublinear_channel_add` makes the excluded class
    closed under sums and `exists_carrier_halfwidth_schedule` inhabits the schedule's two scale
    conditions, so the no-go is neither an instance nor vacuous.

## Meaning

The identity-displacement logarithmic width is a cyclic trace on the exact faithful zero/live Sonin
normal-state semigroup, not merely on an abstract translation algebra.  It is invariant under
compact congruence, diagonalizes genuine CCM Gram factors, returns the exact unsquared von-Mangoldt
coefficient at every prime power, and extends *uniquely* across the concrete Schatten-1
principal-relative ideal.  The Burnol conductor is realized as a concrete self-adjoint channel whose
dilation commutator is exactly `log r`, converging in operator norm to a genuine logarithm of
position on a dense domain, whose archimedean defect is noncompact.

## Scope

This is the principal cyclic/source-value connector together with its aperture and conductor layers,
and the terminal verdict on the completion: there is no completed lower floor from the Burnol
conductor.  It does not prove RH, and it does not exclude some hypothetical channel family with
Hilbert--Schmidt norms growing linearly in the scale — it shows that the conductor is not one.

## Verification

- `lake env lean` passes on every module named above;
- `#print axioms` on all 554 declarations named by the paper card, and on the 8 of
  `SoninBurnolConductorNoFloor.lean`, returns only `propext`,
  `Classical.choice`, and `Quot.sound`;
- every module is imported by `GaloisForLFunctions.RHTower`;
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration is introduced.

## Remaining frontier

None on this card: every gate is closed, the last one negatively.  What a completion would still
have to be is pinned by `frequently_slope_lt_hsNorm_of_bddBelow` — a channel family whose
Hilbert--Schmidt norms beat a definite positive multiple of the scale infinitely often.  The Burnol
conductor is not such a family, and no other candidate is exhibited in the corpus or in Burnol's
construction, so the weld is retired rather than merely unresolved.
