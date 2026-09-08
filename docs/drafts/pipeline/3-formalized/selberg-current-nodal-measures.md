# Actual current and residual measures from the Maass curvature split

- **ID:** SELBERG-CURRENT-NODAL-MEASURES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Source-current candidate](../1-in-progress/selberg-original-source-conserved-currents.md), [proved pointwise split](selberg-pair-phase-current-curvature.md), Selberg cycle 40 continuation.
- **Statement:** The actual positive current-limit and residual measures sum to the original source curvature measure; the residual is the actual weak limit of the regulator-gradient term and is concentrated on the literal common-zero set.

## Dependency-closed paper proof [PROVED HERE]

Fix an original congruence Maass source f with any real eigenvalue lambda. Its actual source density is D, current-square numerator is C, and gradient density is G. The original formula is kappa_e=C/R_e³+e²*G/R_e³, with R_e²=D+e² and e>0. Both summands are nonnegative. Source C² regularity proves local continuity of C and G, and positive R_e proves local continuity of the regulated current weight. Every admissible compact continuous test therefore has genuinely integrable current and full curvature pairings.

Write I_e(phi)=integral(phi*C/R_e³). Since C>=0 and the positive radius increases with e, the current weight is antitone in e. For phi>=0, I_e is antitone. Fix e and compare at all smaller positive regulators a: I_e<=I_a<=integral(phi*kappa_a). The last quantity has the already proved original curvature limit L(phi). Passing to that limit proves I_e<=L(phi), for every e. The range of I_e is thus bounded above. If t is below its supremum, some I_e exceeds t and every smaller-regulator value does too; all values lie below the supremum. This proves convergence to the finite supremum along the actual positive-regulator filter, without interchanging a pointwise limit and an integral.

For signed phi, use the exact decomposition phi=(phi+|phi|)-|phi|. Both terms are nonnegative continuous compact tests supported in the same original upper-half-plane region. Actual integral additivity proves that I_e(phi) has a finite limit too. Let J be that limit on zero-extended compact upper-half-plane tests. Uniqueness of limits proves real linearity; nonnegative-test limits prove positivity. The comparison above gives J(g)<=L(g) for g>=0, so L-J is also a positive linear functional.

Riesz--Markov constructs regular measures mu_current and mu_residual representing J and L-J on the actual upper half-plane compact-test space. Both are finite on compact sets. Their sum is finite on compact sets by adding the two finite compact masses; on the actual metrizable sigma-compact upper half-plane this gives regularity. Integration against the sum equals L on every compact continuous test, so the original curvature-measure uniqueness theorem proves

`curvatureMeasure = currentMeasure + residualMeasure`.

The pointwise source splitting, multiplied by each zero-extended test, is valid at all positive-height points and vanishes outside the test support. Both full and current pairings are integrable, so their difference proves integrability of the literal regulator-gradient pairing. Its integral is exactly their difference. Subtraction of the proved regulator limits therefore gives

`integral(phi*e²*G/R_e³) -> integral(g d residualMeasure)`

for every actual compact upper-half-plane test g and its zero extension phi. The residual is an actual source limit, not a measure chosen only to satisfy an endpoint equation.

Now suppose the compact test support lies where D>0. Continuity and the extreme value theorem give a positive minimum d of sqrt(D) on the support of its zero extension (for empty support choose any d>0). Hence R_e>=d there for every e. The actual source bound is

`|integral(phi*e²*G/R_e³)| <= (e²/d³)*integral(|phi|*G)`.

The rightmost integral is genuinely finite by local source gradient continuity and compact support; d is derived from that same test and source. The bound tends to zero. Comparison with the actual residual-measure limit proves that mu_residual annihilates every compact continuous test supported where D>0.

The positive-density locus V is open by original source continuity. For every compact K contained in V, the compact cutoff theorem supplies a nonnegative compact continuous g, equal to one on K, supported in V. Its residual integral is zero, while positivity gives mu_residual(K)<=integral(g)=0. Regular inner approximation of V by its compact subsets now proves mu_residual(V)=0. Since D>=0 for the actual source, V is precisely the complement of its literal common-zero set. Thus

`residualMeasure {z | density N f z = 0}ᶜ = 0`.

No nodal contribution has been discarded. No nonvanishing source premise, uniform amplitude floor, lift, entropy estimate, or quarter lower comparison was added. Test-support conditions in intermediate lemmas are discharged by the cutoffs in the final source-measure theorem.

## Corpus evidence

The explicit OR discovery for measure domination, density limits, Fatou, and nodal mechanisms reached 570 declarations in 94 modules. Earlier inspected `SelbergNodalCurvature.nodal_curvature_survives_integration` prevents discarding nodal mass. The original `SelbergMaassContinuousCurvature` constructs actual continuous-test curvature limits; `SelbergMaassCurvatureMeasure` represents them by a regular measure. `SelbergMaassRegulatorMass.weightedMassDensity_antitone` supplies a source-level monotonicity mechanism from the ordered positive square roots. The current term requires its own proof, not a claim of pointwise monotonicity of the full curvature.

Further OR discovery for monotone limits, positive functionals, supremum limits, and measure sums reached 104 declarations in 19 modules (`/tmp/selberg_monotonefunctional41_discovery.json`). Inspected `Bottcher.Brolin.FiniteLimits.limitingBrolinRieszFunctional`: its positive functional uses actual compact-test integrability, while its remaining distributional identification is kept separate. Here the regulator-gradient identification is proved from the actual Maass split before claiming a source residual measure. Mathlib's compact cutoff, regular-measure uniqueness, positive-functional construction, and ordered supremum APIs were inspected and checked in this toolchain's scratch files.

## Gates

- [x] Well-posed original-source candidate; scalar and nodal failure mechanisms retained.
- [x] Actual current regularity, integrability, monotonicity, and compact-test bound.
- [x] Signed-test limits and positive functional split.
- [x] Actual regular measure construction and exact sum.
- [x] Residual measure concentrated on the original common-zero set.
- [ ] Final serialized build, axiom, index, and repository lint audit.

## Lean modules and audit

All modules are under `formal/GaloisForLFunctions/RHTower/` and wired exactly once into its umbrella.

| Module | Public declarations | Main results |
|---|---:|---|
| `SelbergMaassCurrentTests` | 13 | `currentWeight_antitone`, `testedCurrent_le_limit`, `nonnegative_current_limit`, `exists_testedCurrent_limit` |
| `SelbergMaassCurrentFunctional` | 11 | `current_limit`, `currentPositiveFunctional`, `residualPositiveFunctional`, `functional_sum` |
| `SelbergMaassCurrentMeasures` | 16 | `curvatureMeasure_eq_add`, `current_limit_integral`, `regulator_limit_integral` |
| `SelbergMaassResidualSupport` | 7 | `exists_amplitude_floor`, `regulator_limit_zero`, `residualMeasure_compl_node_zero` |

The total is 47 public declarations, including four measure instances, and two private helpers. Complete scratch checks and needed source oleans passed without warnings. Scratch files are `/tmp/selberg_{currenttests,currentfunctional,currentmeasures,residualsupport}41.lean`. Name checks are `/tmp/selberg_{currenttests,currentfunctional,residualsupport}41_names.lean`.

The sum-measure proof explicitly establishes finite mass on every compact before invoking regularity. No nonexistent additive regularity instance is assumed. The final support proof uses the ENNReal supremum-zero identity to avoid an order-instance mismatch. These fixes changed proof elaboration, not the mathematical statement.

## Remaining Selberg frontier

This is an exact positive split with a proved nodal residual. Absolute continuity of the current measure and its explicit unregularized density have not yet been proved here; do not call this a full Lebesgue decomposition. Separate modular covariance/descent and quantitative control of both contributions remain relevant next tests. The exact measure split alone supplies no congruence-uniform quarter comparison. The full Selberg goal and the parent source-current route remain active and unproved.

New broad OR discovery across coarea, isoperimetry, nodal length, and Cheeger mechanisms reached 564 declarations in 68 modules (`/tmp/selberg_currentnodalbudget41_discovery.json`). Inspected `FormationStokesFolnerSelection`: the boundary-capacity inequality requires the actual finite packet's constant bulk divergence and edge-current bound, both explicit fields of its source structure. Inspected `ReciprocalCoareaOptimality`: its optimized shell cost is tied to a specified cofactor-shell certificate, not an already identified Maass nodal cost. These suggest testing actual source flux/capacity or shell laws; neither supplies a uniform source comparison by renaming the new measures.

## Log

- 2026-09-08 — Candidate recorded before source-measure proof work. Selberg remains active and unproved.
- 2026-09-08 — All four source modules passed complete scratch and needed-source checks; exact positive measure split and nodal support proved. Final audits in progress.
