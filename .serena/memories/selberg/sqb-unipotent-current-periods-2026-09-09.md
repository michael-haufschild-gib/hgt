# SQB: actual block motions reduced to original current periods

RH UNPROVED. Active unbudgeted goal. Frontier map READ ONLY; no edits. This goal turn made verified progress: complete block-to-current differential identification and exact two-period reduction, with geometric costs explicit. No uniform quotient-area quarter comparison or full-Xi spectral occurrence obtained.

## New audited module
formal/GaloisForLFunctions/RHTower/SelbergMaassUnipotentPaths.lean, 384 lines, 43 public declarations, namespace GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths.
Imports SelbergMaassUnipotentBlocks, SelbergMaassChordEnergy, SelbergMaassCurrentCurvature, SelbergMaassCurrentTransport, Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic.

### Literal source/path bridge
upper_eq_T_zpow; lower_eq_conjugate_upper j: lower j=S*upper(-j)*S^-1 (direct matrix algebra); upper_smul_eq_point j z gives horizontal endpoint Re z+j, Im z.
augmented_chord_modular: simultaneous SL2Z action on two endpoints preserves SelbergMaassAugmentedDirection.distanceSq (Option Deck permutation fixes added e-coordinate).
displacementEnergy_eq_radius_sq_mul_augmented_chord: original full displacement E_A(z)=r_e(z)^2 * augmentedChord(z,Az), including common zeros; r²=D+e². lower_augmented_chord_eq: exact upper(-j) chord at S^-1 z.
horizontalCost z j := pathResistance y x (x+j)*pathEnergy y x (x+j). Upper/lower chord bounds follow original oriented weighted FTC source theorem, all continuity/derivative/integrability facts already proved. Both signs product nonnegative.
blockPathCost z := (2(N+1))^-1 sum ALL residue j of horizontalCost z j.val plus horizontalCost (S^-1 z) (-j.val). blockEnergy_le_radius_sq_mul_pathCost. density_le_mean_add_pathCost D≤cardDeck|m|²+16(D+e²)K. Mean-zero D/(D+e²)≤16K.

### Exact original current density
horizontalCurrentDensity(z)=(pairEnergy_1(z)+phaseCurrent_1(z)^2+e²*directionalEnergy_1(ofComplex z))/radius(z)^3.
horizontalCurrentDensity_eq =directionalRemainder_1/radius at actual H points. pathEnergy_eq_current_integral identifies actual integral of this COMPLETE numerator. No node deletion or regulator-gradient loss.

### Exact periodic collapse and level cost
T differential denominator=1 (denom_T). directionalEnergy_T and horizontalCurrentDensity_T proved using literal source derivative/current modular transport and complete quotient permutation.
reciprocal_radius_periodic and horizontalCurrentDensity_periodic: both actual integrands period1.
pathResistance_integer and pathEnergy_integer: signed integer-length integrals exactly j times one-period integrals. horizontalCost_integer: actual product=j²*unitCost.
parameterMoment N=(2(N+1))^-1 sum_j j.val². sum_fin_sq proved by induction/ring (no numerical oracle). parameterMoment_eq=N(2N+1)/12.
periodResistance y=pathResistance y0 1; periodCurrentEnergy y=pathEnergy y0 1; periodCost=product. Periodic integral shift independence proves any unit path equals periodCost(y).
blockPathCost_eq_two_periods:
 K_e(z)=N(2N+1)/12 * [C_e(Im z)+C_e(Im(S^-1 z))].
density_le_mean_add_two_periods:
 D(z)≤cardDeck|m(z)|²+(4/3)N(2N+1)(D(z)+e²)*[C_e(Im z)+C_e(Im(S^-1 z))].
two_period_cost_lower_of_mean_zero: for actual D(z)>0, m(z)=0, e²≤D(z),
 1≤(8/3)N(2N+1)*[C_e(Im z)+C_e(Im(S^-1 z))].
No exceptional forms or zero mean are assumed to exist; these are intrinsic source cases, not RH premises. Level N=0 (n=1) remains valid.

## Mathematical scope
The uniform finite-group coefficient16 now has a fully constructed differential bridge using original paths/currents. That bridge has exact quadratic parameter moment. This does NOT show optimal constants or actual source costs diverge with level, since source/unit costs also vary. No route retired. It also does NOT turn a resistance times line-integral lower bound into unweighted quotient-area current mass. Original mean and nodal residual remain. This explicit product is the remaining object to analyze; do not assume uniform resistance, drop e² derivative term, or infer area mass from selected paths.

Full chain original modular source→independent current comparison or full-Xi occurrence→critical-line classification→RH. Quarter target totalOrbitCurvature≥amplitudeMass/8 remains open; totalOrbitCurvature=λ amplitudeMass/2 already closed earlier. Independent transformed Xi occurrence remains open and is separate even if quarter is proved.

## Audit
Full scratch /tmp/sqb16_paths.lean and actual source passed without warnings. Final lake --no-build build preflight and lake build GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths each list only this leaf for compilation. No umbrella/full build. Existing cached EvenL2LogUnitary informational tactic output replayed, no new warning. 43 #print axioms reports all and only standard propext, Classical.choice, Quot.sound. All43 API entries found exactly once after formal_tools index; one RHTower umbrella import. formal_tools lint PASS existing large-file warnings. No owned compiler processes remain. Frontier-map and all peer work untouched.
Logs /tmp/sqb16_paths_{scratch,source,preflight,build}.log; /tmp/sqb16_axioms.lean/.log; /tmp/sqb16_audit_names.txt; /tmp/sqb16_index.log; /tmp/sqb16_lint.log.
Cards docs/drafts/pipeline/{1-in-progress,3-formalized}/sqb-unipotent-current-paths.md. Older sqb-congruence-unipotent-blocks in-progress card now marks differential identification closed, quotient-area bound stillopen. Universal STATUS new route-independent requirement distinguishes resistance-weighted line products from unweighted area lower bounds.

## Broad discovery this turn
OR full metadata no modulecaps: horocycle/unipotent/matrix coefficient/spectral gap/uncertainty764rows258modules; translationdifference/derivativeenergy/pathenergy/Poincareinequality/uncertainty118/46; Poincare/transport/coarea/capacity/oscillation12339/2711; Mautner/complementary/principalSeries/propertytau/propertyT/Kloosterman/Kuznetsov1999/640. JSON /tmp/sqb16_{horocycle,energy,transport,representation}_broad.json. CountsmetadataNOTproofsread.
Read actual MaassFourierModes1..165, MaassCyclicAutomorphicRepresentation full, source path and current transport modules, Periodic integral mathlib. Existing cyclic automorphic representation is algebraic; no new arithmetic irreducibility/Hilbert/adelic exclusion inferred. Complementary-series metadata alone supplies no actual source exclusion. No Runpod, numerical experiment, or web used.

## Next directions from evidence
Investigate the exact two-height product C_e(y) and C_e(Im(S^-1z)) in quotient-area integration, retaining original amplitude/resistance. Common-zero resistance already can diverge in earlier exact nodal toy, so arbitrary uniform resistance is excluded. Existing periodicity now makes ALL path starting points irrelevant, a usable global simplification. Raw pointwise products aren't area bounds. Possible source-specific control of reciprocal-amplitude correlations or full current/mean/nodal measure remains needed. Avoid merely repackaging the completed path receiver.
Previous mem:selberg/sqb-uniform-congruence-unipotent-blocks-2026-09-09; mem:selberg/sqb-congruence-source-mixing-and-current-decomposition-2026-09-09; older mem:selberg/augmented-source-capacity-and-nodal-resistance-2026-09-08 has superseded later-next-work suggestions but relevant exact node obstruction.

## Lean pitfalls
Avoid open Topology with bare upper/lower (conflicts finite-ring elementary matrices); qualify SelbergMaassAugmentedDirection.unit when simp unfolding outside namespace. bare unit was resolved as wrong simp object. Use explicit Finset.univ in independently elaborated sum_le_sum. radius_sq at z needs simplify ofComplex_apply first before rewriting D+e². ofComplex_apply_of_im_pos is H-valued: prove coerced equality with by rw [theorem], not exact theorem. Function.Periodic goals may need change to beta-reduce before rw. Never simp horizontalCost_integer globally: RHS retains horizontalCost ...1 causing recursion; rewrite individual sum terms once via sum_congr. Attributes on separate lines keep declarations indexable.
