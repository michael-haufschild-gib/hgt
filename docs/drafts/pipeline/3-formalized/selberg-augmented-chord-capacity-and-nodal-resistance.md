# Actual augmented Maass directions, capacity cost, and nodal resistance

- **ID:** selberg-augmented-capacity-29
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 29](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** The actual smooth augmented source has an exact mean defect, chord-energy comparison, and a fixed-path positive variation cost for all small regulators; nodal resistance has an exact logarithmic singularity.

## Scope

All source conditions in the path comparison are proved from the original C² Maass family. The separation witness is a theorem about every hypothetical exceptional eigenform, not an assertion that exceptional eigenforms exist. The source core/Bessel quarter lower bound and Selberg remain unproved.

The local nodal example is not Maass, cuspidal, periodic, or modular invariant. It falsifies an unqualified regulator-uniform resistance shortcut, not a Maass-specific estimate using additional source information.

## Corpus-derived loop

Broad discovery used `--any` throughout; multiple unflagged terms would mean AND.

- Weighted/resistance/chord/endpoint-energy/transport-cost: 9679 declarations, 3041 modules.
- Weighted Cauchy/endpoint difference/integral energy/path energy/reciprocal weight: 153 declarations, 88 modules.
- Arsinh/reciprocal radius/logarithmic resistance/logarithmic primitive: 45 declarations, 27 modules.
- Bounded variation/coarea/nodal domain/isoperimetric/trace transport: 564 declarations, 85 modules.
- Finite limit/derivative limit/convex/integrable forcing/cusp flux: 1058 declarations, 369 modules. More precise OR phrases for derivative decay/bounded convex/convex decay/logarithmic correction returned 26 declarations in 24 modules.

These counts describe index coverage, not source-reading coverage. Sources read included `StokesCartanCoronaCapacity.parallel_completion`, the real/complex weighted Cauchy mechanism in `SelbergPairingPrimeSquare`, and `RiemannXiSuzukiWeilVertical.hasDerivAt_arsinh_sub_div`. The first supplied exact resistance square completion; the last supplied the reciprocal-square-root primitive mechanism. `Arxiv2608BellmanShorelineProjectedCoarea` was read for its retained projection defect. Its isotropy condition is explicit and has not been constructed for Maass displacements. Broad research modules were read for ideas, not imported.

1. **Conjecture:** the added regulator is a genuine extra source coordinate, giving smooth directions through original zeros and exact regularized energy. **Proved.**
2. **Test:** the augmented vector still has weighted mean zero. **Fails in its added coordinate.** Its exact mean and chord correction are proved and retained.
3. **Conjecture:** the actual augmented endpoint chord is controlled by retained energy times literal reciprocal-amplitude resistance. **Proved, with all source regularity and integrability.**
4. **Test:** positive regularization permits a regulator-uniform resistance bound from local smoothness alone. **Fails in the exact nodal model.** Its full logarithmic finite part and vanishing capacity coefficient are proved.
5. **Positive survivor:** actual source separation gives a lower bound greater than two on squared coordinate variation along the same fixed path for every sufficiently small regulator. **Proved without resistance.**

## Dependency-closed paper proof

Write the original finite congruence family as `F_q`, its squared norm as `D`, and the positive regularized amplitude as `rho_e=sqrt(D+e²)`. Append one literal constant coordinate: `A_some(q)=F_q`, `A_none=e`. Set `U_j=A_j/rho_e`.

The augmented squared norm is `D+e²=rho_e²`, so `sum |U_j|²=1`. Positivity of the denominator and original C² regularity give C² normalized coordinates through the common zero set. Modular transport permutes the original coordinates and fixes the added coordinate. Reconstruction `rho_e*U_j=A_j` is exact.

Differentiating reconstruction gives

`rho_e*partial_v U_j = partial_v A_j-c_v A_j`, where `c_v=(partial_v D)/(2rho_e²)`.

The added coordinate has zero original derivative, so its residual is `e²*c_v²`. Summing the literal squared derivatives proves

`R_{e,v}=rho_e²*sum_j |partial_v U_j|²`.

Thus the retained curvature energy from cycle 28 is the actual smooth augmented direction energy, including the original nodal set.

On every shifted level period of length `w=N+1`, the original exceptional constant-term theorem gives `integral rho_e*U_some(q)=0`, while reconstruction gives `integral rho_e*U_none=e*w`, which is nonzero. For original real correlation `Corr(z,t)`, augmented correlation has numerator `Corr(z,t)+e²`. The exact chord formula is

`rho_e(t)*d_e(z,t)² = 2rho_e(t)-2(Corr(z,t)+e²)/rho_e(z)`.

Its period integral is

`2*integral rho_e - 2e²*w/rho_e(z)`.

Original nonvanishing and zero correlation mean provide fixed same-height points with `Corr(z,t)<0`. Choose a positive regulator threshold below `sqrt(-Corr(z,t))`. For every smaller positive regulator, augmented correlation stays negative and squared chord distance is strictly greater than two. The points remain fixed as the regulator varies.

For a positive continuous real path weight `w(x)` and continuous scalar current `g(x)`, let `R=integral 1/w`. On every nondegenerate positively oriented interval, `R>0`. Pointwise square completion and ordinary interval integration give, for every real constant `c`,

`integral w*(g-c/w)² = integral w*g² - 2c*integral g + c²*R`.

Choose `c=(integral g)/R`; nonnegativity gives `(integral g)² <= R*integral w*g²`. Apply this to real and imaginary parts, then use actual FTC and sum over the finite coordinates. This proves

`sum_j |U_j(b)-U_j(a)|² <= (integral_a^b 1/w)*(integral_a^b w*sum_j |U'_j|²)`.

For the actual source choose `w=rho_e` and use the derivative-energy identity. The energy is precisely `integral R_{e,1}/rho_e`, with continuous integrand and proved interval integrability. Ordering the fixed separated points gives a fixed nondegenerate path with

`pathEnergy_e > 2/pathResistance_e`

for every sufficiently small positive regulator. Both factors are literal source quantities.

There is also a resistance-free positive survivor. FTC and the norm-integral inequality give `|U_j(b)-U_j(a)| <= integral |U'_j|`. Squaring and summing proves

`d_e(a,b)² <= sum_j (integral_a^b |U'_j|)²`.

Consequently the same fixed source path has squared coordinate variation strictly greater than two for every small regulator. This quantity is exactly the stated sum of squared coordinate variations; it is not relabeled as the vector's geodesic length or a two-dimensional area energy.

For the local nodal profile `h(x)=x`, the relevant weight is `r_e(x)=sqrt(x²+e²)`. Differentiating `arsinh(x/e)` gives `1/r_e(x)`. The integrand is continuous for positive `e`, so FTC gives

`R_node(e)=integral_{-1}^1 1/r_e = 2arsinh(1/e)`

`=2log(1+sqrt(1+e²))-2log(e)`.

The finite correction tends to `2log 2`; hence `R_node(e)+2log(e) -> 2log 2`, `R_node(e) -> infinity`, and `2/R_node(e) -> 0`. This is the exact degeneration of the coefficient introduced by the resistance split. It does not remove the nodal curvature or the independently retained source variation.

## Lean and verification

- `SelbergMaassAugmentedDirection.lean`: literal augmented source, smooth unit directions, covariance, derivative energy, exact weighted mean/chord defect, and fixed-point small-regulator separation.
- `SelbergWeightedPathEnergy.lean`: integral square completion, real/complex/finite-family resistance estimate, and squared coordinate-variation estimate.
- `SelbergMaassChordEnergy.lean`: actual derivatives and integrability, source path comparison, and the combined `source_capacity_variation_witness` on the same fixed ordered path.
- `SelbergNodalResistance.lean`: actual primitive and integrability, exact resistance, logarithmic finite part, divergence, and vanishing capacity coefficient.

All four complete scratch checks passed without warnings. Four serialized final `LEAN_NUM_THREADS=1 lake build <single-module>` audits passed, each rebuilding only its named target: weighted path (1.8s), augmented directions (5.4s), actual chord energy (4.0s), nodal resistance (1.7s). No full or umbrella build ran. Logs: `/tmp/selberg_weighted_path_build.log`, `/tmp/selberg_augmented_direction_build.log`, `/tmp/selberg_maass_chord_energy_build.log`, `/tmp/selberg_nodal_resistance_build.log`.

All 57 public definitions/theorems passed the scratch axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. No added axioms or admissions. Audit files: `/tmp/selberg_augmented_axioms.lean`, `/tmp/selberg_augmented_axioms.log`, `/tmp/selberg_augmented_declarations.txt`.

All modules are wired in `RHTower.lean`. The refreshed corpus returns the three queried capstones; `/tmp/selberg_augmented_corpus_audit.json` records that check. Task-file whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformizedFrame`**, with existing large-file warnings (`/tmp/selberg_augmented_lint.log`). That file was not modified. All task-owned Lean/build handles are terminal; no task commit or push.

## Remaining source gap and next conjecture

A positive cost along one fixed path does not supply a lower bound for two-dimensional core energy, and the resistance coefficient cannot be discarded. The combined core/Bessel quarter estimate remains unproved.

Next construct the actual regularized horizontal amplitude mean and its literal first and second derivatives. Test whether original uniform density decay plus the source curvature equation gives vanishing top current at fixed positive regulator. The candidate real-analysis mechanism is a bounded mean with second derivative bounded below by `-C/y²`; subtracting `C*log y` should give a convex comparison whose secants force first derivative decay. Every forcing bound must be derived from the source. If successful, pass from the truncated standard-area balance to the full modular-domain weighted curvature budget, with genuine tail integrability. Do not assume a top limit, an isotropic projected-coarea rule, a regulator-limit exchange, or a quarter bound.
