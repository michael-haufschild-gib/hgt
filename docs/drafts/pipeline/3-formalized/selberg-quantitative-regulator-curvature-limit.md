# Quantitative regulator removal in the actual Selberg curvature budget

- **ID:** selberg-regulator-curvature-31
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 31](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** Actual full amplitude mass is finite and positive; the full retained curvature converges monotonically to its amplitude budget, with explicit error at most eigenvalue times regulator.

## Scope

This is a theorem about every hypothetical exceptional Maass eigenform and every positive regulator. All source conditions come from the original source. The theorem does not assert that exceptional eigenforms exist and does not prove the quarter lower bound.

The limiting total retained curvature is identified. No assertion is made that this equals the integral of a pointwise curvature limit. Cycle 28's nodal concentration example remains in force.

## Corpus discovery and proof loop

All broad discovery used --any, because unflagged multiple terms mean AND. Search coverage uses the whole corpus index; these counts do not mean every matching declaration was read.

- uniformIntegrable, dominatedConvergence, finiteVolume, sqrt, norm, defectMeasure, concentration: 43095 declarations in 12403 modules.
- Square-root/error/finite-volume/hyperbolic-area/inverse-square/norm-difference phrases: 2353 declarations in 1090 modules.
- Kato, distributional, weakLaplacian, compactTest, testFunction, defectMeasure, weakConvergence: 228 declarations in 90 modules.
- Local Green, compact support, integration by parts, local regularity: 664 declarations in 381 modules.

Logs: /tmp/selberg_regulator_uniform_discovery.json, /tmp/selberg_amplitude_error_discovery.json, /tmp/selberg_retained_curvature_distribution_discovery.json, /tmp/selberg_weak_curvature_local_green_discovery.json.

MassDispersionUnitExpansion was read for its exact difference-of-squares remainder identity and denominator control. Its complex principal-branch and smallness assumptions were not transferred to the Maass source. SchwartzPositiveCompactDiagonal was read for its retained explicit regulator correction. The actual full-area budget and original mass source were inspected in the current tree before use.

For the next local step, ComplexLaplacianGreenIdentity's two directional integrations by parts and WaveGreenIdentityIntegrable's product-integrability mechanism were read. Mathlib's actual scalar Fréchet integration-by-parts theorem needs differentiability only on the other factor's topological support. CompactSupportIntegrationByParts was read for the proof that derivatives vanish outside the original topological support. No global smoothness of the source's ofComplex extension was assumed.

1. Conjecture: actual full amplitude mass is integrable uniformly without a regulator. Proved from actual finite hyperbolic area and original source mass.
2. Initial scalar test: the spectral-weight error is at most the regulator. Proved with the stronger bound e/2 by exact square completion.
3. Conjecture: actual full retained-curvature error has a uniform quantitative bound. Proved with bound lambda*e, including original common zeros.
4. Strengthening: actual total curvature is antitone in the positive regulator and has a positive limiting budget. Proved. This is not pointwise curvature monotonicity.
5. Next conjecture: identify the local positive limiting curvature functional on compact tests. Not yet proved.

## Dependency-closed paper proof

Let Omega be the literal full modular domain from cycle 30. Since sqrt(1-x²)>=1/2 on its horizontal range, Omega lies in

S=[-1/2,1/2] x [1/2,infinity).

The actual primitive -1/y has positive derivative 1/y² and tends to zero at infinity. The positive-derivative improper FTC proves integrability on every positive ray and integral_a^infinity 1/y²=1/a. Product integration gives integral_S 1/y²=2. Restriction to Omega proves both integrability and integral_Omega 1/y²<=2. This is an exact upper bound, not a numerical area approximation.

Write D for the original actual finite trace density. It is nonnegative, locally continuous on the upper half-plane, and its full hyperbolic mass integral is finite by cycle 30. Since

sqrt(D) <= (D+1)/2,

the actual amplitude mass A(p)=sqrt(D(p))/y² is integrable on Omega. Its continuity at positive heights follows from the original C² density, continuity of the real square root, and the nonzero height denominator.

For d>=0 and e>0 put a=sqrt(d), r=sqrt(d+e²). Then a>=0, r>0, a²=d, r²=d+e², and

(a-d/r)*r*(r+a)=a*e².

The denominator is positive, and

r*(r+a)-2ae=(a-e)²+ar>=0.

Multiplying this inequality by e/2 and dividing by the positive denominator proves

0 <= a-d/r <= e/2.

The lower bound follows separately from r>=a. All statements include d=0; there is no division by a or by D.

The actual inverse-radius spectral mass is W_e=D/(y²*rho_e), where rho_e=sqrt(D+e²). Applying the scalar result gives

0 <= A-W_e <= (e/2)/y².

Every W_e is already integrable by the full-area source theorem. Integrating the actual difference and using the area bound gives

0 <= integral_Omega A - integral_Omega W_e <= e,

and, since the difference is nonnegative,

integral_Omega |A-W_e| <= e.

Thus this is full-domain L¹ control with an explicit uniform error. It also proves convergence of the actual weighted spectral mass to the amplitude mass.

Cycle 30 gives the actual identity C_e=integral_Omega R_e/rho_e=lambda integral_Omega W_e. Consequently

0 <= lambda integral_Omega A - C_e <= lambda*e.

The positive-regulator limit filter is the pullback of neighborhoods of zero under the inclusion of positive reals. It is proved nontrivial using that zero is in the closure of the positive real ray. The displayed inequalities squeeze the mass error to zero along this actual filter. Therefore

C_e -> lambda integral_Omega A.

For e1<=e2, positivity and squaring show rho_e1<=rho_e2. Thus W_e2<=W_e1 pointwise and integral W_e2<=integral W_e1. The full source identity gives C_e2<=C_e1. This is monotonicity of the total retained curvature; the pointwise curvature remainder is not asserted to be monotone.

Original nonvanishing already makes the full weighted spectral mass at regulator one strictly positive. Since it is bounded above by the amplitude mass, integral_Omega A is strictly positive. For exceptional lambda>0 the limiting curvature budget is therefore strictly positive as well.

## Lean and verification

- SelbergModularHyperbolicArea: actual inverse-square primitive, ray integral, product strip integral, and full modular area domination.
- SelbergSquareRootRegularizationError: exact scalar square-root and weighted spectral error inequalities, uniformly through zeros.
- SelbergMaassRegulatorMass: actual integrability, L¹ error, quantitative total curvature error, nontrivial regulator filter, limits, positivity, and total monotonicity.

All complete scratch proofs passed without warnings, and the new actual-source module passed its direct olean-producing check. All 36 public declarations, including the named filter instance, passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. No added axioms or admissions. The audit covers the complete declaration list: /tmp/selberg_regulator_mass_declarations.txt, /tmp/selberg_regulator_mass_axioms.lean, /tmp/selberg_regulator_mass_axioms.log.

All three modules are wired into RHTower.lean. The refreshed corpus returns full_curvature_limit, full_curvature_error_le, full_amplitude_error_l1_le, and full_curvature_antitone (/tmp/selberg_regulator_mass_corpus_audit.json). Task-source and parent-card whitespace checks passed.

All three serialized final LEAN_NUM_THREADS=1 lake build <single-module> audits passed, each rebuilding only its named target: square-root error (2.0s), modular hyperbolic area (12s), actual regulator mass (4.4s). Logs: /tmp/selberg_square_root_error_build.log, /tmp/selberg_modular_hyperbolic_area_build.log, /tmp/selberg_maass_regulator_mass_build.log. Cached informational output from EvenL2LogUnitary was replayed; there were no new task-module warnings. No full or umbrella build ran.

Repository lint failed only on unrelated HTGeometry.FokasLenellsScatteringContinuity and HTGeometry.FokasLenellsSpectralContinuity, with existing large-file warnings (/tmp/selberg_regulator_mass_lint.log). Those sources were not modified by this task. The two cycle-30 lint errors are historical and did not occur in this audit.

All task-owned Lean/build handles are terminal. No commit or push was made by this task.

## Remaining source gap

The new result determines total limiting curvature, with a uniform error bound. It does not determine its spatial distribution or yield the quarter comparison.

For a real C² test phi compactly supported inside the upper half-plane, test the proposed source functional

J(phi)=integral sqrt(D)*Delta phi + lambda integral phi*sqrt(D)/y².

Actual local Green integration should identify the regularized expression. The checked scalar bounds suggest test error at most e*(integral |Delta phi| + lambda/2*integral |phi|/y²). Every product-integrability condition, support inclusion, and integration-by-parts hypothesis must be proved from the actual source. Positivity on nonnegative tests would retain nodal charge. Neither that local theorem nor a representing measure is claimed here.

The ultimate unsolved step is still the source-derived quarter lower comparison, including compact core and Bessel boundary terms. Continue corpus-driven proof/fail/pivot work toward it; the main Selberg goal remains active.
