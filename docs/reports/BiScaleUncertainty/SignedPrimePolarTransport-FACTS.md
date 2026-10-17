# Signed prime–polar transport: facts and failure boundaries

## Counting rule

Target: 100 substantive, independently justified contributions. Verified packages: 9.
Helpers, equivalent restatements, and classical partial summation do not count separately.

Field direction: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read
fully on 2026-10-17 and read-only by user instruction. Section 3.3 remains this
lane's topic: actual signed prime–polar transport and Chebyshev coupling.
Section 3.5 and Trap 10 prioritize explicit unconditional producers and prohibit
pre-floor subtraction that replaces the continuum counterterm by a divisor sum.

## Established inputs

- Pillar XIV retains arbitrary signed node correlations; its Krein increment bound
  controls |h(t+y)−h(t)| by sqrt(2h(0)(h(0)−h(y))).
- Pillar XV proves the reciprocal penalty exp(−y/2)sinh(y) and annular local transport.
- Classical ψ is available as `Chebyshev.psi` in the installed mathlib.
- Compact continuous autocorrelations are continuous via `continuous_autocorr_compact`.

## Exact sign and domain constraints

- Polar density is exp(x/2)+exp(−x/2). Matching prime density to exp(x/2)
  leaves a genuine exp(−x/2) integral; it cannot be discarded.
- With E(x)=ψ(exp x)−exp x, E(0)=−1. Integration by parts contributes +H(0).
- Finite-window endpoints survive unless actual support proves their vanishing.
- Source continuity does not justify differentiating its autocorrelation. An annular
  average H(t)=(b−a)⁻¹∫_a^b h(t+y)dy has the constructed continuous derivative
  (h(t+b)−h(t+a))/(b−a).
- Separate per-node applications spend origin energy repeatedly. A uniform averaging
  estimate followed by the actual total measure mass keeps that cost explicit.

## Contribution 1: continuous-source signed Chebyshev coupling

The dependency-closed paper proof is in `SignedPrimePolarTransport.md`.
`AnnularCorrelationTransport.lean` and `SignedPrimePolarCoupling.lean` establish one
combined package. For every actual compact continuous source and every integer
cutoff L=log(N+2), its original signed prime–polar pairing differs from explicit
Chebyshev work of a constructed C¹ collar average by at most M_L K. The exact work
retains H(0), the upper endpoint, and the negative-exponential polar shadow. K is
bounded by η times annular Lévy energy plus R/(2ηd²) times the reciprocal-weight
integral. No blindness, source derivative, arithmetic bound, finite full Lévy
energy, or nonzero-source premise occurs in either main theorem.

Public endpoints in namespace `SignedPrimePolar`:
- `pairing_eq_literal`: exact requested n=2,...,N+2 atom sum and polar integral.
- `pairing_correlationAverage_eq`: exact Chebyshev work identity.
- `abs_pairing_sub_chebyshevWork_le`: original-source coupling with uniform Krein cost.
- `abs_pairing_sub_chebyshevWork_le_levy`: adjustable local Lévy/reciprocal-weight bound.

Both leaves pass `lake --old env lean <leaf> -o <leaf.olean>` without diagnostics.
Six endpoint axiom audits in `/tmp/spp_final_axioms.lean` pass, with only propext,
Classical.choice and Quot.sound; printed main signatures contain no extra premise.
Both leaves are wired into `BiScaleUncertainty.lean`; indexes were regenerated.
The latest repository lint result is recorded with contribution 8 below.
Earlier package logs: `/tmp/spp-final-axioms.log`, `/tmp/spp-index.log`, `/tmp/spp-lint.log`.

Boundary of contribution 1: its result is at every finite integer cutoff;
contribution 3 supplies the full-half-line scalar identity. M_L is explicit and
grows with the window; no cutoff-uniform
bound follows. Averaging, partial summation, and local Young inequalities are
components of this single contribution, not separately counted contributions.

Reusable Lean detail: the chain-rule derivative of exp(−x/2) can expose `(-id) x`.
Reduce `Pi.neg_apply` and `id_eq` before ring normalization. For restricted-measure
indicator integrability use `Integrable.indicator` explicitly; field notation on
an `IntegrableOn` proof selects a different interface.

## Contribution 2: actual signed-packet Gram transport

Paper proof: `SignedPrimePolarPacketGram.md`. Lean leaves:
`SignedPrimePolarPacket.lean` and `SignedPrimePolarGramTransport.lean`.

For ν_L equal to the actual finite-window prime measure minus the full polar
measure, construct P_L(u)=∫f(u+t)dν_L(t) as a compact continuous source. The
continuum component's support and every mixed Fubini interchange are derived
from the actual source supports. The new invariant is

Q_L=∫P_L²=∫∫h(s−t)dν_L(s)dν_L(t), with 0≤Q_L≤M_L²h(0).

The exact Gram representation retains prime–prime, both negative prime–polar,
and positive polar–polar terms. For every real y,

|D_L(h(·+y)−h)|²≤2Q_L(h(0)−h(y)).

Consequently the original signed pairing differs from its exact Chebyshev work
by at most d⁻¹∫annulus sqrt(2Q_L(h(0)−h(y)))dy. This cost never exceeds the
previous unsigned-mass cost. Its archimedean bound is

η J_annulus + Q_L/(2ηd²) ∫annulus exp(−y/2)sinh y dy.

One source-energy budget controls the full signed measure. No grid zeros,
source derivative, assumed packet integrability, arithmetic estimate, nonzero
source, or finite full Lévy-energy premise enters the main statements.
All ingredients count as one package, not additional contributions.

Public endpoints in `SignedPrimePolar`:
- `integral_mul_signedSource`: exact mixed representation for actual compact sources.
- `pairing_increment_sq_le_packetEnergy`: signed source-chord estimate.
- `packetEnergy_eq_iterated_pairing`: complete signed Gram identity.
- `packetEnergy_le_mass_sq`: comparison with the unsigned-mass budget.
- `packetTransportCost_le_mass_cost`: comparison of actual averaging costs.
- `abs_pairing_sub_chebyshevWork_le_packet`: direct signed Chebyshev coupling.
- `abs_pairing_sub_chebyshevWork_le_packet_levy`: reciprocal-weight penalty.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` without
diagnostics. Seven endpoint axiom reports contain only propext, Classical.choice,
and Quot.sound; printed main signatures have only source and numerical inputs.
Both leaves are wired into `BiScaleUncertainty.lean`; indexes are refreshed.
At contribution 2 verification, global lint had two unrelated concurrent wiring errors:
`BiScaleUncertainty.CoprimeTentHilbertFrame` and
`BiScaleUncertainty.InfiniteCoprimeTraceProjection`. It reports no task-local error.
Evidence: `/tmp/spp2_final_axioms.lean`, `/tmp/spp2-final-axioms.log`,
`/tmp/spp2-transport-build.log`, `/tmp/spp2-index.log`, `/tmp/spp2-lint.log`.

## Contribution 3: source-admitted full-half-line signed transport

Paper proof: `SignedPrimePolarHalfLine.md`. Lean leaves:
`SignedPrimePolarHalfLineDomain.lean` and `SignedPrimePolarHalfLineTransport.lean`.

For every actual compact continuous source f, construct one integer cutoff N₀
from compact support of h=autocorr f. The same cutoff kills h, every positive
right-annular average H, and its constructed derivative V. The literal pairing

D∞(h)=Σ_{n≥2} Λ(n)h(log n)/√n − ∫₀∞ 2cosh(x/2)h(x)dx

has finite atom support, an absolutely summable atom sequence, and an integrable
polar term. The analogous claims hold for H. The actual Chebyshev work kernels
exp(−x/2)(V−H/2)E and exp(−x/2)H are integrable on the positive half-line.
The upper endpoint vanishes by actual source support, giving

D∞(H)=H(0)−∫₀∞ exp(−x/2)(V−H/2)E−∫₀∞ exp(−x/2)H.

For every K≥0, the signed packet bound at N=N₀+K now controls the difference
between D∞(h) and this global work. It retains Q_N, the annular Lévy energy,
and the exact reciprocal-weight penalty. No extra analytic premise, source
derivative, grid blindness, or arithmetic error estimate enters the endpoints.
Domain admission, endpoint removal, and transport are one contribution.

Public endpoints in `SignedPrimePolar`:
- `autocorr_fullPairing_admissible` and `average_fullPairing_admissible`.
- `integrableOn_abelKernel_logError` and `integrableOn_shadowKernel`.
- `fullPairing_average_eq_fullChebyshevWork`.
- `abs_fullPairing_sub_fullChebyshevWork_le_packet`.
- `abs_fullPairing_sub_fullChebyshevWork_le_packet_levy`.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` with empty
diagnostic logs. All seven endpoint axiom audits pass with only propext,
Classical.choice, and Quot.sound. Printed main signatures have only the source
and numerical parameters. Both leaves are wired into `BiScaleUncertainty.lean`.
Evidence: `/tmp/spp3_final_axioms.lean`, `/tmp/spp3-final-axioms.log`,
`/tmp/spp3-domain-build.log`, and `/tmp/spp3-transport-build.log`.

At contribution 3 verification, global lint exited 1 on seven unrelated concurrent modules unreachable from the
field umbrella: `CoprimeProjectionCrossGram`, `CoprimeProjectionLattice`,
`HyperbolicGaugeChebyshevEnergyRepresentation`, `InfiniteGridStrictEnergyLoss`,
`ShortSupportEnergyInjection`, `SmallSourceCorrelationStability`, and
`UnitEnergySmallSources`. It reports no task-local error. Evidence:
`/tmp/spp3-lint.log`. These modules are outside this lane's write scope.
`scripts/formal_tools.py index` exits 0 and refreshes the generated API, gaps,
overview, and search index; see `/tmp/spp3-index.log`. Scoped diff checks pass.

## Contribution 4: coherent annular Schur coupling

Paper: `SignedPrimePolarCoherentSchur.md`. Lean leaves:
`AnnularCorrelationSource.lean` and `SignedPrimePolarCoherentSchur.lean`.

Construct the actual compact continuous backward collar average
g(u)=d⁻¹∫_I f(u-y)dy, with I=[exp(a),exp(a)+d], d=exp(b).
For R=h(0), C=H(0), D=D_N(h), W=chebyshevWork, and Q=packetEnergy:

B=∫g²=d⁻²∫_I∫_I h(z-y)dzdy,   ∫gf=C,   ∫gP_N=W,   0≤B≤R.

The full double collar Gram integral is retained. Actual compact source supports
justify its Fubini interchanges and every source product integral. Projecting both
g and P_N off f yields nonnegative residual energies B-C²/R and Q-D²/R and

(W-CD/R)² ≤ (B-C²/R)(Q-D²/R).

The same source geometry proves

(D-W)² ≤ Q(R+B-2C),
D²/R + (W-CD/R)²/(B-C²/R) ≤ Q.

Thus the two signed scalar observations jointly constrain packet energy beyond
the single-source Cauchy–Schwarz bound. The entire collar is treated coherently;
its cross-correlations and the packet's mixed prime–polar terms remain explicit.
At every N=N₀(f)+K these identities transfer to D∞(h) and fullChebyshevWork.
All endpoints include the zero source and take only actual C_c sources plus
numerical parameters. Real division by zero is handled without a nonzero premise.
No source derivative, grid blindness, or unverified analytic interface is used.

Public endpoints in `SignedPrimePolar`:
- `integral_collarSource_mul_shift` and `integral_collarSource_signedSource`.
- `collarEnergy_eq_double_average` and `collarEnergy_le_origin`.
- `signedPacketSchurEnergy_nonneg` and `collarSchurEnergy_nonneg`.
- `chebyshevWork_schur` and `fullChebyshevWork_schur`.
- `fullPairing_sub_work_sq_le_coherent`.
- `packetEnergy_lower_bound_from_fullWork`.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` with empty
diagnostic logs. The final scratch audit exits 0; ten endpoint axiom reports
contain only propext, Classical.choice, and Quot.sound. Printed global signatures
have no additional premises. Imports are wired; index refresh exits 0 and scoped
whitespace checks pass. Evidence: `/tmp/spp4-source-build.log`,
`/tmp/spp4-schur-build.log`, `/tmp/spp4_final_axioms.lean`,
`/tmp/spp4-final-axioms.log`, and `/tmp/spp4-index.log`.

At contribution 4 verification, global lint exited 1 on three unrelated concurrent unwired modules:
`CoprimeProjectionAnglePolynomial`, `CoprimeProjectionNeighbors`, and
`HyperbolicGaugeChebyshevEnergyRepresentation`. No task-local error is reported;
see `/tmp/spp4-lint.log`. No unrelated source was edited.

Search found finite-packet projection and abstract Schur precedents, which are
not counted as new. The new package connects the actual continuum collar source,
mixed signed packet, and global Chebyshev work. Initial energy search reports
partial=false; targeted Schur search partial=true; both errors=[]. Semantic
coverage remains unmeasured and refresh deferred. No external novelty claim.
This entire construction counts once, including its energy certificate.

## Contribution 5: rough-source Chebyshev mean-square upper control

Paper: `SignedPrimePolarRoughGauge.md`. Lean leaves:
`AnnularSourceRegularity.lean` and `SignedPrimePolarRoughGauge.lean`.

For every actual compact continuous f, the constructed backward collar source g
is C¹ with g'(u)=(f(u-A)-f(u-A-d))/d. Its gauge k=g'-g/2 is an actual compact
continuous source; G=∫|k| is integrable. The exact remainder norm is
δ=||f-g||²=R+B-2C. No derivative of f is assumed.

With e(x)=exp(-x/2)(ψ(exp x)-exp x), E₂=∫₀ᴸe², and arbitrary η=exp(c),

Q_N(f) ≤ 3(1+η)(10+e(L)²)B + 3(1+η)G²E₂ + (1+1/η)M_N²δ.

At η=1 the coefficients are 6,6,2. This discharges the C¹ premise in the
neighboring `ChebyshevGauge.packetEnergy_le_chebyshev_mean_square` by applying
it to actual g, then controlling the exact packet of f-g by the mass bound.
The neighboring theorem is reused, not counted as a contribution in this lane.
Both quantitative integrals are admitted explicitly.

The resulting `roughGaugeBound` controls global coherent transport and global
Lévy–sinh transport at every N=N₀(f)+K. Smoothing and transport collars are
independent. The latter retains the exact exp(-y/2)sinh(y) reciprocal penalty.
All main signatures contain only original C_c sources and numerical parameters;
no C¹, integrability, source nonvanishing, grid-zero, or arithmetic-error premise.
The roughness term is retained: no cutoff-uniform estimate is asserted.

Public endpoints in `SignedPrimePolar`:
- `contDiff_collarSource`, `integrable_abs_collarGaugeSource`.
- `autocorr_collarRemainderSource_zero`, `packetEnergy_le_weighted_split`.
- `packetEnergy_le_weighted_collarGauge`, `packetEnergy_le_roughGaugeBound`.
- `roughGaugeBound_integrals_admissible`.
- `fullPairing_sub_work_sq_le_roughGauge`.
- `abs_fullPairing_sub_work_le_roughGauge_levy`.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` with empty
diagnostics. Final scratch audit exits 0: nine new endpoints and the reused C¹
dependency have only propext, Classical.choice, Quot.sound. Printed main
signatures contain no extra hypotheses. Imports are wired; index refresh exits 0.
Evidence: `/tmp/spp5-regularity-build.log`, `/tmp/spp5-rough-build.log`,
`/tmp/spp5_final_axioms.lean`, `/tmp/spp5-final-axioms.log`, `/tmp/spp5-index.log`.
Global lint exits 1 solely for unrelated concurrent unwired
`ChebyshevGaugeNyquistCellQuadrature`; no task-local error (`/tmp/spp5-lint.log`).
Fresh search `/tmp/spp5-search.json` reports partial=false/errors=[], semantic
coverage unmeasured and refresh deferred. No external novelty claim.

## Contribution 6: exact gauge geometry and correlation-based packet budget

Paper: `SignedPrimePolarGaugeCorrelation.md`. Lean leaves:
`AnnularGaugeEnergy.lean` and `SignedPrimePolarCorrelationBudget.lean`.

For every actual compact continuous f, set A=exp(a), d=exp(b), g=collarSource,
s=g', k=s-g/2, B=||g||², R=h(0), and T=multiplierSourceRadius f. Then

∫s²=2(R-h(d))/d²,   ∫sg=0,
∫k²=2(R-h(d))/d²+B/4=:E_g.

Changing A translates g; B and E_g are independent of A. The actual gauge
source vanishes outside [A-T,A+d+T], so its admitted L¹ norm satisfies

G²≤(2T+d)E_g=:collarGaugeBudget.

This eliminates the constructed gauge norm from contribution 5:

Q_N(f)≤6(10+e(L)²)B+6(2T+d)E_g∫₀ᴸe²+2M_N²(R+B-2H(0)).

The resulting `correlationGaugeBound` transfers to global signed Lévy–sinh
transport at every N=N₀(f)+K, with independent smoothing and transport collars.
All main statements use only actual C_c sources and numerical parameters.
No derivative of f, source nonvanishing, grid blindness, or arithmetic estimate
is assumed. The source radius is derived from f, not an extra hypothesis;
it need not be minimal. The entire exact-energy/support/transport package counts
once. Generic integration by parts and Cauchy–Schwarz are reused inputs.

Public endpoints in `SignedPrimePolar`:
- `integral_collarSourceSlope_sq`, `integral_collarSourceSlope_mul_collarSource`.
- `integral_collarGaugeSource_sq`, `collarEnergy_position_invariant`.
- `collarGaugeEnergy_position_invariant`, `collarGaugeSource_zero_off_interval`.
- `collarGaugeL1_sq_le_budget`, `collarGaugeBudget_position_invariant`.
- `packetEnergy_le_correlationGaugeBound`.
- `abs_fullPairing_sub_work_le_correlationGauge_levy`.

Both leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` with empty
diagnostics. Final scratch audit exits 0; nine endpoint axiom reports contain
only propext, Classical.choice, Quot.sound. Printed main signatures have no extra
premises. Imports are wired; index refresh exits 0. Evidence:
`/tmp/spp6-energy-build.log`, `/tmp/spp6-budget-build.log`,
`/tmp/spp6_final_axioms.lean`, `/tmp/spp6-final-axioms.log`, `/tmp/spp6-index.log`.

Global lint exits 1 on fourteen unrelated concurrent modules unreachable from
the field umbrella: AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis,
DistantCopyCompactness, DistantCopyCorrelationTopology, DistantCopyEnergyTopology,
DistantCopyPolarTopology, DistantCopySharpness,
HyperbolicGaugeMeanSquareChebyshevWeilSynthesis, SignedGramDualSupport,
SignedGramPhysicalPrices, SignedGramTrialCertificate, TwoGridTraceData,
TwoGridTraceMinimality, TwoGridTraceSharpness, TwoGridTraceStability.
No task-local error is reported; see `/tmp/spp6-lint.log`.
Both package searches report partial=false/errors=[]; semantic coverage remains
unmeasured and index refresh was deferred. No external novelty claim.

## Contribution 7: exact signed collar compensation

Paper: `SignedPrimePolarOptimalCollar.md`. Lean leaves:
`SignedPrimePolarScaledCollar.lean` and `SignedPrimePolarOptimalCollar.lean`.

The fixed coefficient in f=g+(f-g) is replaced by every real t. Actual packet
linearity and exact source energy give, for η=exp(c), C=H(0), R=h(0), B=||g||²,

Q_N(f)≤F(t)=(1+η)t²U+(1+1/η)M_N²(R-2tC+t²B),

where U=3(10+e(L)²)B+3collarGaugeBudget∫₀ᴸe² is an admitted upper bound
for Q_N(g). It satisfies U≥30B. Set

D=(1+η)U+(1+1/η)M_N²B, E=(1+1/η)M_N²C,
t*=E/D, V=(1+1/η)M_N²R-E²/D.

The exact excess identity is F(t)-V=D(t-t*)², including D=0. The actual
source Gram inequality discharges degeneracy: D≥U≥30B, so D=0 forces B=0,
then C=E=0. Consequently Q_N(f)≤V≤F(t), and F(t)=V iff D=0 or t=t*.
The coefficient retains the sign of covariance; no positivity of C is imposed.

The capped certificate Z=min(M_N²R,V) satisfies Q_N(f)≤Z≤M_N²R. At η=1,
F(1)=correlationGaugeBound, so Z is no worse than both prior budgets. The
exact uncapped gain is D(1-t*)². At every η, strict improvement over the mass
estimate occurs exactly when M_N²R/η<E²/D. Smoothness alone does not assert
strict gain. Global coherent and Lévy transport use Z at N=N₀(f)+K, retaining
independent smoothing, splitting, and transport parameters.

All main signatures use actual compact continuous sources and numerical inputs
only. No source derivative, denominator/source nonvanishing, covariance sign,
grid blindness, or arithmetic error estimate is assumed. Optimality is for this
scalar trial family with fixed smoothing and η; no joint width optimization or
cutoff-uniform estimate is claimed. The full compensation/degeneracy/comparison/
transport package counts once, not each algebraic identity.

Public endpoints in `SignedPrimePolar`:
- `autocorr_sub_smul_collar_zero`, `packetEnergy_le_collarTrialBound`.
- `collarTrialBound_excess`, `collarTrialBound_eq_optimum_iff`.
- `packetEnergy_le_optimizedPacketBound`, `optimizedPacketBound_le_mass`.
- `optimizedPacketBound_lt_mass_iff`.
- `optimizedPacketBound_le_correlationGaugeBound`, `correlationGaugeBound_sub_optimum`.
- `fullPairing_sub_work_sq_le_optimized`, `abs_fullPairing_sub_work_le_optimized_levy`.

Both direct leaf checks exit 0 with empty diagnostics. Twelve endpoint axiom
reports in the scratch audit contain only propext, Classical.choice, Quot.sound;
main signatures have no extra premises. Imports are wired, index refresh exits 0.
Evidence: `/tmp/spp7-scaled-build.log`, `/tmp/spp7-optimal-build.log`,
`/tmp/spp7_final_axioms.lean`, `/tmp/spp7-final-axioms.log`, `/tmp/spp7-index.log`.
Global lint exits 1 solely for six unrelated concurrent unwired modules:
CausalExponentialResponseAndLaplaceEnergy,
ExplicitNyquistPolarAndChebyshevFactorialProducer, FiniteGridRunLength,
FoldFreeKernelGramAndFranelGcdCancellation, RealizedCoherentCancellation,
SuccessorSequenceHilbert. No task-local error (`/tmp/spp7-lint.log`).

Both package searches report partial=false/errors=[]; snapshot compiler coverage
has many pending/stale entries. Retrieved finite-partition Gram optimization is
distinct from this actual collar-source family. No external novelty claim.

## Contribution 8: explicit factorial producer for the actual signed measure

Paper: `SignedPrimePolarFactorialProducer.md`. Lean leaves:
`SignedPrimePolarHarmonicCorrection.lean`, `SignedPrimePolarFactorialLift.lean`,
and `SignedPrimePolarFactorialProducer.lean`.

For K≥1 define the concrete compact measurable test
R_K(x)=exp(x/2) Σ_{j=1}^K 1_[0,log(K/j)](x), using real K/j. Its actual
critical atomic sum is T(K), while its polar integral is
K H_K−K+K log K−T(K), with H_K=Σ_{j=1}^K 1/j. Hence

ν(R_K)=2T(K)−K log K−K H_K+K.

This retains both polar exponential branches. The continuum cutoff is never
floored; no discrete linear counterterm is subtracted before floor summation.
For W_N=(R_(4N)−4R_(2N)+4R_N)/sqrt(N), the exact signed evaluation is

ν(W_N)=(2 B_N−C_N)/sqrt(N),
C_N=4N(H_(4N)−2H_(2N)+H_N),

where B_N is the existing unconditional factorial bi-null producer. Pairing
adjacent reciprocal terms proves 0≤C_N≤1. The existing bound on B_N then gives

|ν(W_N)|≤(10 log(4N+1)+3)/sqrt(N), N≥1.

Every literal atom sequence has finite support and is absolutely summable;
the polar term is integrable, derived from the explicit rectangles. The public
`factorialBiNull_producer (n : ℕ)` packages admission and the bound at N=n+1,
with no arithmetic estimate, free producer weights, or analytic premise.

The test has fixed top amplitude: W_N(0)=0 and W_N(log(4N))=2. The formal
`factorialBiNull_ne_autocorr` proves it cannot be the autocorrelation of any
compact continuous real source. This is a scalar producer for the actual signed
measure, not a uniform packet estimate or a positivity theorem. It is discontinuous;
Contribution 9 supplies a continuous producer with exact grid preservation.

Public endpoints in `SignedPrimePolar` include `factorialLift_at_log`,
`tsum_primeTerm_factorialLift`, `fullPairing_factorialLift_eq`,
`harmonicCorrection_bounds`, `fullPairing_factorialBiNull_eq`,
`abs_fullPairing_factorialBiNull_le`, and `factorialBiNull_producer`.
Construction, admission, harmonic cancellation, amplitude and bound count once.
The existing numerical bound on B_N is reused, not counted again.

All three direct final leaf checks exit 0 with empty diagnostics. Twelve scratch
axiom reports contain only propext, Classical.choice and Quot.sound; the printed
main signature has only its integer input. Umbrella imports are wired; index
refresh exits 0. Evidence: `/tmp/spp8-harmonic.log`, `/tmp/spp8-lift.log`,
`/tmp/spp8-producer.log`, `/tmp/spp8_final_axioms.lean`,
`/tmp/spp8-final-axioms.log`, `/tmp/spp8-index.log`.

Global lint exits 1 solely for eleven unrelated concurrent unwired modules:
CoprimeShearArithmeticWeightsAndChebyshevCellIncrement,
FiniteIntegerTrainCompactness, FiniteIntegerTrainEnergy, FiniteIntegerTrainPackets,
FiniteIntegerTrainPeak, FiniteIntegerTrainPolar, FiniteIntegerTrainProducers,
FoldFreeKernelGramAndFranelGcdCancellation, TernaryPacketPolarGrowth,
TernaryPacketTrain, WitnessGermOriginMassAndJointTailHeadSynthesis.
No task-local error (`/tmp/spp8-lint.log`). Scoped whitespace checks pass.

Shared dependency objects disappeared during checking. Passing direct checks
restored Coupling and GramTransport without source edits. A temporary field-object
overlay kept later checks stable; all actual dependencies were present in the
shared tree before the overlay and obsolete probes were removed. No owned process
remains active. The audit files and search evidence are retained.

Package searches `/tmp/spp8-producer-search.json` and `/tmp/spp8-lift-search.json`
report partial=false with complete file inventory; compiler metadata remains
mostly source-only/pending and semantic coverage unmeasured. Candidate lemmas and
source arguments were inspected. No external novelty claim follows from retrieval.

## Contribution 9: continuous grid-preserving producer with nonvanishing L² size

`SignedPrimePolarContinuousFactorialProducer.md` gives the dependency-closed paper
proof. For N≥1 set ε=1/(4N), qε(t)=min(1,max(0,(1+ε−t)/ε)), and
Uε,K(x)=exp(x/2) Σ_{j=1}^K qε(j exp(x)/K). The concrete test is
S_N=(Uε,4N−4Uε,2N+4Uε,N)/sqrt(N), defined on all real x.
The stencil cancels exactly on x≤0 and vanishes above log(4N+1), so S_N is
compact and continuous. The bound εK≤1 implies qε(jn/K)=1_{jn≤K}; thus
S_N(log n)=W_N(log n) for every integer n≥1, with no exceptional grid endpoint.

Piecewise FTC evaluates the single-ramp polar integral, retaining both exponential
branches. The additional correction is εK H_K/2+Kρ(ε), where
ρ(ε)=((1+ε)log(1+ε)−ε)/ε. The linear ρ term cancels, giving

ν(S_N)=[2B_N−(1+1/(8N))C_N]/sqrt(N),
|ν(S_N)|≤[10log(4N+1)+3+1/(8N)]/sqrt(N).

The actual atom sequence has finite support and is absolutely summable; the polar
integrand is globally integrable. No discrepancy estimate is assumed. No discrete
counterterm is inserted into a floor sum.

Finite antitone pairing bounds the dyadic ramp stencil in [−2,1]. Consequently
S_N(x)²≤4exp(x)/N and ∫ℝ S_N²≤16. On the full closed interval
[log(2N+1),log(4N)] the test is exp(x/2)/sqrt(N); hence ∫ℝ S_N²≥2−1/N≥1.
The pairing bound therefore does not arise from vanishing L² size.

The actual object `continuousFactorialProducer (n : ℕ) : C_c(ℝ,ℝ)` uses N=n+1.
The main `continuousFactorialProducer_certificate` has only that integer input
and bundles exact grid preservation, the pairing bound, and 1≤∫S_N²≤16.
Exact evaluation and domain admission are separately certified by
`fullPairing_smoothFactorialBiNull_eq` and `smoothFactorialBiNull_admissible`.
`continuousFactorialProducer_ne_autocorr` retains the genuine domain boundary:
origin value zero and top value two exclude a real-source autocorrelation.

This resolves a continuity and nonvanishing-size obstruction, not arbitrary
source-packet control. Construction, finite antitone cancellation, FTC, grid
preservation, pairing and energy bounds count as one package. No external novelty
claim follows from the partial corpus searches.

All five final direct `lake --old env lean <leaf> -o <olean>` checks pass with empty
diagnostics: `AntitoneDyadicStencil`, `ClampedExponentialRamp`,
`SignedPrimePolarContinuousFactorialLift`, `SignedPrimePolarContinuousFactorialProducer`,
and `SignedPrimePolarContinuousFactorialEnergy`. Fourteen scratch axiom audits use
only propext, Classical.choice and Quot.sound. The printed main signature has no
free analytic or arithmetic premise. All five imports occur once; index refresh
passes and includes the public endpoint. Evidence: `/tmp/spp9-*-final.log`,
`/tmp/spp9_final_axioms.lean`, `/tmp/spp9-final-axioms.log`, `/tmp/spp9-index.log`.

Global lint reports eight unrelated concurrent unwired modules and no package-local
error (`/tmp/spp9-lint.log`): DiscrepancyTransformLaw, NyquistPolarDecomposition,
NyquistPolarSourceEscape, NyquistResidualKernel, NyquistResidualMass,
NyquistResidualOperator, NyquistResidualPartition, and
SelbergSieveTailQuadraticFormAndTruncatedDivisorGram. No full build or umbrella
build was run. README remains read-only and unmodified by this work.

## Failure boundaries and remaining frontier

- Scalar support stabilization does not establish packet-energy stabilization:
  distant translates can still carry squared norm. No cutoff-uniform Q_L estimate
  or full-half-line packet has been proved.
- Contribution 3 closes the full-half-line scalar domain and endpoint obligations.
  The remaining quantitative problem is control of the actual signed packet
  energy, while retaining its mixed arithmetic–continuum terms.
- The finite-window Cauchy–Schwarz bound is a refinement, not a prime-cancellation
  estimate. Obtaining useful control of Q_L is a new quantitative problem.
- Contribution 4 gives joint lower control of Q_L; contributions 5–7 supply a
  rough-source upper bound with a genuine M_L²||f-g||² remainder. None yields
  cutoff-uniform packet control. The gauge budget is position independent;
  smoothing error still depends on position through H(0). Quantitative width
  selection and control of that remainder remain open. Contribution 7 removes
  the fixed-coefficient loss, not the residual itself. Multiple-collar compensation
  remains parked in `0-backlog/signed-prime-polar-multiple-collars-2026-10-17.md`.
  Trap 10 prioritizes explicit unconditional producers over further receivers.
- Contributions 8–9 give explicit unconditional scalar producers, including a
  compact continuous family with fixed positive lower L² size. They do not
  discharge arbitrary-correlation packet control. Next uncounted candidate:
  `1-in-progress/signed-prime-polar-factorial-source-factorization-2026-10-17.md`.
  A causal convolution construction may realize a grid-preserving producer as an
  actual mixed source correlation and a polarized autocorrelation difference.
  Source-energy cost must be quantified; shrinking collars may make it grow.
  Search `/tmp/spp9-next-search.json` is partial with interrupted text/source
  retrieval. Candidates and source arguments were inspected; full precursor
  inspection and a broader convolution search were completed for the dependency-closed
  paper proof in `SignedPrimePolarFactorialSourceFactorization.md`. It constructs
  actual source contrasts with predicted equal origin energies in [6N,46N].
  Full Lean verification remains in progress; this package is not counted yet.
- The prior multiple-collar search returned finite discrete Gram precedents, not
  that mixed construction.
  Both searches report partial=false and errors=[]; semantic coverage is unmeasured,
  refresh was deferred to the running indexer, and much compiler coverage was
  pending/stale. No external novelty claim is justified by this search alone.

Reusable Lean facts: explicit function arguments prevent C_c coercions from
elaborating to incompatible `toContinuousMap` forms. Type integrability statements
with literal lambdas before integral rewrites. Generic `have := @Name` API probes
need explicit universe levels. Finite-sum division is `Finset.sum_div`.
