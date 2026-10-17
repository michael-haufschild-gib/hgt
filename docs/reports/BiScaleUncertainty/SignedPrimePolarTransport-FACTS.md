# Signed prime–polar transport: facts and failure boundaries

## Counting rule

Target: 100 substantive, independently justified contributions. Verified packages: 5.
Helpers, equivalent restatements, and classical partial summation do not count separately.

Field direction: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read
fully on 2026-10-17 and read-only by user instruction. Section 3.3 remains this
lane's topic: actual signed prime–polar transport and Chebyshev coupling.

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
The latest repository lint result is recorded with contribution 5 below.
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

## Failure boundaries and remaining frontier

- Scalar support stabilization does not establish packet-energy stabilization:
  distant translates can still carry squared norm. No cutoff-uniform Q_L estimate
  or full-half-line packet has been proved.
- Contribution 3 closes the full-half-line scalar domain and endpoint obligations.
  The remaining quantitative problem is control of the actual signed packet
  energy, while retaining its mixed arithmetic–continuum terms.
- The finite-window Cauchy–Schwarz bound is a refinement, not a prime-cancellation
  estimate. Obtaining useful control of Q_L is a new quantitative problem.
- Contribution 4 gives joint lower control of Q_L; contribution 5 supplies a
  rough-source upper bound with a genuine M_L²||f-g||² remainder. Neither yields
  cutoff-uniform packet control. Next: quantify the gauge cost and roughness
  directly in terms of the original source's translation geometry.
- Search returned finite discrete Gram precedents, not this mixed construction.
  Both searches report partial=false and errors=[]; semantic coverage is unmeasured,
  refresh was deferred to the running indexer, and much compiler coverage was
  pending/stale. No external novelty claim is justified by this search alone.

Reusable Lean facts: explicit function arguments prevent C_c coercions from
elaborating to incompatible `toContinuousMap` forms. Type integrability statements
with literal lambdas before integral rewrites. Generic `have := @Name` API probes
need explicit universe levels. Finite-sum division is `Finset.sum_div`.
