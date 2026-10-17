# Signed prime–polar research lane

Independent BiScaleUncertainty research. User goal: 100 significant theorem packages; **4/100 verified**, goal ACTIVE, 96 outstanding. No RH work, hgtl7 skill, numerical experiments, grid blindness, inflated helper counts, commits, or umbrella builds. Actual C_c sources and structural numerical inputs are allowed; main endpoints must have no extra analytic hypotheses. One foreground Lean process per agent at a time.

Authoritative field README: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read all 242 lines. **READ-ONLY by explicit user instruction.** Section 3.3 directs this lane. Old docs/reports/BiScaleUncertainty/README.md was relocated; do not edit either README.

Canonical ledger: `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`.
Parent card: `docs/drafts/pipeline/1-in-progress/signed-prime-polar-transport-2026-10-17.md`.
Read user attachment each new turn: `/Users/michael/.codex/attachments/e9ef520a-4498-4562-99e8-1c42812df597/pasted-text-1.txt`.

## Verified packages

1. `AnnularCorrelationTransport.lean` + `SignedPrimePolarCoupling.lean`: constructed C1 collar correlation H for every actual compact continuous f, no derivative of f. Finite cutoff L=log(N+2), actual weights Λ(n)/sqrt(n), polar density 2cosh(x/2). Exact work H0+exp(-L/2)H(L)E(L)-integral exp(-x/2)(V-H/2)E-integral exp(-x/2)H, E=ψ(exp x)-exp x. Uniform Krein cost with mass M_L and adjustable annular Levy/reciprocal-weight bound. Paper `SignedPrimePolarTransport.md`.

2. `SignedPrimePolarPacket.lean` + `SignedPrimePolarGramTransport.lean`: actual compact atomicSource, polarSource, signedSource P_N. Q_N=packetEnergy=integral P_N². Mixed Fubini justified by actual source supports; Q_N=iterated signed pairing of h(s-t), retaining both negative prime–polar mixed terms. Q_N<=M_N²R. Signed increments²<=2Q_N(R-h(y)); annular square-root transport and exact Levy/reciprocal-weight penalty use Q_N. Paper `SignedPrimePolarPacketGram.md`.

3. `SignedPrimePolarHalfLineDomain.lean` + `SignedPrimePolarHalfLineTransport.lean`: source cutoff N0 derived from compact autocorrelation support, uniform over positive right-annular H and V. Literal n>=2 atom sequence has finite support/absolute summability; polar and Chebyshev-work terms are integrable on Ici0. Upper endpoint vanishes. `fullPairing H = fullChebyshevWork`. Every N=N0+K gives global scalar transport with actual finite Q_N. Paper `SignedPrimePolarHalfLine.md`.

4. `AnnularCorrelationSource.lean` + `SignedPrimePolarCoherentSchur.lean`: actual backward collar source g(u)=d^-1 integral_I f(u-y), I=[exp a,exp a+exp b], d=exp b. Mixed covariance integral g(u)f(u+t)=H(t). With C=H0, B=collarEnergy=integral g², R=h0, D=pairing h, W=chebyshevWork, Q=packetEnergy:
- B=d^-2 double integral_I h(z-y), 0<=B<=R; integral gP_N=W.
- signedPacketSchurEnergy=Q-D²/R and collarSchurEnergy=B-C²/R are actual nonnegative residual norms.
- (W-CD/R)² <= (B-C²/R)(Q-D²/R).
- collarChordEnergy=R+B-2C >=0; (D-W)²<=Q*collarChordEnergy.
- D²/R+(W-CD/R)²/(B-C²/R)<=Q.
- Global endpoints `fullChebyshevWork_schur`, `fullPairing_sub_work_sq_le_coherent`, `packetEnergy_lower_bound_from_fullWork` replace D,W by admitted full-half-line scalars at N=N0+K. No nonzero premise; real zero division handled.
Paper `SignedPrimePolarCoherentSchur.md`; card `3-formalized/signed-prime-polar-coherent-schur-2026-10-17.md`. Entire collar and residual construction counts once. Generic Schur projection is not claimed as new; this connects actual continuum collar, actual mixed signed packet and global work.

All four packages have direct leaf passes and standard axiom reports. Package 4: both leaves pass `lake --old env lean <leaf> -o <leaf.olean>` with empty diagnostics. `/tmp/spp4_final_axioms.lean` exits 0; ten endpoint reports contain only propext, Classical.choice, Quot.sound. Main signatures have only actual source and numeric inputs. Evidence `/tmp/spp4-source-build.log`, `/tmp/spp4-schur-build.log`, `/tmp/spp4-final-axioms.log`. Imports wired; index refresh exits 0 (`/tmp/spp4-index.log`). Global lint exits 1 solely for unrelated unwired CoprimeProjectionAnglePolynomial, CoprimeProjectionNeighbors, HyperbolicGaugeChebyshevEnergyRepresentation (`/tmp/spp4-lint.log`). No task-local errors. Do not edit other lanes.

## Boundaries and next target

Scalar support stabilization does NOT imply Q_N stabilization. Distant translates still carry energy. No infinite packet or cutoff-uniform Q bound is proved. H is a mixed correlation, not assumed an autocorrelation. H0 and the negative-exponential polar shadow cannot be dropped; E0=-1 fixes the boundary sign. Package 4 provides joint lower control, not a uniform upper bound or prime cancellation asymptotic. No claim that the changed-centering Schur expression directly dominates every older numerical bound.

Next candidate card: `docs/drafts/pipeline/0-backlog/signed-prime-polar-rough-gauge-2026-10-17.md` (NOT counted). Derive C1 regularity of actual g=collarSource f from continuity of f, with g'(u)=(f(u-exp a)-f(u-exp a-exp b))/exp b. Apply neighboring `ChebyshevGauge.packetEnergy_le_chebyshev_mean_square` to g; combine packet linearity and mass bound on f-g. Candidate:
Q_N(f)<=6(10+Etilde(L)²)B+6||g'-g/2||1² integral_0^L Etilde²+2M_N²(R+B-2C).
Keep the roughness remainder; no cutoff-uniform assertion. Neighbor `HyperbolicGaugeChebyshevEnergyRepresentation.lean` is concurrently developed. Its C1 mean-square theorem was seen in actual source (around line 810), but NO compiled artifact existed at last inspection. Recheck freshness and verification before relying on it; do not modify that lane. Smoothing/packet commutation is not required for the proposed bound.

## Search evidence

`/tmp/spp4-search.json`: partial=false/errors=[], energy candidates.
`/tmp/spp4-schur-search.json`: partial=true/errors=[], finite-packet projection and abstract Schur precedents. Read relevant source `ProjectedHyperbolicGramControl.lean` (private generic helper proofs) and actual abstract Schur declarations. Not the new mixed-continuum collar endpoint.
`/tmp/spp4-next-search.json`: partial=false/errors=[], C1 gauge mean-square candidate, plus current collar source energy. Candidate_lemmas and source_arguments inspected. Semantic coverage unmeasured; refresh deferred to background indexer. No external novelty claim.

## Lean details

- Explicit lambdas and named `(f := fun u y : ℝ => ...)` avoid C_c toContinuousMap inference failures. For Fubini, use explicit integrand with `congr 1; exact ...`, not open-ended `rw` inference (can hit heartbeats).
- `continuous_parametric_integral_of_continuous` is ROOT; `integral_integral_swap_of_hasCompactSupport` is MeasureTheory. Compact mixed support rectangle follows from bounds on u and u±y.
- Residual proof: sourceResidual p f c is actual compact source; expand energy/pairing, split R=0 vs R!=0 for field_simp. Unfold packetEnergy/collarEnergy explicitly before rewriting against their integral forms.
- Give the quotient inequality a complete type before `(div_le_iff₀ hp).mpr`; unconstrained metavariables do not infer from a commuted product.
- Generic `have := @Name` probes need universe levels: HTGeometry.sq_integral_mul_le.{0}, integral_const_mul.{0,0}, continuous_parametric_integral_of_continuous.{0,0,0}.
- `Finset.sum_div`, not sum_div_distrib. `summable_of_ne_finset_zero` exists; Function.HasFiniteSupport.summable does not.
- Source cutoff support input is field `exists_pos_autocorr_support_radius` in DistantCopyPolarEnforcement. After Real.lt_log_iff_exp_lt, push_cast handles ↑(N+2).
- update_plan unavailable; cards carry executable plans. Serena cannot handle Lean symbols in active Python project; use precise patches. Preserve concurrent work.

No owned Lean/search/lint/index process remains running. Obsolete spp4_api probe files are cleaned; retain final audit and evidence logs.


## Verified contribution 5 (supersedes prior candidate status)
Package `AnnularSourceRegularity.lean` + `SignedPrimePolarRoughGauge.lean` verified before interruption, reconciliation completed after resume. Count now 5/100, active. Collar source g is C1 with explicit finite-difference slope; compact gauge source k=g'-g/2 has admitted L1 cost G. Remainder energy δ=R+B-2C exactly. Weighted upper Q_N(f)<=3(1+eta)(10+e(L)^2)B+3(1+eta)G² integral e²+(1+1/eta)M_N²δ, eta=exp c. Fixed coefficients 6,6,2 define roughGaugeBound. Global coherent and exact Levy-sinh transport allow independent smoothing and transport collars. Original source remains arbitrary C_c, no extra premises. Nine new endpoint reports plus reused C1 dependency audited standard axioms; both leaves pass with empty logs, scratch exit0. Logs `/tmp/spp5-regularity-build.log`, `/tmp/spp5-rough-build.log`, `/tmp/spp5-final-axioms.log`, index exit0 `/tmp/spp5-index.log`; lint exit1 only unrelated unwired ChebyshevGaugeNyquistCellQuadrature (`/tmp/spp5-lint.log`). Card now3-formalized/signed-prime-polar-rough-gauge-2026-10-17.md; paper and ledger updated. Earlier no-compiled-artifact concern resolved: C1 dependency now compiled and exact endpoint audited.

Current uncounted package6: `AnnularGaugeEnergy.lean` and `SignedPrimePolarCorrelationBudget.lean`; card `1-in-progress/signed-prime-polar-gauge-correlation-2026-10-17.md`; paper `SignedPrimePolarGaugeCorrelation.md`. Goal: exact integral k²=2(R-h(d))/d²+B/4, collar energy/gauge energy independent of position, support window[A-T,A+d+T] with T=existing multiplierSourceRadius f, then G²<=(2T+d)*exactEnergy. Substitute into rough bound/global Levy transport to eliminate constructed gauge norm. Both searches spp6-search.json/spp6-gauge-search.json partial=false/errors=[]; no equivalent retrieved; no external novelty claim. Code written, verification in progress; do not count yet. One owned Lean session for energy leaf currently active, poll actual handle from live context.
