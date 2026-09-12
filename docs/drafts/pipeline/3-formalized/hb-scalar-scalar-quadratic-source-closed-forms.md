# HB: scalar–scalar quadratic Einstein source of the fundamental BM scalar jet

- **ID:** HB-SS-QUADRATIC-SOURCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/notes.md row 35 (route HB, ++ quadratic corrections); rh-current-frontier-map.md route HB
- **Statement:** Every component of `Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) i j` (the scalar–scalar `++` quadratic source `B(h_S,h_S)` on the Birmingham–Mokhtari background, `r ≠ 0`, `y ≠ 0`, `r² ≠ 1`) equals an explicit sum of at most five terms `B² · P(s,r)/(r^a (r²−1)^b) · m · y^k`, with `m` a quadratic monomial in `(S, Sx, Sy, Sxx, Sxy)`, `deg_s P ≤ 6`, `a ≤ 6`, `b ≤ 2`.

## Goal
Row 35 of the HB ledger needs the three `++` blocks SS, SV, VV of the second-harmonic source; SV existed (brute force, 4M heartbeats). The SS block is the physical input to the Kodama–Ishibashi scalar-sector reduction with source (row 35 (ii)) and hence to rows 37, 39, 40. Non-circularity: pure symbolic GR on a fixed background, no Xi input.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea (index collapse over diagonal backgrounds + entry tables + power cancellation)
- [x] 1 → 2  fully-proven: the proof is the Lean computation itself (`[PROVED HERE]` = Lean)
- [x] 2 → 3  formalized: `RHTower.D4BMScalarLinearEquation.scalarJet_quadratic_einstein_0_0` … `_3_3`, `scalarJet_quadratic_ricci_trace`, `scalarJet_quadratic_ricci_i_j`, `scalarJet_quadratic_curvature_u_i_j`; module `ThetaCuspHawkingBMScalarScalarQuadraticSource`; `#print axioms` = propext, Classical.choice, Quot.sound; `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarScalarQuadraticSource` green (2026-09-12)
- [ ] 3 → 4  publication-ready: not a target (no stage 4 for HB pieces)

## Approach
1. `HTGeometry/CoordinateEinsteinDiagonalCollapse`: closed forms of all linearized/quadratic Einstein coefficients over a diagonal background with every background index sum collapsed; `quadratic_scalar_eq`/`quadratic_einstein_eq` over an Einstein background reduce the Einstein coefficient to Ricci minus half the trace.
2. `ThetaCuspHawkingBMScalarJetEntries`: entry tables of the background jet and the scalar jet in a normal form with only `r⁻¹, y⁻¹, (r²−1)⁻¹`.
3. `ThetaCuspHawkingBMScalarJetConnectionTables`: 384 Christoffel-variation closed forms (linear, quadratic, quadratic-spatial), each proved by collapse → tables → `generalize r²−1` → multiply by `r⁹r⁻¹y⁷y⁻¹F⁷F⁻¹` → `ring_nf` → `InversePowerCancellation` → `subst` → `ring`, all at the default heartbeat limit.
4. `ThetaCuspHawkingBMScalarScalarQuadraticRicci`/`…Source`: Riemann traces, Ricci components, trace and Einstein components by `field_simp; ring` assembly.
Consistency: the (2,3) component agrees with the corpus `angularCoefficient_eq` channel (24M-heartbeat module) — checked in scratch by the same pipeline.

## Structure of the result
- Orbit block (0,0), (1,1): only `S²` and the hyperbolic gradient square `y²(Sx²+Sy²)`; (0,1): only `S²`.
- Mixed (0,2),(0,3),(1,2),(1,3): pure `S·∂S` (gradient of `S²`), no gradient of `|∇S|²` (unlike the SV block).
- Angular block: `S²/y²`, `Sx², Sy²`, `S·Sxx`, `S·Sy/y`, `S·Sxy`, `S·Sx/y`; (2,3) `= B² s²((s+1)²−4r²)/(4r⁴) · (2S(Sxy+Sx/y) + Sx·Sy)`.

## Open
- (ii) KI scalar-sector reduction with source (scalar analogue of `D4BMVectorStream.master` and `master_resolvent_defect`).
- VV block via the same pipeline for `D4BMVectorLinearEquation.vectorJet`.

## Log
- 2026-09-12 — created directly at stage 3; all modules compiled clean at default heartbeats; `lake build` of the chain green; axioms standard.

## Response attack (2026-09-12, second pass)
- Built the KI-gauge scalar-stream operator (`ThetaCuspHawkingBMScalarStreamEinstein`) and the gradient-tensor stream operator (`ThetaCuspHawkingBMGradientStreamEinstein`), both clean at default heartbeats; the rate-2s fundamental jet solves the scalar-stream equations identically (cross-check).
- Negative: the SV-style ansatz (rational radial profiles × {S², |∇S|², (∇S⊗∇S)^{tf}, (Δ−λ₂)⁻¹(A S² + B |∇S|²)}) is inconsistent: trace-free and (1,1) balances fix F0, F2 algebraically, the (0,1)/(0,0) gradient-square balances force f_tr = 0 and B = 0, and the (1,2) mixed equation keeps the residual src₀₂/(r⁵(r²−1)). The |∇S|²-stream is excluded by its own Sxx²/Sx·Sxx terms.
- Consequence: 35(ii)/(iii) must go through the per-harmonic KI reduction with source and the ++ Green function; the corpus's `fullAngular` resolvent alone cannot carry the SS response.

## Sourced master identity (2026-09-12, third pass)
- `ThetaCuspHawkingBMScalarStreamMasterIdentity.master_identity` (Lean, standard axioms): for every jet of the KI-gauge harmonic scalar stream, `M[Φ̃] = −(2r/f²)E_tt + (2/s)E_tr + 2rE_rr − (4r/(sf))E_t + 4E_r + (4/r + 4μ/(rf) − 8s²r/f²)E_T − (2/s)E_t' + ((8r²−4)/f)E_T' + 2rE_T''`, `Φ̃ = r(−fF1/s + F0/f − fF2 + 4H)`, `M = ∂_r² + (2r/f)∂_r + μ/(r²f) − 4s²/f²`.
- Vacuum cross-check: the corpus reconstruction `d4KIScalarGaugeInvariantOrbitOfBMMaster` (with `iω = −2s`, `J.first = dΦ/dz`, `z = 1 − r⁻²`) makes E_tr, E_rr, E_t, E_r proportional to `M[Φ]`, E_tt and E_L combinations of `M[Φ]` and `M[Φ]'`, and E_T ≡ 0 (bookkeeping, exact).
- SS master source per harmonic: `(2−μ)² M[Φ_μ] = N(r; s, μ)/(r⁵ f²)`, N explicit (scratch `sigma.json`); the master operator equals the corpus ++ hypergeometric operator after dressing by `z^{s}`.
- Open: rational reconstruction U, the ++ Green at independent angular parameter, spectral assembly.

## Sourced reconstruction (2026-09-12, fourth pass)
- Two bookkeeping errors had produced a false "no rational reconstruction" verdict: source radial derivatives must be envelope-twisted (`D = ∂_r + 2s/(r(r²−1))`, the source carries `B² = z^{s}`), and the trace-free source coefficient is half of `[S·Sxy]` in `½E₂₃`. Diagnosed by testing the three harmonic Bianchi identities of the operator on the sources.
- Corrected harmonic sources (`ThetaCuspHawkingBMScalarStreamSourceHarmonic`): all three Bianchi identities hold (`ssSource_bianchiT/R/Ang`), master source `ssMasterSource`.
- Reconstruction (`…ScalarStreamReconstructionJet`, free symbols): `F1 = 2rs/(2−μ)(Φ̃' − Φ̃/(rf) − src′)`, `H = Φ̃/(4r) + fF1/(4rs) + τ_T/2`, `F2 = ((f/2)F1' + rF1 − 2sH + τ_t)/(sf)`, `F0 = f²F2 − 2fτ_T`; `reconstruction_TT … _L` decompose every sourced harmonic coefficient into master-defect and Bianchi terms (116 coefficient lemmas, `field_simp; ring`; flattened explicit high derivatives are too large for Lean, hence free symbols).
- Field level (`HTGeometry/TwistedRadialDerivative`, `…ScalarStreamReconstructionField`): Horner rational coefficients with explicit derivatives, `twist_linear`, per-chain twist lemmas split per symbol; `sourced_equation_TT … _L` for actual radial functions under `SourcedMasterData` (twisted-jet differentiability, master ODE, Bianchi at order 0 on the exterior). Axioms standard everywhere.
- Dictionary (bookkeeping): master operator in the undressed variable equals `(4/(r²f))` times the corpus `d4BMPlusPlusHypergeometricJet` at `z = 1−r⁻²` with `C = 1+2s`, `A+B = ½+2s`, `AB = s²+s/2−μ/4`.
- Structural: the master equation is the conformally coupled scalar (m² = −2) on Rindler-AdS₄; row 37 needs only the fundamental's own harmonic (reciprocity), the μ-independent Green only for global existence of K₀.

## Per-harmonic causal response as a metric field (2026-09-12, fifth pass)
- `ThetaCuspHawkingBMScalarStreamMasterDictionary`: `masterOp_comp_zmap` (undressed master operator = `4/(r²(r²−1))` × corpus `d4BMPlusPlusHypergeometricJet` at `z = 1−r⁻²` under `C = 1+2s`, `A+B = ½+2s`, `AB = s²+s/2−μ/4`), `dict_C/ApB/AB` for the Birmingham–Mokhtari parameters (`s = −i·chi − (2n+3/2)`, `μ = −(¼+chi²)`), `greenResponse_masterOp`.
- `ThetaCuspHawkingBMScalarStreamSourceField`: Horner radial sources, smoothness, `ssSourcedMasterData`, `ssSourced_equation_*`.
- `ThetaCuspHawkingBMScalarStreamGreenSourced`: forcing `−(r²(r²−1)/4)·ssMasterSource` in `z`, `greenSS`, bootstrap regularity (`contDiffOn_of_linear_ode`), `greenSS_equation_TT … _L`.
- `ThetaCuspHawkingBMScalarStreamEinsteinLower`: lower-triangle stream operator components.
- `ThetaCuspHawkingBMScalarStreamHarmonicField`: `harmonicMetricField_jet` (actual two-jet via `ofField_mul`, `envelope_jet`, `angular_lift_jet`, `ofField_radialLift`, `hasDerivAt_twist`), `harmonicMetricField_einstein`, `greenSS_metricField_einstein`. Axioms standard throughout.
- Still open for row 37: the true SS source is not a single harmonic; the pairing with the − mode's profile reduces the ++ contribution to the single-harmonic response at `Y = S`, `μ = λ`, times the renormalized triple product `⟨S,S²⟩/⟨S,S⟩` (non-L² pairings need the cutoff/renormalized machinery).

## Forcing structure and the finite-part wall (2026-09-12, sixth pass)
- `ThetaCuspHawkingBMScalarStreamForcingHorizon`: the Green forcing is pole-free, `srcForcing = −N(r)/(4r³(2−μ))`, `N` even of degree 6 in `r`; horizon value explicit; at `μ = (s+1)(s+2)` the factor `s` of `N` cancels `2−μ = −s(s+3)`, and the AdS leading growth is `r³/8` (rate-independent).
- `ThetaCuspHawkingBMScalarStreamRadiation`: `ssRadiation` = normalizable coefficient of the SS ++ response = ∫ regular·weight·forcing.
- Structure of the moment (bookkeeping): with `z = 1−r⁻²`, weight `∝ z^{2s−1}(1−z)^{−3/2}`, forcing `= Σ_{k=0}^{3} c_k (1−z)^{3/2−k}`, the integrand is `Σ_k c_k z^{2s−1}(1−z)^{−k}·₂F₁(A,B;C;z)`: Euler integrals `B(2s,1−k)·₃F₂(A,B,2s;C,2s+1−k;1)`, divergent at the AdS boundary for `k ≥ 1` (finite part = analytic continuation in the `(1−z)` exponent), horizon convergence needs `Re s > 0`; not Saalschützian/Watson/Whipple/Dixon, so generically transcendental ₃F₂(1) values — this is the row-33b "unevaluated source moment" made explicit, and rows 31–34's Laurent/collision machinery is the tool for its finite part.


## Pass 7 (2026-09-12): the vector–vector block

Same pipeline for the fundamental vector jet `vectorJet s r y B A C P Q R U W`: 336 entries, 384 Christoffel-variation
closed forms (`bmVectorEntry`, `bmVectorTable`), 40 Riemann traces, ten Ricci and ten Einstein components
(`vectorJet_quadratic_einstein_i_j`, `…VectorVectorQuadraticSource`). Only the symbols `A, C, P, Q, R` occur: the
third-derivative jets `U, W` drop out of the VV source. With the coexact substitution
(`A = S_y, C = −S_x, P = S_xy, Q = S_yy = λS/y² − S_xx, R = −S_xx`) every component is an angular invariant of `S`
(`coexactJet_quadratic_einstein_i_j`, `…VectorVectorSourceInvariants`): orbit block in `S², |∇S|², |∇∇S|²`; mixed
block the gradient of one potential in `S², |∇S|²`; angular block a trace part in the three scalars plus a
trace-free part in `(∇S⊗∇S)^{tf}`, `tfHess(S²)`. Harmonic images (Bochner for `|∇∇S|²`) give `vvSourceTT … vvSourceL`
with all three Bianchi identities (`…VectorVectorSourceHarmonic`), the function-level layer
(`…VectorVectorSourceField`), and the decaying Laurent particular `A/r + B/r³` (`…VectorVectorLaurentMaster`):
the cleared VV master source has no growing part, `B` needs only `(2−μ)⁻¹`, and the normalizable coefficient is
`A = −2s²(3s²+12s+μ+9)/(μ−(2s+1)(2s+2))`. `vvLaurentMetricField_einstein` (`…VectorVectorLaurentField`) is the
field-level statement. All modules at default heartbeats, standard axioms.
