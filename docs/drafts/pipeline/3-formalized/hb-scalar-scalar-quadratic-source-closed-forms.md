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

## Pass 8 (2026-09-13): onset trace and causal cut

- `RHTower/ThetaCuspHawkingBMEvenSectorOnsetCurrent`: time component of the Einstein action current
  between the `−` mode and the SS/VV `++` Laurent responses (`evenSector_onsetCurrent_SS/VV`), built from
  the per-family and per-source-jet closed forms with the radial module's jets.
- `RHTower/ThetaCuspHawkingBMEvenSectorOnsetTrace`: at `μ = (s+1)(s+2)` with the actual Laurent
  coefficients, `r²·Ω^t = N(s,r)/(r⁴(r²−1)s(s+3))`, `N` even of degree six (`onsetDensitySS_eq`), Laurent
  in `u = 1/r` (`onsetDensitySS_substitution`); the continued Euler-integral trace is
  `Γ(½)·Γ((s−3)/2)/Γ((s−2)/2)·R(s)` with explicit rational `R` (`onsetTraceSS_eq`, `onsetTraceVV_eq`),
  no rational part, no logarithm.
- `RHTower/ThetaCuspHawkingBMLaurentHorizonValue`: horizon values of the Laurent particulars, the
  radiation amplitude of the causal cut, at both physical rates.
- Paper step recorded in the ledger (row 37): retarded response = Laurent particular; advanced response
  = particular minus `(y(1)/α)·h_N`; cut = `(y(1)/α)·h_N`; the cut lives in the quartic coefficient.
- Audits: single-module `lake build` green for all three, standard axioms.

## Pass 9 (2026-09-13): the elementary skew cut

- `RHTower/ThetaCuspHawkingBMEvenSectorSkewFamilies`, `…SkewSources`, `…SkewCurrent`: the two-rate
  onset current between the complete `++` Laurent response (half-rate `s`) and the complete `−−`
  response (half-rate `−3−s`), assembled bilinearly from 169 atom-level identities
  (`evenSector_skewOnset_SS`).
- `RHTower/ThetaCuspHawkingBMEvenSectorSkewTraceFamilies`, `…SkewTraceSources`, `…SkewTrace`: at the
  fundamental harmonic with all Laurent coefficients at their actual values, the density
  `skewDensitySS = N/(r⁶(r²−1)s(s+3))`, its Laurent form in `u = 1/r`, the horizon-logarithm
  coefficient `skewLogCoeff` (`skewLogCoeff_eq`), its oddness under the branch reflection
  (`skewLogCoeff_reflect`) and the difference-quotient factorization (`skewLogCoeff_sub`).
- Paper: `A = −3∫r²Ω^t(k₊₊,k₋₋) + ½[r²Ω^r]` is the antisymmetrized retarded pairing; purely imaginary on
  the line; real part `(Re ρ − 1/2)·cofactor` off it; the leading term has one sign for all actual zeros.
- Audits: single-module `lake build` green for all six, standard axioms.

## Pass 10 (2026-09-13): the elementary skew cut, fully explicit

- Radial two-rate chain `RHTower/ThetaCuspHawkingBMEvenSectorSkewRadial{Families,Sources,Current,TraceFamilies,TraceSources,Trace}`:
  the radial component of the current between the `++` and `−−` Laurent responses; density
  `N/(r⁷ s(s+3))`, regular at the horizon.
- `RHTower/ThetaCuspHawkingBMEvenSectorSkewLineSign`: on the critical line the horizon-log coefficient is
  purely imaginary with negative imaginary part for `t² ≥ 3`.
- `RHTower/ThetaCuspHawkingBMEvenSectorSkewFinitePart`: the Hadamard finite part of the bulk integral in
  the boundary variable — partial fractions, explicit primitive, FTC, exact split at the horizon cutoff,
  the finite part as a rational function plus `(b₁+d₁)·log 2`, and the limit theorem.
- Result: `A = Q₀(s) + skewLogCoeff(s)·log(4/ε)` with explicit rational `Q₀`, both odd under the branch
  reflection; `Im A < 0` at every zero for every small horizon cutoff.
- Audits: single-module `lake build` green for all eight new modules, standard axioms.
- Pass 10 addendum: `RHTower/ThetaCuspHawkingBMEvenSectorSkewTiltDetection` — elementary tilt detection:
  `2·Re(skewLogCoeff s)·|s(s+3)|² = (2 Re ρ − 1)·skewTiltCofactor` with the cofactor negative on the strip
  above height 35, so the real part vanishes exactly on the critical line there. `lake build` green,
  standard axioms.
- Pass 10 addendum 2: `RHTower/ThetaCuspHawkingBMEvenSectorSkewFullTilt` — the regularized elementary cut
  `skewCut s ε = skewFinitePart s + skewLogCoeff s·log(4/ε)` with its link to the bulk-limit module, and
  tilt detection for every cutoff `ε ≤ 4/e` above height 58. `lake build` green, standard axioms.

### Addendum (pass 11, 2026-09-13): complete elementary sign law and the cutoff as a clock reading

`ThetaCuspHawkingBMEvenSectorSkewClockSign` (standard axioms, no warnings). On the critical line the finite part of
the regularized cut is purely imaginary with positive imaginary part for `t ≥ 5`, the logarithm coefficient has
negative imaginary part, and their sum has the sign of the logarithm coefficient (`skewLineSumEven_pos`), so
`skewCut_line_im_neg : 5 ≤ t → 1 ≤ log(4/ε) → Im (skewCut (−3/2 + i t) ε) < 0` and `skewCut_line_re = 0`.
The horizon cutoff `z = ε` is the point of static radius `(1−ε)^{−1/2}`, whose corpus tortoise coordinate obeys
`log(4/ε) = −2·tortoise + 2·log(2/(1+√(1−ε)))` (`log_cutoff_eq_tortoise`), correction in `(0, 2 log 2)` and
vanishing at the horizon; `skewCut_eq_tortoise` writes the cut as finite part plus logarithm coefficient times
twice the ingoing depth. Both sign statements hold for every cutoff of ingoing depth at least one half
(`skewCut_line_im_neg_tortoise`, `skewCut_re_eq_zero_iff_tortoise`). Paper-level: the logarithm coefficient is the
horizon residue of the rational static density in `q = e^{2r_*}` (the `q³` Taylor coefficient of the regular ingoing
work density), the corpus translation mass is the order-zero horizon value; the on-line general-harmonic criterion
must include the doubled-rate resolvent resonance at the spectral edge `λ = 4t² − 2` of width `6t`.

### Addendum (pass 12, 2026-09-13): horizon plateau of the two-rate current in the ingoing clock

`ThetaCuspHawkingBMEvenSectorSkewHorizonPlateau` (standard axioms). The ingoing time component of the two-rate
current, `Ω^v = Ω^t + Ω^r/(r²−1)`, dressed by `e^{6r_*}z^{−3}r²`, is `skewIngoingNumerator s w/(1+w)⁷` with
`(1−w)·skewIngoingNumerator = w²(2w·skewLaurentSS + skewRadLaurent)`: the horizon poles cancel, the current is regular
at the future horizon. Its horizon value `skewHorizonPlateau` and the horizon radial flux `skewHorizonFlux =
skewRadLaurent s 1/64` (a polynomial) are the plateau values a translation moment at rate `−6` reads off the post-onset
current. Certified: both odd under `s ↦ −3−s`, purely imaginary on the line, `Im skewHorizonPlateau < 0` for all
`t ≥ 1`, `Im skewHorizonFlux > 0` for `t ≥ 5`, and off the line their real parts are `(2σ−1)` times sign-definite
cofactors (plateau negative for `t ≥ 44`, flux positive for `t ≥ 17`), so both vanish exactly on the critical line there.
Paper-level: the cutoff-free ingoing-slice integral exists (`R_in + c_in log 2`) but its sign laws rest on the
near-cancellation `111/160 − log 2 ≈ 6·10⁻⁴`; the plateau values are the robust targets.

### Addendum (pass 13, 2026-09-13): the plateau at every harmonic and its pointwise on-line sign

`ThetaCuspHawkingBMEvenSectorSkewPlateauHarmonic` (standard axioms). The general-harmonic plateau `skewPlateauMu s μ`
(65-term numerator over `128(2−μ)²(μ−(2s+1)(2s+2))(μ−(2s+4)(2s+5))`) reduces to the certified `skewHorizonPlateau` at
`μ = (s+1)(s+2)` (`skewPlateauMu_fundamental`). On the line with real harmonic `μ = −l` it is purely imaginary with
positive denominator and line form `−(5/64)t⁹l²(l−4t²)² + (weight ≤ 15)` (`skewPlateauLineForm_leading`); the sign
theorem `skewPlateauMu_line_im_neg : 50 ≤ t → 40t ≤ l → Im < 0` is proved by three exact nonnegative-coefficient
identities on `40t ≤ l ≤ 3t²`, `3t² ≤ l ≤ 5t²`, `l ≥ 5t²`. Paper-level identification of `skewPlateauMu` with the
general-harmonic current (exact bookkeeping from the certified `skewOnsetSS`/`skewRadialSS`) is recorded in the ledger.

### Addendum (pass 14, 2026-09-13): the corpus clock coefficients harmonic by harmonic

`ThetaCuspHawkingBMVectorClockHarmonic` (standard axioms). The corpus's `clockCoefficients q a b z 0 0` and `… 1 0` are
certified as quadratic forms `(a²b²/16)(α⟨G,G'⟩ + β⟨G,Q⟩ + γ⟨G',Q⟩ + δ⟨Q,Q⟩)` in the coexact angular responses and the
square covector, with explicit polynomial coefficients in the physical rate (`clockCoefficients_mass`,
`clockCoefficients_radial`). On an angular harmonic the responses contribute `λ₂/(2(μ−λ₂))`, giving the per-harmonic
coefficients `vectorClockMass`, `vectorClockRadial` (denominator `2(μ−λ₂)·2(μ−λ₂')`, reduced numerators of degree two
in `μ`, `_eq_form`). On the critical line both are purely imaginary; their line forms are quadratics in the harmonic with
positive discriminant defect `4AC − B²` for `τ ≥ 1` (leading terms cancel; the doubled-frequency edge is the minimiser),
so `Im vectorClockMass > 0` and `Im vectorClockRadial < 0` at every harmonic and every height `τ ≥ 1`
(`vectorClockMass_line_im`, `vectorClockRadial_line_im`). The spectral integration of the pointwise pairings and the
measure factor are paper-level; the two sectors carry opposite on-line signs in their own normalizations.

### Addendum (pass 15, 2026-09-13): the sector quartic form and the opposite signs of the pure excitations

`ThetaCuspHawkingBMEvenSectorSkewSectorForm` (standard axioms). The vector-vector and scalar×vector kernels of the
scalar-sector two-rate horizon plateau at a general harmonic are explicit (`skewPlateauMuVV`, `skewPlateauMuCross`);
on the line their leading parts are `−(1/4)t⁵l²(l−4t²)²(l−3t²)(l+t²)` and `−(1/8)t⁷l²(l−4t²)²(3l+t²)`, and together
with the scalar-scalar kernel the leading quartic form in the sector amplitudes factors:
`−(1/64)t⁵l²(l−4t²)²(5t²aS² − 4(3t²−l)aV²)(t²aS² + 4(l+t²)aV²)` (`skewSectorForm_factor`, `skewSectorForm_leading`).
Certified: `Im skewPlateauMuVV > 0` on `40t ≤ l ≤ 2t²`, `t ≥ 50`, where `Im skewPlateauMu < 0`
(`skewSector_opposite_signs`). Pure scalar and pure vector excitations therefore give opposite on-line signs of the
clock coefficient at every bulk harmonic; no amplitude-independent sign law exists, and the producer question is the
sector content of the physical excitation.

### Addendum (pass 16, 2026-09-13): the chiral excitation has one sign at every harmonic

`ThetaCuspHawkingBMEvenSectorSkewChiralSign` (standard axioms). For a single-helicity excitation (`aV = ± i·aS`, the
corpus's `d4GravitationalHelicityPlus/Minus`) the sector quartic form collapses to `aS₊²aS₋²·(P_SS − P_X + P_VV)`; the
chiral kernel's line form has leading part `(1/64)t⁵l²(l−4t²)²(51t⁴+56t²l−16l²)` (`skewPlateauMuChiralLine_leading`),
positive on the whole spectral support `l < (17/4)t²` with the constant mode positive, and `Im skewPlateauMuChiral > 0`
is certified for `0 ≤ l ≤ 2t²`, `t ≥ 50` (`skewPlateauMuChiral_line_im_pos`). The on-line sign of the physical clock
coefficient is therefore uniform in the harmonic; remaining: the KI translation of the corpus chirality, the spectral
tail beyond `(17/4)t²`, the edge band, the off-line tilt.

### Addendum (pass 17, 2026-09-13): the chiral kernel on the edge band

`ThetaCuspHawkingBMEvenSectorSkewChiralEdge` (standard axioms). On `2t² ≤ l ≤ (17/4)t²` the weight-fifteen part of the
chiral line form is written in the Bernstein basis of the band with all coefficients at least `22.66`, which pays the
lower-weight cost `17.34` at `t ≥ 50` while the leading part `(1/16)t⁵l²(l−4t²)²((17/4)t²−l)(3t²+4l)` is nonnegative;
hence `skewPlateauMuChiral_line_im_pos_support`: the chiral kernel has positive imaginary part at every harmonic
`0 ≤ l ≤ (17/4)t²` for `t ≥ 50`, i.e. on the whole spectral support of the square of the angular profile.

### Addendum (pass 18, 2026-09-13): traceless-Hessian sources are scalar-type

`ThetaCuspHawkingBMTracelessHessianScalarType` (standard axioms). On the upper half-plane the covariant divergence of
the traceless Hessian of a scalar `f`, computed with the hyperbolic Christoffel symbols, equals the gradient of
`½Δf − f` and has vanishing curl (`tfHessian_divergence_x/_y/_curl`), so a spin-two source of traceless-Hessian form —
the corpus's polarized Plebanski source — carries no vector-type component and excites only the scalar sector. This
fixes `aV = 0` under the "response to the spin-two source" reading of the physical excitation; the single-helicity
reading `aV = ± i·aS` is the alternative, and the clock kernels for both are certified.

### Addendum (pass 19, 2026-09-13): the constant mode of the scalar-scalar plateau

`ThetaCuspHawkingBMEvenSectorSkewConstantMode` (standard axioms). At the constant harmonic the scalar-scalar line form
is `8t¹⁵ + 36t¹³ + 46t¹¹ − …`, at least `4t¹⁵` for `t ≥ 3`, so the constant-mode kernel is at least `t¹¹/2176` for
`t ≥ 5` (`skewPlateauMu_constant_mode_im_ge`); on the bulk band `t² ≤ l ≤ 3t²` the kernel is at most `t⁹/1000` for
`t ≥ 50` (`skewPlateauMu_bulk_im_le`). The constant mode's wrong-sign kernel is thus `t²` larger than the bulk scale:
under the pure-scalar reading the on-line sign of the clock coefficient is decided by the regularized constant term
(the cusp flux), not by the bulk. The two-sided bulk bound is pending.

### Addendum (pass 20, 2026-09-13): the constant mode dominates and is a perfect square — chain-level reframing

`ThetaCuspHawkingBMEvenSectorSkewLowBand`, `…SkewConstantSquare` (standard axioms). On the low band `0 ≤ l ≤ t` the
scalar-scalar kernel is `≥ t¹¹/(544(2+l)²)`; at `l = 0` the three sector kernels have leading coefficients
`8, −192, 1152` with `8x² − 192xy + 1152y² = 8(x − 12y)²`, so the constant-mode kernel is a perfect square in
`(aS², aV²)`, nonnegative for every real amplitude ratio (chiral value `1352`). With the corpus's own spectral weight
(`nativeDiagonalPeriod_fourLambda`) and Stirling, the regularized constant mode (weight `c₀² ≍ e^{−2πt}(log t)⁴|ζ(1+2it)|⁴`)
outweighs the bulk (`≍ e^{−2πt}t^{−1}·M`, `M ≪ t^{3/2}log²t` by convexity) by `t^{3/2}(log t)^{−6}` once the kernels
(`t¹¹` vs `t⁹`) are included. Consequences: the on-line sign of the fundamental clock coefficient is automatic (positive
imaginary part) in every sector reading; off the line the dominant weight `c₀(ρ)² ∝ (Λ(2ρ)Λ(2ρ−1))²` carries the phase
tilt `(2σ−1)(π/2 + 2·Im(ζ'/ζ)(1+2it))`, so `Re/Im ≈ −(2σ−1)(π + 4·Im(ζ'/ζ)(1+2it))` and the coefficient is not a
sign-definite tilt detector; the target must be a nonvanishing law (normalization by `c₀(ρ)²`, or a universal cutoff by
the Baire pattern of `exists_universal_onset_duration`). The producer remains open.

### Addendum (pass 21, 2026-09-13): tilt detection by the constant-mode kernel

`ThetaCuspHawkingBMEvenSectorSkewConstantTilt` (standard axioms). With `v = s + 3/2` the constant-mode kernel is
`v·P(v²)/(512·Q(v²))`, odd in `v`; the difference-quotient numerator factors as `(v−y)·Ĥ((v+y)², vy)` by a pure
polynomial identity, and at the reflected pair the two arguments of `Ĥ` are the real numbers `−4t²` and
`−((σ−½)²+t²)`. Hence `2·Re(skewPlateauMu s 0)·|512Q(v²)|² = (2σ−1)·skewConstantTiltCofactor σ t` with an explicit
real polynomial cofactor of leading term `720896·t¹⁸`, positive on the strip for `t ≥ 92`:
`skewConstantKernel_re_eq_zero_iff`. Together with pass 20 this certifies the elementary side of the receiver: the
normalized physical clock coefficient (divided by the source's regularized constant term, the corpus's unit-source
convention) is purely imaginary with definite sign on the line and has real part `(2σ−1)·(positive)` off it, up to
the paper-level bulk estimate.

### Addendum (pass 22, 2026-09-13): oddness at every harmonic; producer classification

`ThetaCuspHawkingBMEvenSectorSkewPlateauOdd` (standard axioms): `skewPlateauMu (−3−s) μ = −skewPlateauMu s μ` and real
coefficients at every harmonic, hence on the line `K(s, μ̄) = −conj K(s, μ)`; the growing Weyl powers of the angular
square (eigenvalues `(2s+4)(2s+3)`, `0`, `2s(2s+1)`) contribute purely imaginary amounts, and the constant mode still
dominates. Producer classification: sector positivity, chirality, reflection positivity, cutoff-scheme independence and
reality of the metric perturbation were each tested against the certified kernels and found to be either automatic or
receivers equivalent to RH (the reality test shows the Hermitian diagonal terms enter the rate-`(−6)` clock moment only
at second order in the tilt, the corpus's cokernel-orbit structure). Survivor: the explicit certified detector; the
producer, if any, is an independent evaluation of the cusp regularization face carrying `c₀(ρ)²`.
