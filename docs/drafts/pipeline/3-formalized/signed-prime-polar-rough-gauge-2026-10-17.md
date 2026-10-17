# Rough-source packet upper control through the constructed collar source

- **ID:** signed-prime-polar-rough-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Count:** verified contribution 5/100; all components count together.

## Target

Discharge the C¹ source premise in the neighboring Chebyshev mean-square packet
bound by using the actual collar source g=collarSource f a b. Keep the error
between the original source f and g explicit.

With R=h(0), C=H(0), B=collarEnergy, δ=R+B-2C, L=cutoff N,
Ẽ(x)=exp(-x/2)(ψ(exp x)-exp x), target the source-only inequality

Q_N(f) ≤ 6(10+Ẽ(L)²)B + 6||g'−g/2||₁² ∫₀ᴸ Ẽ² + 2 M_N² δ.

Construct g'(u)=(f(u-exp a)-f(u-exp a-exp b))/exp b. The final theorem must
contain no derivative, C¹, integrability, nonzero-source, or arithmetic-error
hypothesis. All quantities must come from actual compact continuous sources.

## Evidence and dependencies

Search `/tmp/spp4-next-search.json`: partial=false, errors=[], semantic coverage
unmeasured, refresh deferred to background indexer. Candidate and source-argument
sections inspected. The current source of
`HyperbolicGaugeChebyshevEnergyRepresentation.lean` contains
`ChebyshevGauge.packetEnergy_le_chebyshev_mean_square` with exactly a C¹ premise;
its statement was checked in the actual file. A compiled artifact newer than the
source subsequently became available. Its exact endpoint was reused and audited;
its axioms are only propext, Classical.choice, Quot.sound. No other lane was edited.

The collar source and δ are already verified in this lane. Existing
`hasDerivAt_annularAverage` suggests deriving g's regularity by an exact interval
change of variables. Packet linearity and Q_N(r)≤M_N²||r||² then control r=f-g.
The elementary squared-sum bound combines g and r. No commutation theorem for
smoothing and signed packets is required for this target.

## Critique and gates

- This is a finite-cutoff upper bound with a genuine roughness remainder. It does
  not establish cutoff-uniform control or permit discarding M_N²δ.
- Search and read current source before formalizing; inspect candidate applicability.
- Prove g's C¹ regularity and derivative from f's continuity, with actual support.
- Prove packet linearity, the residual energy identity, and the combined bound.
- Establish all L¹/L² integrability directly from source bundles.
- Audit the exact unconditional endpoint, wire imports, and count one complete
  theorem package only after direct Lean and axiom checks pass.

## Current proof plan

- [x] Fresh corpus search `/tmp/spp5-search.json`: partial=false, errors=[], candidate
  lemmas and source arguments inspected; semantic coverage unmeasured.
- [x] Dependency-closed mathematical argument in `SignedPrimePolarRoughGauge.md`.
- [x] Derive collar derivative, C¹ regularity, compact gauge source, and L¹ admission.
- [x] Prove exact remainder energy in the regularity leaf.
- [x] Neighboring C¹ dependency compiled and its endpoint axioms were verified.
- [x] Verify signed packet decomposition and its weighted energy inequality.
- [x] Prove weighted and fixed-constant upper bounds for every original C_c source.
- [x] Transfer the packet bound into global coherent and Lévy–sinh Chebyshev transport,
  with independent smoothing and transport collars.
- [x] Audit leaves and axioms, wire imports, lint/index, and count the whole package once.

The field README remains read-only. No RH work, numerical experiments, or umbrella builds.

Both `AnnularSourceRegularity.lean` and `SignedPrimePolarRoughGauge.lean` pass direct
`lake --old env lean <leaf> -o <leaf.olean>` with empty diagnostics; logs are
`/tmp/spp5-regularity-build.log` and `/tmp/spp5-rough-build.log`. Imports are wired.
Scratch audit exits 0: nine new endpoints plus the dependency use only standard
axioms; main signatures contain no extra hypotheses. Evidence:
`/tmp/spp5-final-axioms.log`. Index refresh passes. Global lint flags only unrelated
unwired `ChebyshevGaugeNyquistCellQuadrature` at this snapshot (`/tmp/spp5-lint.log`).
