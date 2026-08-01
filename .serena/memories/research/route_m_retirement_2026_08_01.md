# Route M retirement — 2026-08-01

Route M Gamma--Jacobi singular reader is formally retired.

Hard closure:
- On any finite injectively labelled prime packet, completed Euler clock `diag(log p)` has simple spectrum.
- Exact SR-47 aperture loss is rank one `v_K v_Kᵀ`, with every `v_K(p)=tanh(log p)^(2K)` nonzero.
- Lagrange projectors plus rank-one sandwiches generate every matrix unit, hence full finite matrix algebra independent of Krein signature.
- Existing finite cyclic-reader rigidity and positive jet-opening flux exclude one fixed positively normalized inclusion-compatible cyclic value.
- Actual Toeplitz counterreader is noncyclic already on two jet coordinates.
- First two-sided coefficient is `c₁(m)=-m₄/m₃`; source addition gives third-moment-weighted barycentric aggregation, not edge-symbol multiplication. Literal von Mangoldt edges 2→3 and 3→4 witness inequality.
- Positive survivor: retain edge/fibre marks and use nonmultiplicative barycentric aggregation before a noncyclic, fibre-pointed reader; redirect to co-Poisson fibre orientation.

Lean modules:
- `formal/GaloisForLFunctions/HTGeometry/SimpleClockRankOneAlgebraSaturation.lean`
- `formal/GaloisForLFunctions/RHTower/GammaJacobiEulerTailCyclicReaderNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/VonMangoldtCounterreaderBarycentricAggregation.lean`
- `formal/GaloisForLFunctions/RHTower/GammaJacobiSingularReaderRouteClosure.lean`

Umbrellas wired. Direct `lake env lean` checks pass. Targeted `lake build GaloisForLFunctions.RHTower.GammaJacobiSingularReaderRouteClosure` passes. `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`. Generated formal indexes refreshed. Repository-wide lint reports no Route M error but is nonzero due unrelated concurrently added unwired BVCoPoisson/BlockComplementaryMinor/RisingFactorialPolynomial modules.

Docs:
- Route M marked `[RETIRED]` in `rh-current-frontier-map.md` and literature exchange.
- Failed card: `docs/drafts/pipeline/5-failed/gamma-jacobi-euler-tail-cyclic-reader-no-go.md`
- Formalized survivor card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma-jacobi-counterreader-barycentric-aggregation.md`
- Source ledger adds SR-49 and retires SR-41.
