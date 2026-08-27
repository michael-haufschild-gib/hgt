# GTA quadratic trace-energy defect no-go (2026-08-27)

- Card: `docs/drafts/pipeline/5-failed/finite-schur-quartic-quadratic-trace-energy-defect.md`
- Lean module: `formal/GaloisForLFunctions/HTGeometry/FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect.lean`
- Exact identity for any finite Schur packet:
  `HS²(M) - Re tr(M²) = (HS²(M) - Σ|λᵢ|²) + 2Σ(Im λᵢ)²`.
- The first term is Henrici Frobenius departure-from-normality squared and is nonnegative.
- Dimension-free survivor:
  `Q₄(S) ≤ 1150 HS²(M) T₂(S) ≤ 1150 HS²(M) D₂(M)`.
- Producer necessity is false: upper nilpotent Jordan block has all-zero Schur diagonal and `Q₄=0`, but `D₂=1`.
- Consequence: raw source observable `HS²-Re tr(M²)` conflates nonnormality with transverse spectral orientation; a viable exact GTA producer must isolate/subtract nonnormal Schur energy.
- Direct Lean check and exact module build passed. Endpoint axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`.
- Novelty audit: Henrici component classical (DOI 10.1007/BF01386294); no exact literature/corpus hit for combined transverse split or quartic inequality, so novelty remains UNVERIFIED.
- Frontier map is user-designated read-only; never update it.
