# Determinant-line holonomy on the restricted Grassmannian — Lean programme

- **Stage:** 1 — in progress (Lean infrastructure programme)
- **Consumer:** ULF row 85 —
  `2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/determinant-line-lifted-action-deck-law.md`
- **Goal:** unconditional Lean proofs of Theorem DLLA-A (graph-cap holonomy `exp(2πi E(A))`, unique
  lift in `[0,1)`), Theorem DLLA-B (`q(F₀,F₁) = ⟨c₁(L_det),[S]⟩ ∈ ℤ`, equal holonomy) and (DLLA.5)
  (positive holomorphic bubbles: `q = Σ m_j ≥ 0`, `E(F₀) = E(F₁) + Σ m_j`).

## Global model (no charts, no Fredholm determinant)

- Polarization `P₊` (any orthogonal projection on a complex Hilbert space `H`).
  `Gr_res = {P orthogonal projection : P − P₊ ∈ HS}`; ambient affine space `P₊ + SLSpace H`
  (corpus `SLSpace`, complete real Hilbert space of self-adjoint HS operators).  Smooth maps into
  `Gr_res` = smooth maps into `SLSpace H` with projection values.  All index components are covered
  by re-centring the polarization (`Gr_res(P₊) = Gr_res(P)` for `P ∈ Gr_res(P₊)`).
- Kähler form `ω_det(X, Y) = (1/2πi) Tr(P[X, Y])` (trace of HS products, corpus `opTrace`);
  real, closed (`P_i` off-diagonal ⇒ `Tr(P₁P₂P₃) = Tr(P₁P₃P₂)`).
- Frames: `w : H → H`, `w = w P_{H'}`, `w|H' : H' ≅ W`, admissible iff `P_{H'} w − P_{H'}` has finite
  rank.  Gauge group `G_fin = {g invertible, g − 1 finite rank}`, `det` = finite-dimensional
  determinant on any finite-dimensional `V ⊇ ran(g − 1)` (multiplicative, Jacobi formula).
- Local admissible lifts near `W₀` with frame `u₀`: `w(W) = P_W u₀ (1 + E(W))⁻¹`,
  `E(W) = P_{H'}(P_W − P_{W₀})u₀`; then `P_{H'}w − 1 = R₀(1+E)⁻¹`, range in the fixed `ran R₀`.
  Same lemma ⇒ the admissible sector `S(H')` is clopen.
- Connection of `L_det = DET*` (dual Quillen metric `1/det(w*w)`): `∇(c[w]*) = (ċ − α c)[w]*`,
  `α(w)[ẇ] = Tr((w*w)⁻¹ w* ẇ)`; gauge law `α(wg) = α(w) + Tr(g⁻¹ġ)`; unitary; Chern
  (type `(1,0)` on holomorphic frames).  Curvature identity `dα = Tr(P dP∧dP) = 2πi ω_det`.
- Holonomy of a loop with lift `w`, `w(1) = w(0) h`: `Hol = exp(∫α(w)) / det h` (lift-independent).
- Cubical smooth chains (globally smooth maps `ℝⁿ → SLSpace H`, projection-valued on `[0,1]ⁿ`),
  boundary modulo degenerate 1-cubes, grid subdivision.  Integrality of `∫_c ω` on cycles by
  subdivision + lifts + Stokes on squares + corner telescoping of `det`.  Holonomy–curvature:
  `Hol(γ) = exp(2πi ∫_c ω)` for every filling chain `∂c ≡ γ`.
- Holomorphic maps: `(1 − P) ∂_{z̄}P P = 0`; then `ω(∂ₓP, ∂ᵧP) = (1/π)‖(1−P)∂P P‖²_HS ≥ 0`.
  Bubbles = holomorphic spheres (two-chart cycle `Q_N − Q_S`); degeneration = relative homology
  `c₀ ≡ c₁ + Σ B_j + ∂R`; `∫_{∂R} ω = 0` from `dω = 0`.

## Sector closedness (decided 2026-10-06)

Finite-rank gauge suffices: for `‖P_W − P_{W'}‖ < 1` and an admissible frame `u'` of `W'`,
`M = Q₀ P_W u' = 1 + (finite rank) + (HS)`; approximating the HS part by finite rank in operator
norm gives a finite-rank `F` with `M + F` invertible, and `P_W u' (M + F)⁻¹` is admissible.  Hence
the admissible sector is clopen with uniform radius 1, without Fredholm index theory.

## Integrality plan (2026-10-06)

Per square, not per chain: edge holonomy `edgeHol(e)` from uniformly subdivided lift data
(lift-independent by the edge lemma); per square `∏ⱼ edgeHol(eⱼ)^{εⱼ} = exp(2πi∫∫ω)` by grid
subdivision + Stokes + interior cancellation; chain integrality is then regrouping by edge
(`∂c(e) = 0` for non-constant edges, `edgeHol = 1` on constant ones); fillings give `Hol(γ)`.
Squares are globally `Gr_res`-valued smooth maps `ℝ² → SLSpace`; reparametrize by
`σ(x) = (1 − cos πx)/2` in each coordinate to globalize a filling.

## Modules

| # | Module | Content | Status |
|-|-|-|-|
| 0 | `HilbertSchmidtTraceIdeal`, `HilbertSchmidtCalculus` | trace ideal (span of HS products: linear, cyclic, basis-free trace); HS multiplication/adjoint/trace pairing as bounded bilinear maps | DONE |
| 1 | `RestrictedGrassmannianKahlerForm` | `Gr_res` as projections, off-diagonal tangents, `ω_det` real/antisymmetric, triple traces vanish | DONE (closedness for 3-families pending) |
| 2 | `FiniteRankDeterminant` | `det` on `1 + finite rank`, V-independence, multiplicativity, Jacobi along paths, integrated form | DONE |
| 3 | `AdmissibleFrameLifts` | frames, transfer, finite-rank approximation, index zero, propagation, clopen sector, smooth local lifts | DONE |
| 3b | `DeterminantLineGauge` | gauges `u g = u'`, cocycle, finite-rank defect, gauge law `α(ug) = α(u) + Tr(g⁻¹ġ)`, edge lemma `det g(b) = det g(a)·exp∫(α₂−α₁)` | DONE |
| 3c | `DeterminantLineSquareStokes` | smooth representation of α, C¹ forms, divergence = curvature, Green ⇒ `∫∫Tr(P[Pₛ,Pₜ]) = ∮α` | DONE |
| 4 | `DeterminantLineConnection` | frames `Q + Y`, `α`, derivative along curves, curvature identity `∂ₛα(∂ₜ) − ∂ₜα(∂ₛ) = Tr(P[Pₛ,Pₜ])` | DONE (gauge law, unitarity, Chern type pending) |
| 5 | `DeterminantLineEdgeHolonomy` | detCoord cocycle, path lifts, edge factors (lift-independent, additive), uniform levels, `edgeHol`, fine levels exist, constant paths trivial | DONE |
| 5b | `DeterminantLineSquareHolonomy` | rectangle holonomy (Stokes + corners), grid lifts (2D Lebesgue), `square_holonomy` | DONE |
| 6 | `DeterminantLineChainIntegrality` | squares, chains, boundary, sectors, regrouping, **`∫_c ω_det ∈ ℤ` on cycles** | DONE |
| 6b | `DeterminantLineFillingHolonomy` | fillings `∂c ≡ γ`: `edgeHol(γ) = exp(2πi∫_c ω)`, difference chains, deck integer | |
| 7 | `GraphCapHolonomy` | DLLA-A | |
| 8 | `DeterminantDeckLaw` | DLLA-B, holomorphic bubbles, (DLLA.5) | |
