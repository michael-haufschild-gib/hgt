# Quantitative logarithmic-grid uncertainty constant

- Stage: 1-in-progress
- Type: CANDIDATE
- Date: 2026-10-17
- Scope: independent Bi-Scale Uncertainty theory; no RH objective.
- Brief: attachment `4aea9418-a6fa-4acd-95b8-ea3615aae6cf/pasted-text-1.txt`.
- Goal: 100 significant contributions toward sharp unconditional bounds for the normalized archimedean increment energy under finite logarithmic-grid zeros and hyperbolic polar neutrality. Do not count auxiliary lemmas as separate contributions.

## Plan and current evidence

1. [x] Read supplied brief and field README, including its later expanded architecture; inspect existing foundation and folded-collar modules.
2. [x] Audit common-origin accounting across dyadic cosets; derive exact joint sphere relaxation and paper integrated bound.
3. [x] Audit whether polar neutrality gives a uniform quantitative gain without a common support bound: it does not; polar/nonpolar infima coincide on the full real continuous positive-definite finite-energy cone.
4. [x] Write dependency-closed proofs; formalize shared-origin support, polar enforcement, arbitrary finite moment enforcement, finite-vector scalarization/convexity, and finite spectral source realization; wire all six leaves into umbrella.
5. [x] All six direct leaf and axiom audits pass; spectral `N=2` specialization passes. Index refreshed and lint run; one concurrent module's missing import remains outside this task's leaves.
6. [ ] Prove reverse Fourier-measure comparison and exact finite atomization. Formalize full-cone/even-source extensions and connect adjacent integrated transport to reflection allocation. Determine globally sharp constants; continue toward the full goal.

`update_plan` and `multi_tool_use.parallel` are not exposed in this session. This card tracks the plan; independent tool reads use awaited parallel promises. Serena symbol lookup rejects the ignored Lean source paths, so file reads are the available fallback. `docs/architecture.md` and `docs/testing.md` do not exist.

## Exact issues under investigation

Completed spectral bridge: for a nonzero real compact envelope `f` and finite probability cosine
mixture `m`, cosine/sine-modulated components realize `h_f m`. Their normalized vector energy
differs from `Σ p_j Ψ(ω_j)` by at most `E(f)`, uniformly in frequencies, where
`Ψ(ω)=∫₀∞(1−cos(ωx))w_arch(x)dx=gammaBracket(ω)−gammaBracket(0)`.
Scalarization and polar enforcement preserve exact finite-grid zeros and an upper energy bound.
`BroadSpectralCostRealization.lean` discharges the envelope premise: compact-source Lipschitz
control and the finite first weight moment show that a concrete smooth bump's dilations have
energy tending to zero. Every feasible finite spectral probability therefore yields actual
smooth compact polar grid sources with energy below `spectralMixtureCost + ε`, for every `ε>0`.
Both spectral leaves pass direct Lean checks. Reverse Fourier-measure comparison, exact finite
atomization, attainment, and strong duality remain separate open obligations.

Completed attack: finite-vector to scalar-source reduction. For separated real sources, the plus
and minus combinations have the same local autocorrelation sum, while their energies average
to the sum of the component energies. Choosing the better sign gives exact energy domination,
stronger than an asymptotic approximation. The two-source theorem, finite-list induction,
scalar/vector finite-grid equivalence, polar composition, and actual scalar epigraph convexity
are Lean-certified. Modulation and vanishing-envelope energy are now also certified; convexity
alone does not discharge reverse spectral reduction or strong-duality/attainment obligations.
No global scalar factorization of an arbitrary positive-definite kernel is assumed.

Completed concrete operation: `f_T(u)=f(u)−exp(−T/2)f(u−T)` has proved autocorrelation and polar identities, exact normalized local preservation, and `O(exp(−T))` energy error. The coefficient-uniform `O(exp(−T/2))` estimate extends this to arbitrary finite real exponential-moment constraints, using successive separated copies. No abstract transfer-map premise is assumed.

- Summing the one-chain origin-leverage bound over cosets spends the same origin energy repeatedly. A valid joint bound needs one shared origin coordinate.
- Verified joint support function: with block constraints `u0² + ||u_m||² ≤ R²`, the maximum of `W0 u0 + Σ_m <w_m,u_m>` is `R sqrt(W0² + (Σ_m ||w_m||)²)`.
- Verified polar escape: polar neutrality leaves the finite-grid infimum unchanged for real compact sources of every differentiability order at least two. Full-cone and source-evenness-preserving extensions remain paper-only.
- Correct deformation is `(R−h)w+μhc=Rw−h(w−μc)`. The current field overview no longer displays the old extra constant. Crossover sign remains essential when integrating.

## Contribution ledger

Two significant core contributions are Lean-certified: (1) quantitative polar enforcement with exact local preservation and finite-grid infimum invariance; (2) arbitrary finite real exponential-moment enforcement with the same local preservation and infimum invariance, including zero/negative rates. Supporting lemmas do not count separately. These nested advances are not an exhaustive external novelty verdict. Full-cone taper, source-evenness preservation, and the explicit common-separation polynomial estimate remain paper-only.

Third certified contribution: exact finite real vector scalarization with bounded-window data
preservation and no energy increase, scalar/polar/vector grid lower-bound equivalence, and
convexity of the actual scalar local energy epigraph. This is one package. Existing complex-even
whole-profile/fixed-window purification is prior work, not counted again.

Fourth certified contribution: actual smooth compact polar scalar realization of every feasible
finite spectral probability, with exact grid zeros and energy below its spectral cost plus any
positive tolerance. The low-energy envelope is constructed, not assumed. Count the two spectral
leaves as one package. Existing cosine/sine modulation algebra is prior work, not a new count.

Shared-origin support law, equality witness, rational penalty, and literal dyadic-grid specialization are Lean-certified in `SharedOriginMultiCosetLeverage.lean`. Adjacent concurrent research independently found this support formula; count it as a shared bridge, not as separate novel knowledge. Existing foundation/folded-collar work also does not count toward this task's 100.

Authoritative facts/failures: `docs/reports/BiScaleUncertainty/WORKING-LEDGER.md`. Complete paper proofs and explicit N-dependent quadrature certificates: `docs/reports/BiScaleUncertainty/quantitative-constant.md`.

## Validation

All six task modules passed direct `lake --old env lean -o ...`, exit 0 without diagnostics. Scratch axiom audits passed for five shared-origin endpoints, all 23 polar theorems, five finite-moment theorems, 14 scalarization theorems, and all 24 spectral theorems; only `propext`, `Classical.choice`, `Quot.sound`. Explicit smooth-order specializations and the `N=2`, `ω=π/(2log2)` spectral realization passed. All six modules are wired into the umbrella. Index regeneration and scoped whitespace checks passed. Latest lint reports one concurrent missing umbrella import, `PhysicalCollarDualCertificate`, plus 381 large-file warnings; no task-module error. All owned Lean processes exited.

No numerical experiments; no full or umbrella builds; no increased heartbeat limits; no commits. User cleared the active goal; research is stopped, not complete. Globally sharp constants, full formalization, and the 100-contribution target remain unfinished. The open items above are continuation notes, not authorization to resume.
