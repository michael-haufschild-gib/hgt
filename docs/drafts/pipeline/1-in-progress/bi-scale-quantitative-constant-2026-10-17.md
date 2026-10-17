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
4. [x] Write dependency-closed proofs; formalize shared-origin support, polar enforcement, arbitrary finite moment enforcement, and finite-vector scalarization/convexity; wire all four leaves into umbrella.
5. [x] Direct leaf and axiom audits pass for all four task modules, including explicit smooth-order specializations. Preserve concurrent work.
6. [ ] Formalize full-cone/even-source extensions and connect adjacent integrated transport to the reflection-allocation certificate. Determine globally sharp constants; continue significant research toward the full goal.

`update_plan` and `multi_tool_use.parallel` are not exposed in this session. This card tracks the plan; independent tool reads use awaited parallel promises. Serena symbol lookup rejects the ignored Lean source paths, so file reads are the available fallback. `docs/architecture.md` and `docs/testing.md` do not exist.

## Exact issues under investigation

Current spectral bridge: for a nonzero real compact envelope `f` and a finite probability cosine
mixture `m`, realize `h_f m` by cosine/sine-modulated source components. Prove normalized vector
energy differs from `Σ p_j Ψ(ω_j)` by at most `E(f)`, uniformly in frequencies, where
`Ψ(ω)=∫₀∞(1−cos(ωx))w_arch(x)dx`. Then scalarize and enforce polar neutrality while preserving
the exact finite grid zeros. Broad-envelope energy convergence and spectral duality remain
separate obligations until proved; no small-envelope-energy hypothesis may be silently assumed.
The envelope-existence obligation now has a concrete formalization in progress:
`BroadSpectralCostRealization.lean` derives global linear correlation control from compact-source
Lipschitz regularity, proves the weight's first moment finite, dilates a concrete smooth bump,
and targets actual polar grid sources with energy below `spectralMixtureCost + ε`.

Completed attack: finite-vector to scalar-source reduction. For separated real sources, the plus
and minus combinations have the same local autocorrelation sum, while their energies average
to the sum of the component energies. Choosing the better sign gives exact energy domination,
stronger than an asymptotic approximation. The two-source theorem, finite-list induction,
scalar/vector finite-grid equivalence, polar composition, and actual scalar epigraph convexity
are Lean-certified. Next spectral reduction needs modulation identities, energy convergence,
and strong-duality/attainment arguments; convexity alone does not discharge those obligations.
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

Shared-origin support law, equality witness, rational penalty, and literal dyadic-grid specialization are Lean-certified in `SharedOriginMultiCosetLeverage.lean`. Adjacent concurrent research independently found this support formula; count it as a shared bridge, not as separate novel knowledge. Existing foundation/folded-collar work also does not count toward this task's 100.

Authoritative facts/failures: `docs/reports/BiScaleUncertainty/WORKING-LEDGER.md`. Complete paper proofs and explicit N-dependent quadrature certificates: `docs/reports/BiScaleUncertainty/quantitative-constant.md`.

## Validation

All four task modules passed direct `lake --old env lean -o ...`, exit 0 without diagnostics. Scratch axiom audits passed for five shared-origin endpoints, all 23 polar-module theorems, all five finite-moment theorems, and all 14 scalarization-module public theorems; only `propext`, `Classical.choice`, `Quot.sound`. Explicit smooth-order specializations passed. All four modules are wired into the umbrella. Index regeneration passed; latest lint reports four concurrent wiring errors outside this task's modules, named in the working ledger. All owned Lean processes exited.

No numerical experiments; no full or umbrella builds; no increased heartbeat limits; no commits. Goal remains active: globally sharp constants, full formalization, and the 100-contribution requirement are unfinished.
