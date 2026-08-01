# Route E literal OPEN-SOURCE-001 pursuit (2026-08-01)

Status: OPEN. Never reuse earlier finite/local “terminal closure” framing as Route E completion.

Exact hard source:
- Critical schedule `z^2 x / log z -> 1`.
- Need `|A_z(x)-sum_{p>z} A_z(px)| <<_epsilon x^(-1/2-epsilon)`.
- Zero/one boundary coefficient through `T=z^2` is literal Möbius coefficient; source implies RH through existing consumer.

Exact flow infrastructure in `formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean`:
- unrestricted proportional bipartite conductance attains defect exactly equal to signed imbalance, so unspecified flow is source repackaging;
- literal `{1<->2, 1>z<->4}` factor-replacement graph and window pruning;
- weighted Hall-cut necessary condition and canonical defect consumers;
- umbrella import already in `formal/GaloisForLFunctions/RHTower.lean`.

New terminal obstruction:
- If every prime factor of `n` is at most `y<z`, every replacement neighbor `m` satisfies `n <= y^4 * Nat.dist n m`.
- Lean theorem: `le_pow_four_mul_dist_of_boundaryFactorReplacementAdjacent_of_primeFactors_le`.
- If `y^4 H<n`, no displacement-`H` neighbor exists. Lean theorem: `not_boundaryFactorReplacementWindowAdjacent_of_primeFactors_le_of_pow_mul_lt`.
- Fixed-power squarefree-smooth density gives `Omega(N)` isolated Gibbs capacity in every `H=N^theta`, `theta<1`; this falsifies the proposed `z^(1+o(1))=N^(1/2+o(1))` hard-support producer.
- Direct `lake env lean GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean` passes. Targeted module build was run only because scratch import needed current `.olean`; no full build.

Second terminal obstruction:
- De la Bretèche--Tenenbaum 2024, Cor. 1.3, specialized to `f=mu`, zeta exponent `-1`: for fixed noninteger `u>1`, `Y=X^(1/u)`,
  `M_fri(X,Y)=X/(log Y)^2 {phi_{-1}(u)+O_u(1/log Y)}`.
- `v phi' = phi(v-1)`, `phi=1` on `(0,1]`, hence positive. Fixed-power friable Möbius sector has near-linear positive bias, not strict-half size.
- Therefore `FRIABLE-SIFTED SPLIT SOURCE` is false: bias must cancel across macroscopic smooth/rough seam.

Renewal exponent barrier:
- For fixed `1<u<2`, `Y=X^(1/u)`, exact sharp recurrence is `M(X)=M_fri(X,Y)-sum_{Y<p<=X}M(X/p)`.
- Positive renewal norm on `X^alpha` is `sum p^(-alpha)`: PNT gives `log u+o(1)` at `alpha=1` but `~X^(1-alpha)/((1-alpha)log X)` for every `alpha<1`.
- Scalar Daboussi renewal contracts only in linear PNT norm; it cannot bootstrap any fixed power saving. Surviving source must see sign/correlation across lower Mertens scales or use another non-scalar macroscopic structure.

Current exact open core:
- critical aperture approaches integer delay seam `log N/log z=2-o(1)`;
- zero/one comparison is cross-seam cancellation between deterministic friable bias and one-large-prime correction;
- PNT/zero-free-region theory cancels algebraic profiles but leaves a beyond-all-orders remainder far above square-root;
- strict-half control of that remainder is still literal `OPEN-SOURCE-001`, not renamed closure.

Primary files:
- `docs/drafts/pipeline/1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- `formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean`

Lean discipline: foreground only, one Lean process for this agent, `lake env lean <file>` direct checks, targeted module build only when `.olean` missing/stale, never full build.