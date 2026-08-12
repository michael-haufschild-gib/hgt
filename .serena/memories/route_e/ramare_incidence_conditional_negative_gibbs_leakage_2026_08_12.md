# Route E Ramaré incidence and Gibbs frontier (2026-08-12)

New umbrella-wired modules:
- `formal/GaloisForLFunctions/RHTower/Sieve/RouteERamareIntegerIncidence.lean`
- `formal/GaloisForLFunctions/RHTower/Sieve/RouteERamareIncidenceConditionalNegative.lean`
- `formal/GaloisForLFunctions/RHTower/Sieve/RouteERamareGibbsMeanLeakage.lean`

Exact advances:
1. Each Ramaré prime block equals its ordinary active-integer incidence block. Ordered `p != q` pairs give coefficient `1-|P(n)∩P(m)|/(|P(n)||P(m)|)`. Full finite-volume `ramarePrimeOffDiagonal` is an integer pair sum retaining Möbius signs and Mellin kernel.
2. Generic incidence-complement Gram law:
   `Q(c)=normSq(sum c)-sum_p normSq(sum_(p∈F_n)c_n/|F_n|)`.
   Hence on centered histories `Q(c)` is exactly negative prime-load energy; equality iff every normalized prime load vanishes. Actual Ramaré/Möbius specializations closed.
3. For positive Gibbs weights with pairwise log-ratio oscillation `eta` and `|f|<=1`, normalized incidence covariance satisfies
   `Q(a) <= (|uniformMean f| + 2*tanh(eta/4))^2`.
   Equal-product histories of arbitrary order `|R|` instantiate `eta=|R|H^2/(X(X-H))`.

Verification:
- direct `lake env lean` checks pass;
- targeted `lake build` of each module passes; no full build;
- key theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden declaration scan and scoped `git diff --check` pass.

Exact open Route E core:
Source-faithful decomposition of actual sharp Ramaré cofactors into common-aperture incidence cells; signed enumeration/cancellation of explicit uniform scalar cell means at affine strict-half scale; transport of same decomposition through zero/one-large-prime, moving Gallagher, and physical recurrence seams. Centered incidence covariance and Gibbs curvature are closed jointly, not open burdens.

Docs updated:
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- Stage-2 Ramaré and critical diffuse-codiagonal cards
- new Stage-3 cards for integer incidence, conditional negativity, Gibbs mean leakage.

Do not kill unrelated Lean processes in shared workspace.