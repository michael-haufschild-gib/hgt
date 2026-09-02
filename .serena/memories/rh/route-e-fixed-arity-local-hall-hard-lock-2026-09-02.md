# Route E fixed-arity local Hall hard lock

Authority: `docs/drafts/pipeline/3-formalized/route-e-fixed-arity-local-hall-mass-obstruction.md`; status summary in `docs/drafts/pipeline/1-in-progress/rh-research-status.md`.

- RH chain: squarefree Möbius source -> local Hall/factor replacement -> half-power control -> Möbius half-power -> RH.
- KILLED unconditionally: every fixed source-token arity, common multiplicative spectator, local positive Hall/fractional-defect implementation. Failure already at broad `N^(2/3)` displacement/defect scale, hence kills half-power-local versions.
- Exact obstruction: for arity `k`, depth `r=12(k+1)` products of distinct primes in `(Y,2Y]`, with `N=(2Y)^r` and `H=(2Y)^(8(k+1))=N^(2/3)`, form a near-linear isolated family. Isolated Gibbs mass eventually exceeds every `C H`.
- DO NOT REOPEN through another fixed arity, finitely many replacement templates, constants, or positive degree-normalized refinements.
- LIVE ONLY: arity growing with scale; displacement `>N^(2/3)`; non-spectator/history-dependent incidence; separate collective Ramaré incidence.
- Lean module: `GaloisForLFunctions.RHTower.MobiusBoundaryFixedArityLocalHallMassNoGo`.
- Kill theorem: `RHTower.routeEFixedArityTwoThirdLocalHallDefectRouteKilled`.
- Quantitative core: `RHTower.eventually_const_mul_twoThirdScale_lt_routeEFiniteIsolatedGibbsMass`.
- Exact target build passed; axiom audit only `propext`, `Classical.choice`, `Quot.sound`.
- Before new Route E conjecture: read this memory/card, then run `scripts/formal_tools.py research "<exact proposed mechanism>"`.