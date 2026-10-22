# Failed route: Suzuki positive growing-rank Cartan fission Ward producer

- **Route:** Use one positive determinant-one rank-two Stokes block for every retained transition-core prime pair, then feed completed growing-rank Cartan mass as nonnegative source energy into rectangular Ward connector.
- **Status:** RETIRED — unconditional Lean no-go for actual source and every sublinear correction class.
- **Exact killing theorem:** `RHTower.no_growingRankPositiveCartanFission_rectangularWardProducer`.

## Why it fails

Exact positive transition core satisfies `E_(8n) ≥ n/288` eventually. Fixed-width Xi rectangular
curvature is only `O(sqrt n)`. Any correction `c` making

`K_L(8n) - (E_(8n) - c_(8n))`

eventually lower-semibounded must therefore satisfy `c_(8n) ≥ n/576` eventually. Literal completed
growing-rank Cartan fission instead has `F_N = E_N + 2R_N`, `R_N ≥ 0`; its effective correction
`E_N-F_N` is nonpositive. Its Ward defect tends to negative infinity on `8n` for every width.

Growing rank solves finite-channel mass escape but not sign or scale mismatch.

## Strongest positive survivor

`RHTower.eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow` proves any viable
assembly needs coefficient-faithful signed correction carrying at least `n/576` mass along `8n`.
This excludes all bounded and asymptotically sublinear renormalizations, not only current Cartan
model.

Remaining shared HB/FZZ-P/RBH/PW-B source problem is narrower: construct signed
atomic–continuous compensation at full transition-core linear scale while leaving rectangular
residual uniformly lower-semibounded. Positive rank growth alone is terminal.

## Verification

Module `GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreLinearCompensationNoGo` passes direct Lean
checking, targeted build (`11979/11979`), and axiom audit. It is imported by RHTower umbrella.
Global formal lint is blocked by unrelated pre-existing unreachable module
`GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicInertia`; no forbidden declarations occur in
new module. Frontier map was not modified.
