# Suzuki PNT-envelope Cesàro producer no-go

- **ID:** SUZ-PNT-CESARO-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · common HB/FZZ-P/RBH/PW-B Suzuki Ward source
- **Statement:** Square-root magnitude control and PNT sublinearity cannot force boundedness of the exact Suzuki anchored-Cesàro source, even after adding nonnegativity and monotonicity.

## Goal

Kill an early common-source proof strategy before further work on four downstream routes. Audited chain:

`PNT O(sqrt N) envelope + o(N)`
`→ bounded weighted-Chebyshev anchored high-pass`
`→ bounded completed Suzuki Abel source`
`→ bounded aligned Gamma energy`
`↔ RH`
`→ shared Ward transmutation for HB/FZZ-P/RBH/PW-B`.

The first implication is false as an abstract analytic step. This does not kill the full Suzuki source route; it proves that its remaining premise must contain signed arithmetic cancellation not present in current envelope and sublinearity estimates.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact RH chain, hostile witness
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone exposition

## Paper proof `[PROVED HERE]`

Let the corpus anchored current be

`H_a(N) = a(N+1) - (3a(2) + sum_{j=3}^N a(j))/(N+1)`.

Take `a(n)=sqrt n`. It is nonnegative and monotone, satisfies `|a(n)| ≤ sqrt n` with equality, and `a(n)/n → 0`.

The corpus unit-Riesz prefix theorem gives

`3 sum_{r=1}^N sqrt r ≤ 2(N+1)sqrt(N+1)`.

The anchored tail `sum_{j=3}^N sqrt j` is contained in that prefix. Since `N+1 ≥ 3` and `sqrt 2 ≤ 2`, the anchored potential satisfies

`(3sqrt 2 + sum_{j=3}^N sqrt j)/(N+1) ≤ (2/3)sqrt(N+1) + 2`.

Therefore

`H_a(N) ≥ (1/3)sqrt(N+1) - 2 → +∞`.

Hence `H_a` has no uniform absolute bound. This contradicts the proposed universal implication from nonnegativity, monotonicity, square-root envelope, and sublinearity to bounded anchored current.

## No-go closure

- **Exact killing theorem/mechanism:** `suzukiPNTEnvelopeCesaroProducerRouteKilled`; an explicit envelope-saturating sequence has divergent literal Suzuki current.
- **Strongest positive survivor:** `tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop`, backed by the explicit lower law `suzukiSqrtEnvelopeWitness_highPass_lower`.
- **New insight:** endpoint magnitude and Cesàro history live at the same square-root scale but retain a nonzero first-order gap. Successful SWA-1 work must prove signed checkpoint cancellation, a spectral oscillation law, or another arithmetic invariant that controls this gap directly. Stronger one-sided regularity is not a replacement.
- **Status:** paper proof dependency-closed and formalized without added axioms.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.SuzukiPNTEnvelopeCesaroNoGo`
- Capstone: `suzukiPNTEnvelopeCesaroProducerRouteKilled`
- Divergence theorem: `tendsto_suzukiSqrtEnvelopeWitness_highPass_atTop`
- Explicit survivor bound: `suzukiSqrtEnvelopeWitness_highPass_lower`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/SuzukiPNTEnvelopeCesaroNoGo.lean` passed.
- Targeted audit: `lake build GaloisForLFunctions.RHTower.SuzukiPNTEnvelopeCesaroNoGo` passed (`14114/14114`).
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Formal lint: passed; no forbidden declaration.

## Conjecturing loop

- **SWA-1:** uniform boundedness of the completed signed Abel source. Still exact RH-bearing premise.
- **Hostile branch A — envelope/sublinearity closure:** false; killed here, even with positive monotone witness.
- **Hostile branch B — square/cumulative-energy closure:** rejected by corpus audit as equivalent/circular at aligned Gamma readout.
- **Surviving branch C — arithmetic oscillation:** only non-killed branch; must control signed weighted-Chebyshev checkpoint cancellation before Ward assembly.

## Novelty audit

Internal corpus had the exact mass-error high-pass decomposition, sharp unit-Riesz prefix bounds, PNT envelope/sublinearity, and the aligned Gamma/RH equivalence, but no theorem testing whether the first two controls can close the high-pass. External audit through 2026-08-31 found Suzuki screw-function RH criteria and bounded oscillatory zero sums, but no anchored weighted-Chebyshev PNT-envelope implication or this counterexample at the corpus source: [Suzuki 2022/2023](https://arxiv.org/abs/2206.03682), [Suzuki screw line](https://arxiv.org/abs/2209.04658), [Matsumoto--Suzuki](https://arxiv.org/abs/2409.00888), and [Cloitre's Tauberian RH characterization](https://arxiv.org/abs/2407.18859). Novelty claim is limited to this exact source-coordinate no-go and its four-route consequence.

`[LEAN-PROVED] [COMMON FOUR-ROUTE PRODUCER-STRATEGY KILL] [SIGNED-CANCELLATION SURVIVOR]`

## Log

- 2026-08-31 — conjectured from exact corpus source, proved on paper, formalized, audited, and route class retired.
