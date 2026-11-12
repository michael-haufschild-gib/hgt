# Critical half-line ground-state outerness

- **Stage:** 1-in-progress
- **Target:** B104 and the outer-predictor obstruction in B4.
- **Conjecture:** The reflected actual critical state is cyclic for causal translations in the half-line L² space.
- **Status:** Open; not counted.

## Connection

The actual weak equation and causal reflection exclude open-right-half-plane Laplace zeros. Boundary exclusion is undergoing Lean verification in `critical-half-line-boundary-laplace-exclusion.md`. Neither statement alone establishes cyclicity: a delay preserves zero-freeness.

The arithmetic energy is translation invariant, while translating toward the endpoint strictly lowers the exponential mass. Thus a critical state should have positive L² mass in every interval `(-d,0)`, `d>0`: otherwise its right translate remains admitted and has negative full energy, contradicting endpoint nonnegativity.

## Remaining inputs

1. Prove actual-domain translation admission, exact arithmetic-energy invariance, and the resulting absence of a support gap, including almost-everywhere representatives.
2. Connect exponential integrability, closed-half-plane zero-freeness, and absence of a support gap to causal cyclicity. Corpus inner/outer factorization is available, but no applicable theorem eliminating a singular inner factor has yet been identified.

No implication to nonvanishing of the arithmetic polar pairing is established. Zero-freeness and endpoint support alone must not be substituted for a proof of cyclicity.
