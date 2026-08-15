# Formalization certificate — `ccm-rectangular-critical-mellin-tent-floor-law`

- **Card:** `ccm-rectangular-critical-mellin-tent-floor-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRectangularTentFloor.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 10 declarations
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(2)` moving tent, support, endpoints, peak | `movingTent*` |
| `(9)` two-edge autocorrelation | `interval_overlap_len`, `autocorrelation_split` |
| `(6)`–`(7)` adjacent equal blocks | `adjacent_block_readout` |
| `(18)` Haar shell localization | `overlapLen`, `haar_overlap_eq_zero` |
| `(12)`, `(14)` uniform Gamma bound | `quadratic_two_translate_bound` |

## Deliberately outside the Lean statement

- the distributional Weil form and the Stieltjes autocorrelation law `(10)`;
- the digamma form domain for indicators;
- the rectangular completeness theorem `(15)`;
- the Möbius mass-escape analysis `(19)`–`(20)`.

The card's remaining open gates (an unconditional positive source floor for `(7)`; formalizing the
source-side Stieltjes/autocorrelation layer; RH) are route gates, not statements of this card.
