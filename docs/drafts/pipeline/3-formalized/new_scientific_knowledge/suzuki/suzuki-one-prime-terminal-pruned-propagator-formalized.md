# Literal one-prime terminal pruning is a two-site involution, formalized

- **ID:** `suzuki-one-prime-terminal-pruned-propagator`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-one-prime-terminal-pruned-propagator.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOnePrimeTerminalPrunedPropagator.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOnePrimeTerminalChannel.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOnePrimeFractionalCarrier.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOnePrimeFractionalCarrierOperator.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLiteralPairedSourceAssembly.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ScalarSquareExponential.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`, `(8)`: the aperture threshold `2a < log 3 < 2 log 2` | `log_three_lt_two_mul_log_two` |
| `(6)`: the two rooted center families | `onePrimeDisplacement`, `onePrimeRightCenter`, `onePrimeLeftCenter` |
| `(7)`: closed-aperture membership `⟺ 0 ≤ d_n ≤ 2a` | `onePrimeRightCenter_mem_Icc_iff`, `onePrimeLeftCenter_mem_Icc_iff`, `onePrimeDisplacement_nonneg_iff` |
| `(9)`: confinement to `{0,1}` | `onePrime_terminal_index`, `onePrimeRightCenter_terminal_index`, `onePrimeLeftCenter_terminal_index` |
| strict interior forces `n = 1` | `onePrime_strictInterior_index_eq_one` |
| `(10)`: the aperture-independent gap `δ > 0` | `onePrimeTerminalGap`, `onePrimeTerminalGap_pos` |
| `(11)`: every nonterminal center is `δ`-separated from the aperture | `onePrimeRightCenter_outside_terminalGap`, `onePrimeLeftCenter_outside_terminalGap` |
| `(12)`, `(13)`: the canonical cutoff vanishes identically off `{0,1}` | `onePrimeScaleBufferedCutoff_eq_zero_of_outside_terminalGap`, `onePrimeRightScaleBufferedCutoff_eq_zero_off_terminal`, `onePrimeLeftScaleBufferedCutoff_eq_zero_off_terminal` |
| §3, `2a < log 2`: only the root site survives | `onePrime_terminal_index_eq_zero`, `onePrimeRightCenter_index_eq_zero`, `onePrimeLeftCenter_index_eq_zero` |
| §3, `2a < log 2`: the one-site compressed block is zero | `onePrimeTerminalCompression_eq_zero_of_rootSupported` |
| §3, `2a = log 2`: sites `0,1` are opposite endpoints with opposite inward orientations | `onePrimeRightCenter_one_eq_neg_of_resonant`, `onePrimeResonant_not_both_active` |
| `(14)`: `log 2 < 2a < log 3` makes site `1` strictly interior | `onePrimeRightCenter_one_mem_Ioo` |
| `(14)`: the outward orientation drops the root, the inward one retains it | `onePrimeRightRoot_cutoff_eq_zero_of_outward`, `onePrimeRightRoot_cutoff_ne_zero_of_inward`, `onePrimeRightSite_one_cutoff_ne_zero_of_interior` |
| `(15)`: the rank-one carrier weight `(1+|n|)^{-2/3}` | `fractionalPolynomialOrbitWeight` |
| `(16)`: the reciprocal terminal ratios | `onePrimeForwardRatio_zero`, `onePrimeBackwardRatio_one`, `onePrimeTerminalRatio` |
| `(2)`, `(17)`: `B_r` is the literal compression of the weighted shifts | `onePrimeTerminalAdjacency`, `onePrimeTerminalRestrict`, `onePrimeTerminalAdjacency_is_literal_compression` |
| `(3)`: `B_r² = I` | `onePrimeTerminalAdjacency_mul_self` |
| `(4)`, `(18)`: `exp(-itB_r) = cos t·I − i sin t·B_r` | `exp_onePrimeTerminalAdjacency`, `abs_sinc_mul_abs` |
| `(5)`: `sup_t ‖exp(-itB_r)‖ ≤ 1 + ‖B_r‖`, any real coupling | `norm_exp_onePrimeTerminalAdjacency_le`, `norm_exp_real_smul_onePrimeTerminalAdjacency_le` |
| `(19)`: the terminal transport degree is zero | `onePrimeTerminalGroup_degree_zero` |
| `(20)`: `p = 1/2 + 3/4 = 5/4` and `x^{-p}` is square integrable | `onePrimeSlowExponent`, `integrableOn_sq_onePrimeSlowTail`, `integrableOn_sq_rpow_neg_of_half_lt` |
| `(20)`: the near-end remainder `x^{1-N}` is square integrable from `N = 2` on | `integrableOn_sq_onePrimeNearEndRemainder` |

## What the card actually closes

The earlier one-prime Hardy argument needed a continuous group bound on the infinite weighted
Laurent adjacency of `ℓ²(ℤ)`, which the discrete weighted-shift estimate does not supply.  The card
observes that the bridge is unnecessary for the literal source, and the Lean development proves
exactly that in three steps.

**Support.**  The one-prime displacements are `d_n = n log 2`.  A rooted center lies in the closed
aperture exactly when `0 ≤ d_n ≤ 2a`; with `2a < log 3 < 2 log 2` this forces `n ∈ {0,1}`.  The
confinement is not a limiting argument: `δ = min(log 2, 2 log 2 − log 3)` is a positive constant
independent of the aperture, every center with `n ∉ {0,1}` lies at distance at least `δ` outside
`[−a,a]`, and the canonical scale-buffered cutoff — which is nonzero exactly on the open aperture —
therefore vanishes identically on the whole terminal ray `e^{-L} < δ`, uniformly in the infinitely
many discarded valuations.

**Channels.**  Which of the two surviving sites a fixed puncture orientation sees is decided by the
aperture.  Below `log 2` only the root remains and the compressed block annihilates every
root-supported state.  At the resonance `2a = log 2` the two sites are the two opposite endpoints;
the right endpoint admits only inward orientation `o < 0` and the left endpoint only `o > 0`, so no
orientation activates both and every fixed-orientation block is again one-site.  In the open window
`log 2 < 2a < log 3` site `1` is strictly interior and is activated by every orientation with
`|o| ≤ 1` once the physical scale is finer than its two wall distances, while the root endpoint is
activated by the inward orientation and dropped by the outward one.  Hence one orientation per root
carries the two-site block and the other carries zero.

**Propagator.**  Compressing the literal `κ = 2/3` weighted shifts to `{0,1}` gives the reciprocal
off-diagonal matrix with `r = 2^{2/3}`, because the weight ratios across the single step are exactly
`r` and `r^{-1}`.  That matrix is an involution — `B_r² = I` — so its continuous group is the exact
cosine–sine pair, and `|cos| ≤ 1`, `|sin| ≤ 1` bound it by `1 + ‖B_r‖` uniformly in the frequency
and in any real prime coupling.  The terminal transport degree is therefore `0`, not `2/3`: the
`2/3` exponent is a finite condition number on the terminal block, not continuous frequency growth.

At Gamma height `σ = 3/4` the slow exponent is `p = 1/2 + σ = 5/4 > 1/2`, so the homogeneous tail
`x^{-5/4}` is square integrable past the frequency origin, and the near-end remainders `x^{1-N}` are
square integrable from `N = 2` on.  The existing three-step Hardy argument survives with room to
spare.

## Hypotheses

Object data only: an aperture `a`, an integer valuation `n`, a puncture orientation `o` with
`|o| ≤ 1`, and a physical scale `L`.  The aperture conditions `2a < log 3`, `2a < log 2`,
`2a = log 2`, `log 2 < 2a` are the card's own case hypotheses, and `e^{-L} < δ` is its own terminal
threshold.  Nothing else is assumed: `B_r` is *not* assumed self-adjoint — it is generally nonnormal
— and the group bound comes from the involution, not from normality.  No `sorry`, `axiom`, `opaque`,
or `unsafe`; every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

What stays open is what the card itself declares open: higher-rank apertures,
recurrence-infinite transfer, completed/raw Evans identification, the producer classes P and I, and
Route O as a whole.  The one-prime terminal propagator gap is closed.
