# Route L folder → stage 3: Lean programme ledger

Goal: formalize, unconditionally, every displayed theorem of every card in this folder; move each
card to `3-formalized/` (with a `-formalized.md` companion) when all its results have closed Lean
theorems (`lake env lean` clean, `#print axioms` = propext/Classical.choice/Quot.sound, wired into
`RHTower.lean`). Delete this file when the folder is empty.

## Shared layers

| Layer | Content | Module | Status |
|-|-|-|-|
| G0 cubic Gamma norm | `‖F‖_δ² = Γ(5+δ)⁻¹∫_0^∞ t^{4+δ}F²`, inner product, finiteness class, L² embedding (triangle, Cauchy–Schwarz, polarization), domination, monomial–exponential Gram `Γ(5+δ+j+k)/(Γ(5+δ)(a+b)^{5+δ+j+k})`, atom Gram `K_δ`, dilation | `MobiusCubicGammaNorm` | done |
| G1 atom jets | `∂_x^r f_x` (`atomJet`), chain Taylor bound, `‖∂^r f_x‖_δ ≤ C_r x^{2-r-(5+δ)/2}` uniform in `δ∈[0,1]`, Taylor remainder, block Taylor law `gammaNorm_atomPacket_le` | `MobiusCubicGammaAtomJets` | done |
| A0 arithmetic | uniform PNT in cells, prime counts in windows, Mertens sums (corpus: `primeCounting_sub_logIntegral_isBigO`, `mertensS_le`, `le_mertensS`, theta-mass every base, odd-squarefree harmonic) | per card | audit |

## Cards

| Card | Needs | Status |
|-|-|-|
| l-abel-prefix-mixed-gram-sign | `MobiusAbelPrefixGramIntegral`, `MobiusAbelPrefixFourierMultiplier` | done → 3-formalized/route l |
| l-all-prime-semiprime-local-matching | G0, G1 (first order), A0, cell matching, semiprime count (6), triprime supply (7) | todo |
| l-balanced-prime-semiprime-two-jet-extraction | `MobiusTwoJetBlockTaylor`, `…CofactorPacket`, `…PrimeSemiprimePacket`, `…LinearDensity` | done → 3-formalized/route l |
| l-discrete-mobius-packet-sobolev | `MobiusDiscretePacketGeneralOrder`, `…Horizon`, `…EdgeEstimates`, `…CriticalHorizon`, `…SourceAperture` | done → 3-formalized/route l |
| l-prime-insertion-dipole-jet | `MobiusPrimeInsertionDipoleJet`, `…LiteralPackets`, `…MacroscopicPacket`, `MobiusCubicSourceMertensEnergy` | done → 3-formalized/route l |
| l-three-window-cofactor-third-jet | G0, G1 (third / d-th order), simplex selector, rounding (corpus), cofactor layers | todo |

## Log
- 2026-09-27 — card 3 (two-jet extraction) closed and moved; reusable: `exists_window_family` (theta-mass window primes), `exists_block_two_jet`, `blockSet`/`packetSet` bookkeeping, `cofinal_packet_reduction`, `moebius_two_mul_mul_prime`.
- 2026-09-27 — card 4 (discrete packet identity, horizons, aperture, wedge) closed and moved; `MobiusDiscretePacketEdgeEstimates` has Abel/Mertens tools, kernel monotonicity, telescoping low-edge bound and `Σ (log k)^p E(k)²/k` summability for cards 3 and 6; `mertensSaving_antitone`, `tendsto_mertensSaving_mul_log` moved to `MobiusCubicSourceMertensEnergy`.
- 2026-09-27 — card 5 (prime insertion) closed and moved; Mertens energy bound `gammaNorm_mobiusCubicSource_le` available for card 4.
- 2026-09-27 — G0, G1 built; card 1 closed and moved.
- 2026-09-27 — ledger created; corpus audit of cited modules done.
