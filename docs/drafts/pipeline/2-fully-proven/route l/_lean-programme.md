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
| l-balanced-prime-semiprime-two-jet-extraction | G0, G1 (second order), theta mass, block selection (corpus), cofactor sum | todo |
| l-discrete-mobius-packet-sobolev | general-`J` packet identity, horizon (5)–(6), critical horizon (6a), aperture (7), wedge (8) | todo (cubic identity in `MobiusReciprocalDiscretePacketBridge`) |
| l-prime-insertion-dipole-jet | G0, jet limits, rationals, dyadic compensation, PNT selections, Mertens energy, (8)–(9) | todo |
| l-three-window-cofactor-third-jet | G0, G1 (third / d-th order), simplex selector, rounding (corpus), cofactor layers | todo |

## Log
- 2026-09-27 — G0, G1 built; card 1 closed and moved.
- 2026-09-27 — ledger created; corpus audit of cited modules done.
