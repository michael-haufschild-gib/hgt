# Littlewood L2 CLOSED: region gate certifies c > 0 (2026-08-05)

Cards: `littlewood-zero-free-region.md` (status: L1 ✓, L2 ✓), companion doc
`littlewood-l2-weyl-chain.md` (full chain + (R) section).

**(R) gate result:** the end-to-end detector inequality — Ford's vertical-line zero detector
(growth enters as log(B)/(2η)) + 3-4-1, with the certified honest-shape Weyl-chain growth
`B(x,L) = Σ_blocks b_N·N^x` as the ONLY analytic input, crude constants everywhere — yields

- log t = 2303:  ζ ≠ 0 for σ ≥ 1 − 0.0149·loglog/log  (a=6, η = 4·LL²/L)
- log t = 23026: c = 0.0179  (a=6, η = 8·LL²/L)

increasing in height. Key structural facts for L6: the window is `η ≍ (loglog t)²/log t`
(NOT ≍ δ); pole offset η' = aδ with a ≈ 6; the detected-zero cot expansion contributes
`−1/((a+1)δ) + π²(a+1)δ/(8η²)`; right-line term `log(1/(aδ+η)) + 2`; total remainder
prefactor 5/(2η) (from 4·(it-line) + 1·(2it-line)).

The entire Littlewood chain (KL, D2, W, Dk, Z, R) is dependency-closed on paper and
certified numerically. Next: **L3 = `Sieve/KuzminLandau.lean`** (Lean mapping in the L2 doc:
MVT per consecutive pair, monotone β_n, summation by parts, cot-variation or two-half
monotonicity to avoid the integral).
